## RFC-0005 (soundness channels) slice S1 -- the lattice, the carrier and the
## `degrade()` funnel. NO verdict change: `classOf` maps every
## `SymexErrorKind` to `dcNoAnswer` (the conservative ⊤ default, RFC §5
## sequencing decision 1), and all-⊤ reproduces today's "any degrade blocks
## both verdicts" behaviour bit-for-bit. Later slices (S4-S6) reclassify one
## funnel at a time and flip only that funnel's pins.
##
## What this file pins:
##   (a) the §2.1/§2.2 algebra -- `classOf` totality + default, the
##       `pathTaint`/`runTaint` table per `DegradeClass`, `channels`;
##   (b) Path-carrier behaviour through runtime.nim test hooks (`Path` is
##       private -- the H1 hook pattern, `runtime.nim` `h1PathHasHeapFields`);
##   (c) `RawResult.pathTaint` is PRODUCED at the target-hit site;
##   (d) the `.taint`/`.runTaint` writer grep-pin (RFC §2.2 "Scope the
##       totality claim honestly");
##   (e) the lowering pending-taint leak pin (RFC §2.2 last paragraph).
import std/[unittest, strutils, os, algorithm, sets]
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import audit_scan_utils

const clean: Taint = {}   ## ⊥ -- the identity of join

suite "RFC-0005 S1 (a) -- the channel algebra":

  # RFC-0005 S4 reclassified the first rows out of S1's all-⊤ default; every
  # kind NOT in this set must still be dcNoAnswer (later slices extend it).
  const reclassified = {heUnsupportedPointeeRead, seUnsupportedCompoundSortLeaf}

  test "classOf is total and maps every not-yet-reclassified kind to dcNoAnswer (the conservative ⊤ default)":
    for k in SymexErrorKind:
      if k notin reclassified:
        check classOf(k) == dcNoAnswer

  test "pathTaint per class (RFC §2.2 table)":
    check pathTaint(dcFreshSymbol) == {scSpurious}
    check pathTaint(dcSubstituted) == {scSpurious, scIncomplete}
    check pathTaint(dcFabricated)  == {scSpurious, scIncomplete}
    check pathTaint(dcNoAnswer)    == {scSpurious, scIncomplete}
    check pathTaint(dcOmitted)     == clean

  test "runTaint per class (RFC §2.2 table)":
    check runTaint(dcFreshSymbol) == {scSpurious}
    check runTaint(dcSubstituted) == {scSpurious, scIncomplete}
    check runTaint(dcNoAnswer)    == {scSpurious, scIncomplete}
    check runTaint(dcFabricated)  == {scIncomplete}
    check runTaint(dcOmitted)     == {scIncomplete}

  test "dcFabricated is the one class whose path and run coordinates differ in a way no two-literal encoding named (§2.2)":
    check pathTaint(dcFabricated) == {scSpurious, scIncomplete}
    check runTaint(dcFabricated) == {scIncomplete}

  test "the path codomain is closed: only {}, {scSpurious} or ⊤ (§2.6 -- no {scIncomplete}-only path)":
    for c in DegradeClass:
      check pathTaint(c) != {scIncomplete}

  test "channels(k) is (pathTaint(classOf k), runTaint(classOf k)) and is ⊤/⊤ for every not-yet-reclassified kind":
    for k in SymexErrorKind:
      let ch = channels(k)
      check ch.path == pathTaint(classOf(k))
      check ch.run == runTaint(classOf(k))
      if k notin reclassified:
        check ch.path == {scSpurious, scIncomplete}
        check ch.run == {scSpurious, scIncomplete}

  test "runTaintOf derives the run coordinate from drained errors: only sevError contributes (§2.2 severity rule)":
    check runTaintOf(newSeq[SymexErrorInfo]()) == clean
    check runTaintOf(@[SymexErrorInfo(kind: eeUnknownExnType, severity: sevWarning, msg: "w"),
                       SymexErrorInfo(kind: hePtrFamily, severity: sevHint, msg: "h")]) == clean
    check runTaintOf(@[SymexErrorInfo(kind: heUnresolvedRef, severity: sevError, msg: "e")]) ==
      runTaint(classOf(heUnresolvedRef))
    # Union over entries -- the join, not the last writer.
    check runTaintOf(@[SymexErrorInfo(kind: heUnresolvedRef, severity: sevError, msg: "a"),
                       SymexErrorInfo(kind: beBudgetExhausted, severity: sevError, msg: "b")]) ==
      runTaint(classOf(heUnresolvedRef)) + runTaint(classOf(beBudgetExhausted))

suite "RFC-0005 S1 (b) -- the Path carrier and the degrade() funnel (runtime.nim test hook)":
  # `Path`/`WalkCtx`/`Degrade` are private to the runtime unit, so -- exactly
  # the H1 pattern (`h1PathHasHeapFields`) -- one exported hook drives the
  # real templates/procs and reports what it observed.
  let probe = rfc0005S1CarrierProbe()

  test "Path carries `taint: Taint`; the `uncertain: bool` carrier is gone":
    check probe.hasTaintField
    check probe.hasNoUncertainField

  test "forkPath propagates the parent's taint unchanged":
    check probe.forkPathPropagated == {scSpurious}

  test "forkPathTainted joins parent.taint + the Degrade token's path coordinate (never replaces)":
    check probe.forkTaintedJoined == {scSpurious} + pathTaint(classOf(feUnsupportedOp))
    check probe.forkTaintedParentUntouched == {scSpurious}

  test "degrade() records exactly one SymexErrorInfo into the walk sink and its token carries pathTaint(classOf kind)":
    check probe.walkSinkKinds == @[feUnsupportedOp]
    check probe.walkSinkSeverities == @[sevError]
    check probe.tokenPath == pathTaint(classOf(feUnsupportedOp))

  test "each sibling sink records into its OWN seq (heap-depth / new-field-zero / closure), never the walk sink":
    check probe.heapDepthSinkKinds == @[heDepthExhausted]
    check probe.newFieldZeroSinkKinds == @[heNewFieldZeroUnsupported]
    check probe.closureSinkKinds == @[ceInlineBudgetExceeded]
    check probe.closureThreadvarKinds == @[ceInlineBudgetExceeded]

  test "degrade() does NOT write the run coordinate -- it is derived at drain (§2.2)":
    check probe.runTaintBeforeDrain == clean

  test "taintInPlace joins into an existing path (the runtime_heap.nim isNew shape)":
    check probe.taintInPlaceJoined == {scSpurious} + pathTaint(classOf(heNewFieldZeroUnsupported))

  test "the return-merge joins caller and callee taint (union replaces OR)":
    check probe.returnMergeJoined == {scSpurious}
    check probe.returnMergeCleanStaysClean == clean

  test "the lowering funnel joins pathTaint(classOf kind) into the pending taint and records the lowering sink":
    check probe.lowerPendingAfter == pathTaint(classOf(seUnsupportedStringOp))
    check probe.loweringSinkKinds == @[seUnsupportedStringOp]
    check probe.lowerDrainedPath == pathTaint(classOf(seUnsupportedStringOp))
    check probe.lowerPendingAfterDrain == clean

suite "RFC-0005 S1 (c) -- RawResult.pathTaint is produced at the target-hit site":

  test "a clean label hit reports sxSat with pathTaint == {}":
    let prog = SymexProgram(params: @[], body: mkTargetLabel("hit"))
    let raw = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    check raw.status == sxSat
    check raw.pathTaint == clean

  test "no verdict change: an isUnsupported path still blocks SAT and degrades the run to sxUnknown":
    # RFC-0005 S1b: the node carries a kind (was kindless/transitional in S1).
    let prog = SymexProgram(params: @[],
      body: mkBlock(@[mkUnsupported(feUnsupportedStmtKind, "rfc0005 S1 probe"),
                      mkTargetLabel("hit")]))
    let raw = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    check raw.status == sxUnknown
    check raw.errors.len > 0   # Invariant 7 (the backstop still stamps)

# ---- (d) the writer grep-pin -------------------------------------------------
# RFC §2.2 "Scope the totality claim honestly": nothing structural stops a
# future `p.taint = {}` from clearing a tainted path, so this pins the COMPLETE
# set of routines that write the carrier. Read at TEST RUNTIME (`readFile`,
# path fixed at compile time via `currentSourcePath`) -- the N27/N36/pairing
# audit precedent (MSVC C2026 avoidance for a large `staticRead`).

const smtDir = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "smt"

type Writer = tuple[file, routine, line: string]

proc stripTrailingComment(line: string): string =
  ## Drop a trailing `#`/`##` comment (string literals in the runtime unit
  ## never contain the patterns scanned for, so a naive cut is sufficient).
  let ix = line.find(" #")
  if ix >= 0: line[0 ..< ix] else: line

proc routineName(line: string): string =
  ## `proc foo*(...)` / `template bar(...)` at column 0 -> `foo` / `bar`.
  for kw in ["proc ", "template ", "func ", "iterator ", "macro ", "method "]:
    if line.startsWith(kw):
      var i = kw.len
      var name = ""
      while i < line.len and isIdentChar(line[i]):
        name.add line[i]
        inc i
      return name
  ""

proc isTaintWrite(code: string; field: string): bool =
  ## A WRITE of `field` is either `.<field> =` (assignment, not `==`) or a
  ## `<field>: <expr>` object-constructor argument -- but not a
  ## `<field>: Taint` field declaration, and never a longer identifier that
  ## merely contains `field` (`pathTaint`, `taintInPlace`, `kindlessRunTaint`).
  var i = 0
  while true:
    i = code.find(field, i)
    if i < 0: return false
    let before = if i > 0: code[i - 1] else: ' '
    let after = i + field.len
    let afterCh = if after < code.len: code[after] else: ' '
    if not isIdentChar(before) and not isIdentChar(afterCh):
      if before == '.':
        var j = after
        while j < code.len and code[j] == ' ': inc j
        if j < code.len and code[j] == '=' and
           (j + 1 >= code.len or code[j + 1] != '='):
          return true
      elif afterCh == ':' and (after + 1 >= code.len or code[after + 1] != ':'):
        let rest = code[after + 1 .. ^1].strip()
        # A colon ending the line (bare, or before a `#` comment) opens a
        # BLOCK -- `if scIncomplete notin runTaint:  # rule 5` is a read in
        # `decideVerdict` (RFC-0005 S1c), not a constructor argument.
        if rest.len > 0 and rest[0] != '#' and not rest.startsWith("Taint"):
          return true
    i = after

proc scanWriters(src, file, field: string): seq[Writer] =
  var routine = "<top-level>"
  for raw in src.splitLines():
    let r = routineName(raw)
    if r.len > 0: routine = r
    let trimmed = raw.strip()
    if trimmed.len == 0 or isCommentLine(trimmed): continue
    if isTaintWrite(stripTrailingComment(raw), field):
      result.add (file, routine, trimmed)

proc allWriters(field: string): seq[Writer] =
  for path in walkFiles(smtDir / "runtime*.nim"):
    result.add scanWriters(readFile(path), path.extractFilename, field)

proc routinesOf(ws: seq[Writer]): seq[string] =
  var s: HashSet[string]
  for w in ws: s.incl w.file & ":" & w.routine
  for x in s: result.add x
  result.sort()

proc report(ws: seq[Writer]): string =
  for w in ws: result.add "\n  " & w.file & " [" & w.routine & "]: " & w.line

suite "RFC-0005 S1 (d) -- the .taint / .runTaint writer grep-pin":

  test "Path.taint is written ONLY by the fork primitive, taintInPlace, the clean closure-descent root, and the S1 test hook":
    let ws = allWriters("taint")
    checkpoint(report(ws))
    check routinesOf(ws) == @[
      "runtime.nim:applyClosureGround",      # descentBase: `taint: {}` (fresh root)
      "runtime.nim:forkPathTaintPrimitive",  # the ONE fork constructor
      "runtime.nim:rfc0005S1CarrierProbe",   # test hook (synthetic parents)
      "runtime.nim:taintInPlace",            # the mutation-shaped join
    ]

  test "WalkCtx.runTaint is written ONLY at runSymexImpl's drain (derived, never at a site)":
    let ws = allWriters("runTaint")
    checkpoint(report(ws))
    check routinesOf(ws) == @["runtime.nim:runSymexImpl"]

  test "scanner demonstration: an injected site-level write trips the pin; reads and declarations do not":
    check isTaintWrite("    p.taint = {}", "taint")
    check isTaintWrite("  w.runTaint = {scSpurious}", "runTaint")
    check isTaintWrite("  Path(pc: pc, env: env, taint: {})", "taint")
    check not isTaintWrite("    if p.taint != {}:", "taint")
    check not isTaintWrite("    if p.taint == {}:", "taint")
    check not isTaintWrite("    taint: Taint      ## doc", "taint")
    check not isTaintWrite("  w.kindlessRunTaint = true", "runTaint")
    check not isTaintWrite("  let t = pathTaint(classOf(k))", "taint")
    check not isTaintWrite("  if scIncomplete notin runTaint:   # rule 5", "runTaint")
    check not isTaintWrite("  if scIncomplete notin runTaint:", "runTaint")

suite "RFC-0005 S1 (e) -- the lowering pending-taint leak pin (§2.2 last paragraph)":
  let probe = rfc0005S1LeakPinProbe()

  test "a clean walk end stamps nothing":
    check probe.cleanStampedKinds.len == 0

  test "a pending-taint residue at walk end is a classified weInternalWalkerFault (Invariant-7 extension) and is reset":
    check probe.leakStampedKinds == @[weInternalWalkerFault]
    check probe.leakStampedSeverities == @[sevError]
    check probe.pendingAfterStamp == clean
