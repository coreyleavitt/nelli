## RFC-0005 (soundness channels) slice S8 -- decline scope (§2.5, §6.6) and
## the i3 annotation-violation channel (§13.3). Walker 147 -> 148.
##
## S9 deletes the blanket vetoes (`capForcedUnknown`/`closureForcedUnknown`)
## on the strength of the structural guarantee pinned here: every decline the
## run coordinate admits (`taintsRun`) says WHERE it sits, so the verdict can
## ask "was it reached?" instead of insuring against the answer. Suites:
##   (a) i3 end to end -- a false `{.symexTransparent.}` claim rides
##       `annotationViolations` through `symexFind`, not `errors`;
##   (b) the scope battery -- one SUT per decline-site class, each asserting
##       its scope and that the run's bucket-4 (`dskUnplaced`) list is
##       exactly the enumerated one;
##   (c) reach -- a parse record and the walker's reach record join on one
##       anchor; an unreached decline has the parse record only;
##   (d) the verdict flips the i3 split causes, each justified per §4.3;
##   (e) structural -- the totality pin over the source: every writer of a
##       parse record is a funnel, every marker is minted by one, and every
##       `sevError` `SymexErrorInfo` construction names its scope;
##   (f) the walker version floor.
import std/[unittest, macros, strutils, os, tables]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/dsl_parser
import nelli/smt/canonicalize
import audit_scan_utils

macro progOf(fn: typed): untyped =
  ## The `SymexProgram` `symexFind` would build for `fn` (incl. the S8
  ## annotation channel), so a test reads the raw `RawResult`.
  let parsed = parseEntryImpl(fn, "progOf",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  let b = parsed.bodyNimNode
  let p = parsed.paramsNimNode
  let pr = parsed.procsNimNode
  let u = parsed.userExnHierarchyNimNode
  let pe = parsed.parseErrorsNimNode
  let av = parsed.annotationViolationsNimNode
  result = quote do:
    SymexProgram(params: `p`, body: `b`, procs: `pr`,
                 userExnHierarchy: `u`, parseErrors: `pe`,
                 annotationViolations: `av`)

macro progOfCapped(fn: typed; cap: static int): untyped =
  ## `progOf` under a per-proc instantiation cap (the `geInstantiationCapped`
  ## callee-key decline).
  let parsed = parseEntryImpl(fn, "progOfCapped", cap)
  let b = parsed.bodyNimNode
  let p = parsed.paramsNimNode
  let pr = parsed.procsNimNode
  let u = parsed.userExnHierarchyNimNode
  let pe = parsed.parseErrorsNimNode
  let av = parsed.annotationViolationsNimNode
  result = quote do:
    SymexProgram(params: `p`, body: `b`, procs: `pr`,
                 userExnHierarchy: `u`, parseErrors: `pe`,
                 annotationViolations: `av`)

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & "@" & $e.scope
  "[" & parts.join(", ") & "]"

proc scopesOf(errs: seq[SymexErrorInfo]; k: SymexErrorKind): seq[DeclineScope] =
  for e in errs:
    if e.kind == k and taintsRun(e): result.add e.scope

const bucket4: seq[string] = @[]
  ## RFC-0005 S8 (§2.5 point 4). The named bucket-4 members any battery SUT
  ## below may produce: EMPTY. The one construction that is `dskUnplaced` by
  ## design -- `runSymexImpl`'s Invariant-7 backstop, recorded only when a
  ## run is `sxUnknown` with NOTHING recorded -- is enumerated in (e) by
  ## name, and no battery run reaches it (the backstop firing is itself a
  ## walker bug). A non-empty list here is an enumerated defect, never a
  ## tolerance.

proc unplacedNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in unplacedDeclines(errs): result.add $e.kind

# =============================================================================
# SUTs
# =============================================================================

var probeS8State = 11   ## module-level: unmodellable, and deliberately so

proc probeS8(): int {.symexTransparent.} = probeS8State

proc usesProbeS8(x: int) =
  ## A transparent callee whose RESULT is used: `avResultUsed`.
  let p = probeS8()
  if x + p == 0x5A4D:
    symexTarget("s8_probe")

proc bumpS8(v: var int) {.symexTransparent.} =
  inc v

proc argNotInertS8(x: int) =
  ## A transparent callee handed a `var`: `avArgNotInert`.
  var m = x
  bumpS8(m)
  if m != x:
    symexTarget("s8_bump")

proc flipSatS8(x: int) =
  ## (d) The target's path never passes the over-claimed call: pre-S8 the
  ## parse-time `feTransparentResultUsed` (sevError) vetoed the whole run to
  ## `sxUnknown`; now only the OTHER path is tainted (by the opaque
  ## fallback), and the hit is a clean `sxSat`.
  if x == 7:
    symexTarget("s8_flip_sat")
  else:
    let p = probeS8()
    discard p

proc flipUnsatS8(x: int) =
  ## (d) A dead target behind the same over-claim: nothing reaches it, and
  ## the only run record is the opaque call's own walk-time degrade.
  let p = probeS8()
  if x > 5 and x < 3 and p > 0:
    symexTarget("s8_flip_unsat")

proc castS8(x: int) =
  ## Class A, site-anchored: the CR-2a catch-all (`cast[int32]` operand).
  let y = cast[int32](x) + 1
  if y == 1:
    symexTarget("s8_cast")

proc castDeadS8(x: int) =
  ## Class A, site-anchored, UNREACHED: the decline sits in a handler no
  ## raise is routed to, so no path's walk reaches its marker. (The walker
  ## forks `if` branches without a feasibility check, so an infeasible guard
  ## would NOT make a site unreached -- reach is per walked path.)
  try:
    if x == 4:
      symexTarget("s8_cast_dead_live")
  except ValueError:
    let y = cast[int32](x) + 1
    if y == 1:
      symexTarget("s8_cast_dead")

proc classBS8(x: int) =
  ## Class B: an augmented assignment outside the modelled set -- a marker
  ## with no parse record (its reach record is its only record).
  var f = float(x)
  f /= 2.0
  if f > 1.0:
    symexTarget("s8_classb")

proc unsafeCastS8(x: int) =
  ## The `isUnsafeCast` sibling of Class A.
  var y = x
  let p = addr y
  if p[] == 3:
    symexTarget("s8_unsafe")

proc szofS8[T](x: T): int = sizeof(T)

proc cappedS8(a: int8, b: int16, c: int32) =
  ## Callee key: the third `szofS8` instantiation is over a cap of 2.
  if szofS8(a) == 1 and szofS8(b) == 2 and szofS8(c) == 4:
    symexTarget("s8_capped")

proc signatureS8(t: Table[string, string], y: int) =
  ## Signature: the parameter type itself cannot be allocated.
  if y == 1:
    symexTarget("s8_sig")

proc opaqueS8(x: int) =
  ## Walk site: an unmodelled opaque call, recorded by the walk that
  ## reached it.
  let s = $x
  if s.len == 3:
    symexTarget("s8_opaque")

proc cleanS8(x: int) =
  if x == 9:
    symexTarget("s8_clean")

# =============================================================================
# (a) i3 end to end
# =============================================================================

suite "RFC-0005 S8 (a) -- a false annotation claim is its own channel (§13.3, i3)":

  test "oracle: usesProbeS8 really gates on x + 11 == 0x5A4D":
    doAssert probeS8State == 11
    usesProbeS8(0)
    usesProbeS8(0x5A4D - 11)

  test "result-used: symexFind carries it on annotationViolations with pragma, callee and site":
    let r = symexFind(usesProbeS8, tLabel("s8_probe"))
    checkpoint(show(r.errors))
    check r.annotationViolations.len == 1
    let av = r.annotationViolations[0]
    check av.pragma == saSymexTransparent
    check av.kind == avResultUsed
    check av.callee == "probeS8"
    check "tsymex_rfc0005_s8_scope" in av.site
    check av.site.count(':') >= 2          # file:line:col
    check "statement position" in av.msg

  test "result-used: it is NOT a decline -- no retired kind in errors; the opaque fallback still taints":
    let r = symexFind(usesProbeS8, tLabel("s8_probe"))
    checkpoint(show(r.errors))
    var opaque = false
    for e in r.errors:
      check e.kind notin {feTransparentResultUsed, feTransparentArgNotInert}
      if e.kind == feOpaqueCallUnmodelled and "probeS8" in e.msg: opaque = true
    check opaque
    check r.status != sxUnsat

  test "arg-not-inert: the var-argument overclaim is avArgNotInert on the same channel":
    let r = symexFind(argNotInertS8, tLabel("s8_bump"))
    checkpoint(show(r.errors))
    check r.annotationViolations.len == 1
    check r.annotationViolations[0].kind == avArgNotInert
    check r.annotationViolations[0].callee == "bumpS8"
    for e in r.errors:
      check e.kind notin {feTransparentResultUsed, feTransparentArgNotInert}
    check r.status != sxUnsat

  test "the channel is on RawResult on every branch, and verdict-neutral: no parse record, no run taint":
    let prog = progOf(usesProbeS8)
    check prog.annotationViolations.len == 1
    check prog.parseErrors.len == 0
    let r = runSymex(prog, tLabel("s8_probe"))
    check r.annotationViolations == prog.annotationViolations
    check runTaintOf(prog.parseErrors) == Taint({})

  test "a clean SUT has an empty channel":
    let r = symexFind(cleanS8, tLabel("s8_clean"))
    check r.status == sxSat
    check r.annotationViolations.len == 0

# =============================================================================
# (b) the scope battery
# =============================================================================

suite "RFC-0005 S8 (b) -- every decline names its scope; bucket 4 is the enumerated list":

  test "Class A (site-anchored parse decline)":
    let prog = progOf(castS8)
    checkpoint(show(prog.parseErrors))
    check prog.parseErrors.len == 1
    check prog.parseErrors[0].kind == feUnsupportedExprKind
    check prog.parseErrors[0].scope.kind == dskSiteAnchored
    check prog.parseErrors[0].scope.markerId >= 1
    let r = runSymex(prog, tLabel("s8_cast"))
    checkpoint(show(r.errors))
    check unplacedNames(r.errors) == bucket4

  test "Class B (marker only: no parse record; the reach record is anchored)":
    let prog = progOf(classBS8)
    check prog.parseErrors.len == 0
    let r = runSymex(prog, tLabel("s8_classb"))
    checkpoint(show(r.errors))
    let sc = scopesOf(r.errors, feUnsupportedStmtKind)
    check sc.len >= 1
    for s in sc: check s.kind == dskSiteAnchored
    check unplacedNames(r.errors) == bucket4

  test "unsafe cast (site-anchored at the isUnsafeCast marker)":
    let prog = progOf(unsafeCastS8)
    checkpoint(show(prog.parseErrors))
    check prog.parseErrors.len == 1
    check prog.parseErrors[0].kind == heUnsafeCast
    check prog.parseErrors[0].scope.kind == dskSiteAnchored
    let r = runSymex(prog, tLabel("s8_unsafe"))
    checkpoint(show(r.errors))
    check r.status == sxUnknown
    check unplacedNames(r.errors) == bucket4

  test "callee key (over-cap instantiation, never registered)":
    let prog = progOfCapped(cappedS8, 2)
    checkpoint(show(prog.parseErrors))
    check prog.parseErrors.len == 1
    check prog.parseErrors[0].kind == geInstantiationCapped
    check prog.parseErrors[0].scope.kind == dskCalleeKey
    check prog.parseErrors[0].scope.calleeKey notin prog.procs
    let r = runSymex(prog, tLabel("s8_capped"))
    checkpoint(show(r.errors))
    check unplacedNames(r.errors) == bucket4

  test "signature (a parameter type the allocator declines)":
    let r = runSymex(progOf(signatureS8), tLabel("s8_sig"))
    checkpoint(show(r.errors))
    check r.status == sxUnknown
    var sig = 0
    for e in r.errors:
      if taintsRun(e) and e.scope.kind == dskSignature: inc sig
    check sig >= 1
    check unplacedNames(r.errors) == bucket4

  test "walk site (opaque call recorded by the walk that reached it)":
    let r = runSymex(progOf(opaqueS8), tLabel("s8_opaque"))
    checkpoint(show(r.errors))
    for s in scopesOf(r.errors, feOpaqueCallUnmodelled):
      check s.kind == dskWalkSite
    check unplacedNames(r.errors) == bucket4

  test "the i3 SUTs: no bucket-4 entry either":
    for r in [runSymex(progOf(usesProbeS8), tLabel("s8_probe")),
              runSymex(progOf(argNotInertS8), tLabel("s8_bump"))]:
      checkpoint(show(r.errors))
      check unplacedNames(r.errors) == bucket4

# =============================================================================
# (c) reach
# =============================================================================

suite "RFC-0005 S8 (c) -- reach joins on the anchor":

  test "a reached Class-A decline: parse record and walk record share one marker":
    let prog = progOf(castS8)
    let m = prog.parseErrors[0].scope.markerId
    let r = runSymex(prog, tLabel("s8_cast"))
    checkpoint(show(r.errors))
    var anchored = 0
    for s in scopesOf(r.errors, feUnsupportedExprKind):
      check s.kind == dskSiteAnchored
      if s.kind == dskSiteAnchored and s.markerId == m: inc anchored
    check anchored == 2       # the parse record + the reach record

  test "an unreached Class-A decline: the parse record alone (S9's reach question has an answer)":
    let prog = progOf(castDeadS8)
    check prog.parseErrors.len == 1
    let m = prog.parseErrors[0].scope.markerId
    let r = runSymex(prog, tLabel("s8_cast_dead_live"))
    checkpoint(show(r.errors))
    var anchored = 0
    for s in scopesOf(r.errors, feUnsupportedExprKind):
      if s.kind == dskSiteAnchored and s.markerId == m: inc anchored
    check anchored == 1
    # Vetoes retained (S8 moves no verdict): still `sxUnknown` today; the
    # verdict without the vetoes is the clean hit S9 will report.
    check r.status == sxUnknown
    check rfc0005UnvetoedStatus == sxSat

  test "a reached unsafe cast records its reach under the parse record's marker":
    let prog = progOf(unsafeCastS8)
    let m = prog.parseErrors[0].scope.markerId
    let r = runSymex(prog, tLabel("s8_unsafe"))
    checkpoint(show(r.errors))
    var anchored = 0
    for s in scopesOf(r.errors, heUnsafeCast):
      if s.kind == dskSiteAnchored and s.markerId == m: inc anchored
    check anchored == 2

  test "a reached over-cap callee records its reach under the same key":
    let prog = progOfCapped(cappedS8, 2)
    let k = prog.parseErrors[0].scope.calleeKey
    let r = runSymex(prog, tLabel("s8_capped"))
    checkpoint(show(r.errors))
    var keyed = 0
    for s in scopesOf(r.errors, geInstantiationCapped):
      if s.kind == dskCalleeKey and s.calleeKey == k: inc keyed
    check keyed == 2

  test "markers are unique per parse":
    let prog = progOf(castDeadS8)
    check prog.parseErrors[0].scope.markerId >= 1

# =============================================================================
# (d) verdict flips caused by the i3 split (§4.3)
# =============================================================================

suite "RFC-0005 S8 (d) -- the i3 flips, each justified":

  test "oracle: flipSatS8 reaches its label at x == 7":
    flipSatS8(7)

  test "sxUnknown -> sxSat: a clean hit is no longer vetoed by a non-decline (§2.3 rule 1)":
    ## Pre-S8 the parse-time `feTransparentResultUsed` (sevError) tripped the
    ## cap veto, suppressing rule 1 for the whole run. It was never a decline
    ## -- nothing is approximated because of it; the opaque fallback's own
    ## walk-time `feOpaqueCallUnmodelled` taints every path through the call
    ## -- so the hit, on a path that never passes the call, is clean.
    let r = symexFind(flipSatS8, tLabel("s8_flip_sat"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.witness[0] == 7
    check r.annotationViolations.len == 1
    check r.annotationViolations[0].kind == avResultUsed

  test "no unsat flip: a dead target behind the over-claim stays sxUnknown":
    ## The split removes a parse record, never a walk record: the opaque
    ## fallback's `feOpaqueCallUnmodelled` is `dcSubstituted`, whose run
    ## coordinate carries `scIncomplete`, so rule 5 stays blocked (§4.3: an
    ## `sxUnsat` flip would need every admitted record to leave the claim
    ## sound, and this one does not).
    let r = symexFind(flipUnsatS8, tLabel("s8_flip_unsat"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxUnknown
    check r.annotationViolations.len == 1

# =============================================================================
# (e) structural -- the totality pin
# =============================================================================

const smtDir = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "smt"
const parserSrc = smtDir / "dsl_parser.nim"

proc routineName(line: string): string =
  for kw in ["proc ", "template ", "func ", "iterator ", "macro ", "method "]:
    if line.startsWith(kw):
      var i = kw.len
      var name = ""
      while i < line.len and (line[i].isAlphaNumeric or line[i] == '_'):
        name.add line[i]
        inc i
      return name
  ""

proc codeLines(path: string): seq[tuple[routine, line: string]] =
  var routine = "<top-level>"
  for raw in readFile(path).splitLines():
    let r = routineName(raw)
    if r.len > 0: routine = r
    let t = raw.strip()
    if t.len == 0 or isCommentLine(t): continue
    result.add (routine, t)

proc stripComments(src: string): string =
  ## Source with every whole-line comment and every trailing `#` comment
  ## (outside a string literal) removed, lines kept.
  for raw in src.splitLines():
    let t = raw.strip()
    if isCommentLine(t):
      result.add "\n"
      continue
    var inStr = false
    var cut = raw.len
    for i, c in raw:
      if c == '"' and (i == 0 or raw[i-1] != '\\'): inStr = not inStr
      elif c == '#' and not inStr:
        cut = i
        break
    result.add raw[0 ..< cut] & "\n"

proc constructions(src, head: string): seq[tuple[routine, text: string]] =
  ## Every `head(` ... `)` construction in `src` (comment-stripped), balanced
  ## on parentheses, tagged with its enclosing top-level routine.
  let code = stripComments(src)
  var routine = "<top-level>"
  var i = 0
  var lineStart = 0
  while i < code.len:
    if i == lineStart:
      let eol = code.find('\n', i)
      let line = code[i ..< (if eol < 0: code.len else: eol)]
      let r = routineName(line)
      if r.len > 0: routine = r
    if code[i] == '\n':
      lineStart = i + 1
      inc i
      continue
    if code.continuesWith(head & "(", i) and
       (i == 0 or not isIdentChar(code[i-1])):
      var depth = 0
      var j = i + head.len
      while j < code.len:
        if code[j] == '(': inc depth
        elif code[j] == ')':
          dec depth
          if depth == 0: break
        inc j
      result.add (routine, code[i .. min(j, code.len - 1)])
      i = j
      continue
    inc i

proc srcFiles(): seq[string] =
  for f in walkFiles(smtDir / "*.nim"): result.add f
  result.add smtDir / ".." / "symex.nim"

suite "RFC-0005 S8 (e) -- structural totality pin":

  test "only the decline funnels write ctx.parseErrors":
    var writers: seq[string]
    for (r, t) in codeLines(parserSrc):
      if "parseErrors.add" in t: writers.add r
    checkpoint($writers)
    for w in writers:
      check w in ["declineAtSite", "declineUnsafeCast", "declineCallee"]
    check writers.len == 3

  test "every parser marker is minted by a funnel (no bare mkUnsupported / mkUnsafeCast)":
    var minters: seq[string]
    for (r, t) in codeLines(parserSrc):
      if "mkUnsupported(" in t or "mkUnsafeCast(" in t: minters.add r
    checkpoint($minters)
    for m in minters:
      check m in ["declineAtSite", "declineMarker", "declineUnsafeCast"]

  test "no parser site records a retired transparent kind (§13.3, i3)":
    for (r, t) in codeLines(parserSrc):
      check "feTransparentResultUsed" notin t
      check "feTransparentArgNotInert" notin t

  test "every sevError SymexErrorInfo construction in src names its scope (the one unplaced one by name)":
    ## §2.5 point 4, pinned against the code: a construction that could be
    ## admitted by `taintsRun` without a scope would default to `dskUnplaced`
    ## silently. The one deliberate `dskUnplaced` construction is the
    ## Invariant-7 backstop in `runSymexImpl` (recorded only when nothing
    ## else was -- there is no site to name); it must say so explicitly.
    var admitted = 0
    var unplacedByDesign: seq[string]
    for f in srcFiles():
      for (r, t) in constructions(readFile(f), "SymexErrorInfo"):
        let decline = "sevError" in t or "severity: severity" in t
        if not decline: continue
        inc admitted
        checkpoint(f.extractFilename & " " & r & ": " & t.replace("\n", " "))
        check "scope:" in t
        if "dskUnplaced" in t: unplacedByDesign.add r
    check admitted >= 30
    check unplacedByDesign == @["runSymexImpl"]

  test "the walker's anchor-bearing arms pass the parse-minted anchor":
    let rt = readFile(smtDir / "runtime.nim")
    check "scope = siteAnchored(stmt.unMarker)" in rt
    check "scope = siteAnchored(stmt.ucMarker)" in rt
    check "scope = calleeKeyed(stmt.callee)" in rt

  test "the placement check runs before the parse records are emitted":
    var seen: seq[string]
    for (r, t) in codeLines(parserSrc):
      if r != "parseProc": continue
      if t.startsWith("placeDeclineScopes("): seen.add "place"
      if "emitErrorSeq(ctx.parseErrors)" in t: seen.add "emit"
    check seen == @["place", "emit"]

# =============================================================================
# (f) walker version floor
# =============================================================================

suite "RFC-0005 S8 -- walker version pin":

  test "walker version floor >= 148 (S8: decline scope + the i3 channel)":
    check parseInt(symexWalkerVersion) >= 148
