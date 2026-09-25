## RFC-0005 (soundness channels) slice S4 -- classify the `allocDegrade`
## funnel (§5 row S4, §3.1's substitution rule, §3.2's split discipline).
## The FIRST verdict-changing slice: walker 141 -> 142.
##
## What the site-by-site audit found (every row is pinned in suite (a)):
## the funnel's NAME does not decide the class. Of the kinds `allocDegrade`
## (with its `degradeAlloc` pairing helper and `runtime_heap.nim`'s
## `heapArmDegrade` wrapper) records, most arms FORCE a value or DROP
## behaviour rather than havoc:
##   - `allocateSym`'s Table/HashSet placeholders assert `size == 0`;
##   - its `itUninterp` placeholders (`heUnsupportedOwnership`,
##     `feUnsupportedParamType`, `feUnsupportedWitnessType`) are a 2-valued
##     `svBool` keyed on the allocation's OWN name -- a sort lie, shared by
##     repeat allocations;
##   - `rawAnyAstOf`'s compound-leaf filler is a concrete BV64 `0` that heap
##     stores and closure args consume as a value (`dcSubstituted`);
##   - `walkHeapArm`'s decline arms (`heUnresolvedRef`'s non-ref-SymVal
##     reads/writes, `heRefVariantUnsupported`'s multi-variant field
##     read/write) bind a placeholder WITHOUT the NilAccessDefect fork, or
##     drop the write outright;
##   - `feUnsupportedOp` / `feUnsupportedExprKind` / `weInternalWalkerFault`
##     span several classes or are never an approximation at all.
## Exactly ONE arm substitutes a fresh unconstrained symbol:
## `liftHeapValue`'s unsupported-pointee read (a `string`/`seq`/... field
## through a `ref`, AFTER the nil fork). It shared `heUnresolvedRef` with
## four substituting heap sites and a run-aborting boundary arm, so §3.2's
## split discipline applies: tail-append ONE sibling for the minority
## funnel -- `heUnsupportedPointeeRead`, `dcFreshSymbol` -- and keep
## `heUnresolvedRef` (⊤) for the rest.
##
## §2.1's introduction invariant ("a dcFreshSymbol site's symbol carries no
## constraints at introduction") was VIOLATED by that very site before this
## slice: it named every occurrence `__liftHeapValueUnsupported`, so two
## reads of two different cells were ONE Z3 constant. Under ⊤ that was
## harmless; the moment the class became `dcFreshSymbol` it proved
## `a.s != b.s` unreachable -- a false `sxUnsat`, observed RED here before
## the site moved onto `degradeAlloc` + `freshDegradeName` (suite (c)).
##
## Flip audit (§4.3): the flipped pins are rewritten through
## `checkUnsatOverTaintOnly` (exported from `types.nim` by this slice) in the
## slice that flipped them -- S0's pin 1 and S3's family-2b F1.
import std/[unittest, strutils, os]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import audit_scan_utils

proc kindNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in errs: result.add $e.kind

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc sevErrorKinds(errs: seq[SymexErrorInfo]): seq[SymexErrorKind] =
  for e in errs:
    if e.severity == sevError: result.add e.kind

# ---- SUTs (module scope so the macro resolves them via getImpl) -------------

type
  S4Node = ref object
    s: string

  S4KindA = enum s4KindA1, s4KindA2
  S4KindB = enum s4KindB1, s4KindB2
  S4MultiObj = object
    case kindA: S4KindA
    of s4KindA1: a1: int
    of s4KindA2: a2: int
    case kindB: S4KindB
    of s4KindB1: b1: int
    of s4KindB2: b2: int

## The exhibit shape (S0 pin 1's twin): a string field read through a `ref`
## is the only degrade; the target is a value-independent contradiction over
## a clean `int`.
proc s4DeadFreshSymbol(p: S4Node, n: int) =
  if p != nil:
    discard p.s
  if n == 5 and n == 6:
    symexTarget("s4_dead_fresh_symbol")

## The degraded value itself feeds the (unreachable) target: the fresh symbol
## ranges over EVERY string, and still no string equals both literals. Bound
## ONCE (`let v = p.s`): each deref is its OWN fresh symbol (the introduction
## invariant, suite (c)), so `p.s == "abc" and p.s == "xyz"` -- two reads --
## is satisfiable in the model (two independent symbols) and correctly stays a
## spurious candidate (sxUnknown), not an UNSAT: over-approximation may cost
## precision, never soundness.
proc s4DeadThroughValue(p: S4Node) =
  if p != nil:
    let v = p.s
    if v == "abc" and v == "xyz":
      symexTarget("s4_dead_through_value")

## The two-read spelling of the same contradiction: a spurious candidate.
proc s4TwoReadsSpurious(p: S4Node) =
  if p != nil:
    if p.s == "abc" and p.s == "xyz":
      symexTarget("s4_two_reads_spurious")

## Reachable ONLY through the degraded read: a candidate, never a clean win.
proc s4LiveThroughValue(p: S4Node) =
  if p != nil:
    if p.s == "hello":
      symexTarget("s4_live_through_value")

## §2.1's introduction invariant: two DIFFERENT cells are independent in
## reality, so `a.s != b.s` is reachable. A shared placeholder name made the
## two reads one Z3 constant and proved this unreachable (false sxUnsat).
proc s4TwoCells(a, b: S4Node) =
  if a != nil and b != nil:
    if a.s != b.s:
      symexTarget("s4_two_cells")

## Same invariant, repeat hits of the site across loop iterations.
proc s4TwoCellsLoop(a, b: S4Node) =
  if a != nil and b != nil:
    var first = ""
    var differ = false
    for i in 0 .. 1:
      let cur = if i == 0: a.s else: b.s
      if i == 0: first = cur
      elif cur != first: differ = true
    if differ:
      symexTarget("s4_two_cells_loop")

## Must-NOT-promote: the `heRefVariantUnsupported` heap arm (reaches
## `allocDegrade` through `heapArmDegrade`) skips the nil-deref fork, so it
## stays ⊤ and an unreachable target through it stays sxUnknown.
proc s4MultiVariantDead(p: ref S4MultiObj, n: int) =
  if p != nil:
    discard p.a1
  if n == 5 and n == 6:
    symexTarget("s4_multivariant_dead")

# =============================================================================
# Oracles -- the same facts executed for real (house rule)
# =============================================================================

suite "RFC-0005 S4 -- oracles":

  test "oracle: n == 5 and n == 6 is a genuine contradiction":
    for n in [0, 5, 6, -1]:
      check not (n == 5 and n == 6)

  test "oracle: no string equals both \"abc\" and \"xyz\"":
    for s in ["abc", "xyz", "", "hello"]:
      check not (s == "abc" and s == "xyz")

  test "oracle: two distinct cells CAN hold different strings (the two-cells target is reachable)":
    let a = S4Node(s: "x")
    let b = S4Node(s: "y")
    check a.s != b.s

# =============================================================================
# (a) the classification rows S4 wrote (types.nim `classOf`, rows marked S4)
# =============================================================================

suite "RFC-0005 S4 (a) -- the allocDegrade funnel's classOf rows":

  test "heUnsupportedPointeeRead is dcFreshSymbol: {scSpurious} on the path AND the run":
    check classOf(heUnsupportedPointeeRead) == dcFreshSymbol
    check channels(heUnsupportedPointeeRead).path == {scSpurious}
    check channels(heUnsupportedPointeeRead).run == {scSpurious}

  test "seUnsupportedCompoundSortLeaf is dcSubstituted (a concrete BV64 0 filler consumed as a value)":
    check classOf(seUnsupportedCompoundSortLeaf) == dcSubstituted

  test "every other kind the funnel records is audited ⊤ -- never promoted by S4":
    for k in [heUnresolvedRef, heRefVariantUnsupported, heUnsupportedOwnership,
              seUnsupportedTableKeyType, seUnsupportedTableValType,
              seUnsupportedSetCharInterop, feUnsupportedParamType,
              feUnsupportedWitnessType, feUnsupportedExprKind,
              weInternalWalkerFault]:
      checkpoint($k)
      check classOf(k) == dcNoAnswer
      check scIncomplete in runTaint(classOf(k))
    # RFC-0005 S6b classified `feUnsupportedOp` (still ⊤ on both coordinates:
    # dcSubstituted) and moved this funnel's one fresh-symbol emission (the
    # uninterpreted-ref merge) to `feUnsupportedOpHavoc`.
    check classOf(feUnsupportedOp) == dcSubstituted
    check scIncomplete in runTaint(classOf(feUnsupportedOp))
    check classOf(feUnsupportedOpHavoc) == dcFreshSymbol

  test "the split is a TAIL append (ordinal stability, §3.2)":
    ## RFC-0005 S5 tail-appended `seRuneDecodeSymbolic` after this kind; the
    ## pin is the ordinal adjacency, not `.high`, so later splits keep it.
    check ord(heUnsupportedPointeeRead) == ord(beSolverUndef) + 1
    check ord(seRuneDecodeSymbolic) == ord(heUnsupportedPointeeRead) + 1

# =============================================================================
# (b) the flip: an over-taint-only run that proves the target unreachable
# =============================================================================

suite "RFC-0005 S4 (b) -- over-taint-only UNSAT (§0.3's recovered capability)":

  test "the exhibit shape flips sxUnknown -> sxUnsat, over-taint-only by checkUnsatOverTaintOnly":
    let r = symexFind(s4DeadFreshSymbol, tLabel("s4_dead_fresh_symbol"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[heUnsupportedPointeeRead]

  test "a contradiction THROUGH the fresh value is still sxUnsat (the symbol is free, not pinned)":
    let r = symexFind(s4DeadThroughValue, tLabel("s4_dead_through_value"))
    checkpoint($kindNames(r.errors))
    checkUnsatOverTaintOnly(r)
    check sevErrorKinds(r.errors) == @[heUnsupportedPointeeRead]

  test "two reads of one cell are two fresh symbols: the contradiction is a spurious candidate -> sxUnknown, never sxUnsat":
    let r = symexFind(s4TwoReadsSpurious, tLabel("s4_two_reads_spurious"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(heUnsupportedPointeeRead)

  test "a target reachable ONLY through the fresh value is a candidate: sxUnknown, never sxSat or sxUnsat (§2.3 rule 4)":
    let r = symexFind(s4LiveThroughValue, tLabel("s4_live_through_value"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(heUnsupportedPointeeRead)

# =============================================================================
# (c) §2.1's introduction invariant for heUnsupportedPointeeRead
# =============================================================================

suite "RFC-0005 S4 (c) -- introduction invariant: the fresh symbol carries no constraint":

  test "two cells' reads are independent symbols -- never sxUnsat (RED before freshDegradeName)":
    let r = symexFind(s4TwoCells, tLabel("s4_two_cells"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat
    check r.status == sxUnknown           ## a candidate (rule 4) until S10's replay
    check r.errors.hasKind(heUnsupportedPointeeRead)

  test "repeat hits of the site across loop iterations are independent -- never sxUnsat":
    let r = symexFind(s4TwoCellsLoop, tLabel("s4_two_cells_loop"))
    checkpoint($kindNames(r.errors))
    check r.status != sxUnsat

  test "structural: the site allocates through degradeAlloc (freshDegradeName), never a fixed name":
    const heapSrc = currentSourcePath.parentDir() / ".." / "src" / "nelli" /
                    "smt" / "runtime_heap.nim"
    var emitting: seq[string]
    for raw in readFile(heapSrc).splitLines():
      let t = raw.strip()
      if t.len == 0 or isCommentLine(t): continue
      if "heUnsupportedPointeeRead" in t: emitting.add t
    checkpoint($emitting)
    check emitting.len == 1
    check emitting[0].startsWith("degradeAlloc(")
    check "__liftHeapValueUnsupported\", freshLiftPc" notin readFile(heapSrc)

  test "IR level: the tainted path carries exactly {scSpurious}; unreachable is sxUnsat":
    let pRef = tRef(tString())
    let params = @[IRParam(name: "p", ty: pRef)]
    # Guarded `p != nil` so `nilDerefFork` short-circuits (a NilAccessDefect
    # sxRaised would otherwise win the label target's precedence).
    let body = mkBlock(@[mkIf(@[mkBranch(
      mkBinop(bNe, mkVar("p"), mkNil(pRef)),
      mkBlock(@[mkDeref("v", mkVar("p"), tString()), mkTargetLabel("hit")]))])])
    let prog = SymexProgram(params: params, body: body)
    let hit = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    checkpoint($kindNames(hit.errors))
    check hit.status == sxUnknown
    check hit.candidates.len == 1
    check hit.candidates[0].pathTaint == {scSpurious}
    check hit.errors.hasKind(heUnsupportedPointeeRead)
    let nowhere = runSymex(prog, SymexTarget(kind: stkLabel, label: "nowhere"))
    checkpoint($kindNames(nowhere.errors))
    check nowhere.status == sxUnsat
    check nowhere.candidates.len == 0

# =============================================================================
# (d) must-NOT-promote: the funnel's ⊤ siblings keep blocking sxUnsat
# =============================================================================

suite "RFC-0005 S4 (d) -- the funnel's substituting arms stay ⊤":

  test "heRefVariantUnsupported (heapArmDegrade, nil fork skipped) keeps an unreachable target sxUnknown":
    let r = symexFind(s4MultiVariantDead, tLabel("s4_multivariant_dead"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(heRefVariantUnsupported)
    check scIncomplete in runTaintOf(r.errors)

  test "checkUnsatOverTaintOnly rejects an sxUnknown result":
    let r = SymexResult[int](status: sxUnknown,
      errors: @[SymexErrorInfo(kind: heUnsupportedPointeeRead,
                               severity: sevError, msg: "m")])
    expect AssertionDefect:
      checkUnsatOverTaintOnly(r)

  test "checkUnsatOverTaintOnly rejects an sxUnsat carrying an under-approximating kind":
    let r = SymexResult[int](status: sxUnsat,
      errors: @[SymexErrorInfo(kind: heUnresolvedRef, severity: sevError,
                               msg: "m")])
    expect AssertionDefect:
      checkUnsatOverTaintOnly(r)

  test "checkUnsatOverTaintOnly ignores warnings/hints (the §2.2 severity rule)":
    let r = SymexResult[int](status: sxUnsat,
      errors: @[SymexErrorInfo(kind: beBudgetExhausted, severity: sevWarning,
                               msg: "m")])
    checkUnsatOverTaintOnly(r)

suite "RFC-0005 S4 -- walker version pin":

  test "walker version floor >= 142 (S4 classifies the allocDegrade funnel)":
    check parseInt(symexWalkerVersion) >= 142
