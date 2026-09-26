## RFC-0005 (soundness channels) slice S1c -- the verdict rule (§2.3): the
## ordered decision procedure, the candidate pool, the `isTargetLabel` solve,
## and `routeRaise` no longer killing tainted paths (§2.6).
##
## Before S1c the walker REFUSED to solve a tainted path: `isTargetLabel`
## skipped `trySolve` and `routeRaise` dropped the path outright, each
## marking the run with a kindless ⊤ (`kindlessRunDegrade`). That skip is
## itself an omission (§0.1), so the UNSAT half of the verdict rule could not
## be relaxed on top of it without minting a false `sxUnsat`. S1c solves every
## path that reaches the target: a SAT on a clean path enters `w.found` (and
## may halt the walk, `shouldStop`); a SAT on an `scSpurious`-tainted path
## becomes a CANDIDATE in a separate pool that never halts the walk and never
## wins by itself (only S10's replay can promote one). Any solved SAT --
## candidate included -- blocks `sxUnsat` (rule 4).
##
## Still all-⊤ (`classOf` maps every kind to `dcNoAnswer`), so every tainted
## path's degrade already puts `scIncomplete` in `runTaint`, and no verdict
## moves. What IS observable today, and pinned below:
##   (a) the solve now RUNS on a tainted path (a solver resource-out there is
##       recorded as `beSolverUndef`, where the skip recorded nothing);
##   (b) a tainted raise is ROUTED (its handler body is walked) instead of
##       killed;
##   (c) a clean witness discovered AFTER a tainted one still wins (the
##       §4.1 family-1 witness-monotonicity pin, tainted arm first);
##   (d) the lowering pending-taint leak S1b measured in
##       `tsymex_r6_n40_alloc_totality` (N40-4) is consumed onto its path,
##       and the concolic collect now runs the walk-end leak stamp too;
##   (e) the candidate pool itself, read off `RawResult.candidates` (the
##       pool RFC-0005 S10's replay consumes);
##   (f) every rule of the ordered procedure, driven directly through the
##       pure `decideVerdict` -- the only place rule 4 (a candidate blocks
##       `sxUnsat`) is distinguishable from rule 5 before S4 classifies a
##       funnel out of ⊤;
##   (g) a tainted path's solve is BOUNDED (`taintedSolveRLimit`): the N36
##       `iekStrInOptionRegion` residue spun Z3's `check` forever once the
##       skip was lifted -- a new non-termination S1c itself introduced.
import std/[unittest, tables, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize

proc kindNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in errs: result.add $e.kind

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# ---- SUTs (module scope so the macro resolves them via getImpl) -------------

proc s1cSensor(): int {.symexOpaque.} = 7
  ## An opaque call whose result is USED: every path through it is tainted
  ## (`feOpaqueCallUnmodelled`) -- the RFC's over-taint shape.

const tightRLimit = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 1'u,
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 5))

# (a) the only path reaching the target is tainted; under `queryRLimit = 1`
# its solve returns unknown -- which can only be observed if the solve runs.
proc s1cTaintedRareLabel(a, b, c, d: int) =
  let s = s1cSensor()
  if s > 0 and a * b * c * d == 1234567:
    symexTarget("s1c_rare")

proc s1cTaintedRareRaise(a, b, c, d: int) =
  let s = s1cSensor()
  if s > 0 and a * b * c * d == 1234567:
    raise newException(ValueError, "s1c rare")

# (b) a tainted raise caught by a handler whose body holds a Class-B
# `isUnsupported` (a field-LHS augmented assignment) -- recorded only where a
# path actually reaches it, so its kind appears iff the handler is walked.
type S1cPoint = object
  x, y: int

proc s1cTaintedCaught(p: S1cPoint, b: int) =
  let s = s1cSensor()
  try:
    if b + s > 0:
      raise newException(ValueError, "s1c tainted raise")
  except ValueError:
    var q = p
    q.x += b
  symexTarget("s1c_after_catch")

# (c) witness monotonicity, tainted arm FIRST: the `if` arm is walked before
# the `elif`, and its path is tainted by the opaque call.
proc s1cTaintedFirst(x: int) =
  if x < 0:
    let s = s1cSensor()
    if x + s == -100:
      symexTarget("s1c_mono")
  elif x == 42:
    symexTarget("s1c_mono")

# (d) N40-4's shape: a heap field WRITE of an unallocatable (`Table[int, _]`)
# value through a call-returned ref.
type S1cBadHeap = object
  t: Table[int, string]
  n: int

proc s1cMkBadHeap(): ref S1cBadHeap {.symexOpaque.} =
  discard

proc s1cMkBadTable(): Table[int, string] {.symexOpaque.} =
  discard

proc s1cHeapWriteBlock() =
  let p = s1cMkBadHeap()
  if p != nil:
    p.t = s1cMkBadTable()
    symexTarget("s1c_heap_write")

proc s1cOpaqueBadRet(x: int) =
  ## A walk-level call-return allocation (`freshRetSym`, the opaque arm) of
  ## an unallocatable type degrades in-band with no `lower()` around it. It
  ## does NOT leak: the parser A-normalises the call into a synthetic retName
  ## plus a `let` binding, and that `let`'s `lowerInExpr` drains the pending
  ## taint onto the same path one statement later -- pinned here, with
  ## nothing else lowering after it, so a future change to that shape shows.
  if x == 3:
    let t = s1cMkBadTable()
    symexTarget("s1c_bad_ret")

proc s1cHeapWriteFlat() =
  ## Branch-free twin for the concolic follow-concrete walk (which follows
  ## only the concretely-taken arm of an `if`).
  let p = s1cMkBadHeap()
  p.t = s1cMkBadTable()

type S1cScanError = object of CatchableError

proc s1cReadCStr(s: string, offset: int): (string, int) =
  ## `tsymex_r6_n36_raise_degrade`'s `readCStringOptN36`, verbatim shape.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(S1cScanError, "unterminated")

proc s1cRegionBlock(s: string) =
  ## N36-1's pair-loop-in-a-block shape: the two-hop literal-seeded counter
  ## lands BV-sorted, `iekStrInOptionRegion` declines, and the tainted path
  ## that still reaches the label carries that decline's residue in its pc.
  block:
    var localOffset = 0
    var i = localOffset
    var pairs: seq[(string, string)] = @[]
    while i < s.len:
      let (key, p1) = s1cReadCStr(s, i)
      if key.len == 0:
        break
      let (val, p2) = s1cReadCStr(s, p1)
      pairs.add((key, val))
      i = p2
  symexTarget("s1c_region_block")

suite "RFC-0005 S1c (a) -- isTargetLabel/routeRaise SOLVE a tainted path":

  test "a tainted path reaching the label is solved: its solver resource-out is recorded (beSolverUndef)":
    let r = symexFind(s1cTaintedRareLabel, tLabel("s1c_rare"), tightRLimit)
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(feOpaqueCallUnmodelled)
    check r.errors.hasKind(beSolverUndef)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a tainted raise at the SUT boundary is solved: its solver resource-out is recorded (beSolverUndef)":
    let r = symexFind(s1cTaintedRareRaise, tRaisedExn(), tightRLimit)
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(beSolverUndef)
    check not r.errors.hasKind(weInternalWalkerFault)

suite "RFC-0005 S1c (b) -- routeRaise routes a tainted raise instead of killing the path (§2.6)":

  test "the handler of a tainted raise is walked (its body's own decline is reached and recorded)":
    let r = symexFind(s1cTaintedCaught, tLabel("s1c_after_catch"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedStmtKind)
    check not r.errors.hasKind(weInternalWalkerFault)

suite "RFC-0005 S1c (c) -- witness monotonicity, tainted arm discovered first (§4.1 family 1)":

  test "a clean witness found AFTER a tainted SAT still wins -- the candidate never halts the walk":
    let r = symexFind(s1cTaintedFirst, tLabel("s1c_mono"))
    checkpoint($kindNames(r.errors))
    check r.status == sxSat
    check r.witness[0] == 42

suite "RFC-0005 S1c (d) -- the lowering pending-taint leak (S1b's N40-4 finding)":

  test "a heap field write of an unallocatable value drains its pending taint onto its path (no leak stamp)":
    let r = symexFind(s1cHeapWriteBlock, tLabel("s1c_heap_write"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seUnsupportedTableKeyType)
    check not r.errors.hasKind(weInternalWalkerFault)
    check loweringPendingTaint == {}

  test "a walk-level call-return allocation drains its pending taint onto its path (no leak stamp)":
    let r = symexFind(s1cOpaqueBadRet, tLabel("s1c_bad_ret"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seUnsupportedTableKeyType)
    check not r.errors.hasKind(weInternalWalkerFault)
    check loweringPendingTaint == {}

  test "a concolic collect ends its walk with no pending lowering taint left on the thread":
    let r = concolicCollect(s1cHeapWriteFlat, newSeq[ChoiceNode](),
                            newSeq[ConcolicParamBinding]())
    checkpoint("walkDegradeCount=" & $r.counters.walkDegradeCount)
    check loweringPendingTaint == {}

# ---- (e) the candidate pool, observed on the raw result (IR level) ----------
# `RawResult.candidates` is the pool S10's replay reads; `symexFind` does not
# surface it before S10, so these read it straight off `runSymex`. An
# `isUnsupported` node taints every path through it (its kind is `dcNoAnswer`
# under the all-⊤ default, so the path carries `scSpurious`).

let xVar = mkVar("x")
let xParam = @[IRParam(name: "x", ty: tInt(64, true))]
const allTop = {scSpurious, scIncomplete}

suite "RFC-0005 S1c (e) -- the candidate pool (w.candidates, RawResult.candidates)":

  test "a tainted label hit is solved INTO the candidate pool, not dropped, and the run stays sxUnknown":
    let prog = SymexProgram(params: xParam,
      body: mkBlock(@[mkUnsupported(feUnsupportedStmtKind, "s1c probe", 0),
                      mkTargetLabel("hit")]))
    let raw = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    check raw.status == sxUnknown
    check raw.candidates.len == 1
    check raw.candidates[0].status == sxSat
    check raw.candidates[0].pathTaint == allTop
    check raw.errors.hasKind(feUnsupportedStmtKind)
    check not raw.errors.hasKind(weInternalWalkerFault)

  test "tainted arm FIRST: its SAT is a candidate, the walk goes on, and the later clean SAT wins":
    let prog = SymexProgram(params: xParam,
      body: mkBlock(@[mkIf(@[
        mkBranch(mkBinop(bLt, xVar, mkIntLit(0)),
                 mkBlock(@[mkUnsupported(feUnsupportedStmtKind, "s1c probe", 0),
                           mkTargetLabel("hit")])),
        mkBranch(mkBinop(bEq, xVar, mkIntLit(42)), mkTargetLabel("hit"))])]))
    let raw = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    check raw.status == sxSat
    check raw.pathTaint == {}              ## the winner is the CLEAN arm
    check raw.candidates.len == 1          ## the tainted arm was solved first
    check raw.candidates[0].pathTaint == allTop

  test "a tainted SUT-boundary raise is solved into the candidate pool as an sxRaised":
    let prog = SymexProgram(params: xParam,
      body: mkBlock(@[mkUnsupported(feUnsupportedStmtKind, "s1c probe", 0),
                      mkRaise("ValueError", mkStrLit("s1c"))]))
    let raw = runSymex(prog, SymexTarget(kind: stkRaisedExn, typeFilter: ""))
    check raw.status == sxUnknown
    check raw.candidates.len == 1
    check raw.candidates[0].status == sxRaised
    check raw.candidates[0].pathTaint == allTop

  test "a clean run has an empty pool and keeps its verdict":
    let prog = SymexProgram(params: xParam,
      body: mkBlock(@[mkIf(@[mkBranch(mkBinop(bEq, xVar, mkIntLit(42)),
                                      mkTargetLabel("hit"))])]))
    let sat = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    check sat.status == sxSat
    check sat.candidates.len == 0
    let unsat = runSymex(prog, SymexTarget(kind: stkLabel, label: "nowhere"))
    check unsat.status == sxUnsat
    check unsat.candidates.len == 0

# ---- (f) the ordered procedure itself (§2.3), every rule ---------------------
# `decideVerdict` is pure, so each rule is driven with the exact `Taint` it
# names -- including a `{scSpurious}`-only run, which no kind produces until
# S4 reclassifies a funnel (that is the ONLY way to observe rule 4 as distinct
# from rule 5 today).

proc sat(t: Taint): RawResult = RawResult(status: sxSat, pathTaint: t)
proc raised(t: Taint): RawResult =
  RawResult(status: sxRaised, raisedTypeId: "ValueError", pathTaint: t)
const fresh = {scSpurious}   ## pathTaint(dcFreshSymbol) = runTaint(dcFreshSymbol)

suite "RFC-0005 S1c (f) -- decideVerdict: the ordered decision procedure":

  test "rule 1: a clean sxSat wins, in discovery order":
    let d = decideVerdict(@[sat({}), sat({})], @[], allTop, vetoed = false)
    check d.status == sxSat
    check d.winnerIdx == 0

  test "rules 1-2 order: a clean sxSat beats an EARLIER clean sxRaised":
    let d = decideVerdict(@[raised({}), sat({})], @[], {}, vetoed = false)
    check d.status == sxSat
    check d.winnerIdx == 1

  test "rule 2: a clean sxRaised wins when no clean sxSat exists":
    let d = decideVerdict(@[raised({})], @[], allTop, vetoed = false)
    check d.status == sxRaised
    check d.winnerIdx == 0

  test "rules 1-2 never accept an scSpurious finding, even one filed in `found`":
    let d = decideVerdict(@[sat(fresh), raised(allTop)], @[], {}, vetoed = false)
    check d.status == sxUnknown
    check d.winnerIdx == -1

  test "a candidate never shadows a clean winner found after it":
    let d = decideVerdict(@[sat({})], @[sat(fresh)], allTop, vetoed = false)
    check d.status == sxSat
    check d.winnerIdx == 0

  test "rule 4: a candidate blocks sxUnsat even on a run with NO scIncomplete":
    ## The false-sxUnsat guard: the enlarged program reaches the target, so a
    ## candidate that is not (yet) confirmed falls to sxUnknown, never sxUnsat.
    check decideVerdict(@[], @[sat(fresh)], fresh, vetoed = false).status == sxUnknown
    check decideVerdict(@[], @[raised(fresh)], fresh, vetoed = false).status == sxUnknown

  test "rule 5: nothing solved SAT and no scIncomplete -> sxUnsat (an over-taint-only run)":
    check decideVerdict(@[], @[], fresh, vetoed = false).status == sxUnsat
    check decideVerdict(@[], @[], {}, vetoed = false).status == sxUnsat

  test "rule 6: nothing solved SAT but scIncomplete in the run -> sxUnknown":
    check decideVerdict(@[], @[], {scIncomplete}, vetoed = false).status == sxUnknown
    check decideVerdict(@[], @[], allTop, vetoed = false).status == sxUnknown

  test "the blanket vetoes (until S9) suppress rules 1-2 and block rule 5":
    check decideVerdict(@[sat({})], @[], {}, vetoed = true).status == sxUnknown
    check decideVerdict(@[], @[], {}, vetoed = true).status == sxUnknown

  test "behaviour-preserving under all-⊤: runTaint ∈ {{}, ⊤} reproduces the pre-S1c rule":
    ## Pre-S1c: winner if any finding and no veto; else sxUnknown iff
    ## runTaint != {} or a veto; else sxUnsat.
    for rt in [Taint({}), allTop]:
      for vetoed in [false, true]:
        let expected = if vetoed or rt != {}: sxUnknown else: sxUnsat
        check decideVerdict(@[], @[], rt, vetoed).status == expected

suite "RFC-0005 S1c (g) -- a tainted path's solve is bounded (never a new non-termination)":

  test "taintedSolveRLimit: finite under default settings; an explicit caller budget wins":
    check taintedSolveRLimit(defaultSymexSettings()) == defaultConcreteBranchRLimit
    check taintedSolveRLimit(defaultSymexSettings()) > 0'u
    var s = defaultSymexSettings()
    s.budget.queryRLimit = 1234'u
    check taintedSolveRLimit(s) == 1234'u

  test "the N36 region-decline shape terminates under DEFAULT settings, honestly sxUnknown":
    ## Pre-bound: `check` on the tainted path's pc never returned (the whole
    ## file hung under dt-bounded; `tsymex_r6_n36_raise_degrade` 0 -> 137 in
    ## the sweep). Post-bound: the tainted solves finish (sat, unsat or a
    ## bounded `beSolverUndef`) and the verdict is the pre-S1c sxUnknown.
    let r = symexFind(s1cRegionBlock, tLabel("s1c_region_block"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(seUnsupportedStringOp)
    check not r.errors.hasKind(weInternalWalkerFault)

suite "RFC-0005 S1c -- walker version pin":

  test "walker version floor >= 141 (S1c: tainted paths are solved; candidate pool; ordered verdict)":
    check parseInt(symexWalkerVersion) >= 141
