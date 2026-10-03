## RFC-0005 (soundness channels) slice S8bp -- no walker search depends on
## what the walk, or an earlier walk, left in Z3's context.
##
## Pinned here (the RFC's "As landed (S8bp)" note has the mechanism and
## the measurements):
##   (1) every `checkCapped` step searches in a context of its own, so no
##       step's cost moves with what the walk's context already holds:
##       thirty unrelated constants made before each query (S8bm's probe)
##       leave every step's answer and units as they were. S8bm isolated
##       step 1; the theory-free steps moved too (a factoring search in
##       them is not small), as did (2), (3) and a query with no string;
##   (2) the per-thread kind probes (`seqCapKinds`, `byteDomainKinds`,
##       `intDivDeclKinds`, `heapChainKinds`, `theoryFreeSimple`'s check)
##       build their terms in a context of their own, so a thread's first
##       walk searches as its second does.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8bp_isolation needs -d:symexQueryStats (its .nim.cfg)".}

proc lastNl(s, t: string; x, y: int) =
  ## A `rfind` query refuted only by the cap (step 1 UNSAT), so step 3
  ## decides it, with a factoring search in every step.
  if t.len > 10 and s.rfind("bc") == 1 and x > 1 and y > 1 and x < 2000 and
     y < 2000 and x * y == 1022117:
    symexTarget("s8bp_lastnl")

proc preSufNl(s: string; x, y: int) =
  ## UNSAT on its own (`"ab" & ..` cannot end in `"ba"` at length 2), so
  ## every step up to step 2's core runs, each with a factoring search.
  if x > 1 and y > 1 and x < 2000 and y < 2000 and x * y == 1022117 and
     s.startsWith("ab") and s.endsWith("ba") and s.len == 2:
    symexTarget("s8bp_presuf")

proc plainNl(x, y: int) =
  ## No string: the `plain` query.
  if x > 1 and y > 1 and x < 2000 and y < 2000 and x * y == 1022117:
    symexTarget("s8bp_plain")

const smallCap = SymexSettings(budget: ResourceBudget(maxSeqLen: 8))

proc steps(): seq[string] =
  ## `symexStepStats` as `step/status=units`.
  for s in symexStepStats: result.add s.step & "/" & s.status & "=" & $s.units

proc symexStepStatsNames(steps: seq[string]): seq[string] =
  for x in steps: result.add x.split('/')[0]

var walks: array[2, tuple[status: SymexStatusKind, steps: seq[string]]]

proc twoWalks() {.thread.} =
  ## `lastNl`'s walk, twice, on a fresh thread: the first is the thread's
  ## first walk, the one its per-thread probes run in.
  {.cast(gcsafe).}:
    for w in 0 .. 1:
      symexStepStats = @[]
      let r = symexFind(lastNl, tLabel("s8bp_lastnl"), smallCap)
      walks[w] = (r.status, steps())
    symexStepStats = @[]

template perturbed(sut: untyped; lbl: string; settings: SymexSettings;
                   n: int): tuple[status: SymexStatusKind,
                                  steps: seq[string]] =
  ## `sut`'s walk, recorded, with `n` unrelated constants made in the
  ## walk's context before each query (`symexPerturbConsts`).
  symexStepStats = @[]
  symexPerturbConsts = n
  let r = symexFind(sut, tLabel(lbl), settings)
  symexPerturbConsts = 0
  let recorded = steps()
  symexStepStats = @[]
  (r.status, recorded)

suite "S8bp (1): no step's search moves with unrelated walk state":

  var seen: HashSet[string]

  template same(sut: untyped; lbl: string; settings: SymexSettings;
                want: SymexStatusKind) =
    let a = perturbed(sut, lbl, settings, 0)
    let b = perturbed(sut, lbl, settings, 30)
    checkpoint "as is:     " & a.steps.join(" ")
    checkpoint "perturbed: " & b.steps.join(" ")
    check a.status == want and b.status == want
    check a.steps.len > 0
    # Every step of every query: the same answer, the same units.
    check a.steps == b.steps
    for x in symexStepStatsNames(a.steps): seen.incl x

  test "the facts-first check, steps 1, 1b, 1c and 2":
    ## Before S8bp (Z3 5.1): step 1c 114,891 against 350,726 units, step
    ## 2 401,123 against 231,590 (4.13.4: 238,219 against 327,223).
    same(preSufNl, "s8bp_presuf", defaultSymexSettings(), sxUnsat)

  test "step 3":
    ## Before S8bp: 207,893 against 464,636 units (4.13.4).
    same(lastNl, "s8bp_lastnl", smallCap, sxSat)

  test "a query with no string":
    ## Before S8bp: 124,550 against 92,799 units (Z3 5.1), 74,780 against
    ## 94,956 (4.13.4).
    same(plainNl, "s8bp_plain", defaultSymexSettings(), sxSat)

  test "a walk's spend is exactly its steps' units":
    ## Every step's units are counted once: in its query's `rlimitDelta`
    ## and in what a target hit spent (`symexTargetSolveStats.units`, by
    ## which `solveTargetHit` classifies a budget-out and a slow SAT).
    symexQueryStats = @[]
    symexStepStats = @[]
    symexTargetSolveStats = (budgetOut: 0, declined: 0, slowSat: 0, units: 0)
    let r = symexFind(lastNl, tLabel("s8bp_lastnl"), smallCap)
    check r.status == sxSat
    var stepUnits, queryUnits = 0
    for x in symexStepStats: stepUnits += x.units
    for q in symexQueryStats: queryUnits += q.rlimitDelta
    checkpoint "steps " & $stepUnits & ", queries " & $queryUnits &
      ", hit " & $symexTargetSolveStats.units
    check stepUnits > 0
    check queryUnits == stepUnits
    # Each of the walk's queries is a target hit's solve (an `rfind` index
    # split reaches the target twice, one hit UNSAT).
    check symexQueryStats.len == 2
    check symexTargetSolveStats.units == queryUnits
    symexQueryStats = @[]
    symexStepStats = @[]

  test "the three walks reached every step":
    check seen == toHashSet(["plain", "factsFirst", "1", "1b", "1c",
                             "1c-capped", "2", "3"])

suite "S8bp (2): a thread's first walk searches as its second does":

  test "the same SUT, walked twice on a fresh thread, costs the same":
    var th: Thread[void]
    createThread(th, twoWalks)
    joinThread(th)
    checkpoint "first:  " & walks[0].steps.join(" ")
    checkpoint "second: " & walks[1].steps.join(" ")
    check walks[0].status == sxSat and walks[1].status == sxSat
    check walks[0].steps.len > 0
    # Every step of every query: the same answer, the same units. Before
    # S8bp (Z3 5.1) the step-3 search of the target query took 482,126
    # units in the first walk and 85,882 in a later one.
    check walks[0].steps == walks[1].steps

suite "S8bp: walker version floor":

  test "symexWalkerVersion >= 219":
    check parseInt(symexWalkerVersion) >= 219
