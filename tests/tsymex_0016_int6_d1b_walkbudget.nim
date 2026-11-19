## RFC-0016 int6 D1b. `walkRLimit` bounds what a walk of many cheap queries
## costs, so a clean loop whose unrolled paths multiply ends on the budget.
##
## The budget charges Z3's step count and the walker's term visits
## (`walkerTermUnits`), each sized so a unit costs about 0.254 us of wall
## (RFC-0016 K7's calibration). Neither counted the fixed cost of one query:
## the fresh Z3 context each check runs in (`ownContextSolver`), the solver it
## builds, the check's own overhead and the context's teardown. A walk of
## large queries hides it; a k-unroll of small ones is made of it. The
## `filterIt` over a `seq[seq[int]]` parameter below (the
## `tsymex_0016_k9cg_unbacked_p` FilterIt probe's shape) forks every path
## every iteration, about 12x the queries per unroll step, each a ~1.5k-unit
## plain check of ~430 term visits. Measured on c, podman (int6 D1b,
## 2026-11-19), walk time only:
##   unroll 3:   426 queries,  3,389,554 units charged, 3.0-3.6 s
##   unroll 4: 3,906 queries, 43,770,718 units charged, 42-57 s
## so about 1M units a second against the calibrated 3.9M, and the default
## budget (1G units) was about 1,000 s of this shape: the unroll-5 walk ran
## to the 600 s stall backstop instead. The 0.254 us rate puts unroll 3's
## 3.0 s at about 12M units; the query charge (`walkerContextUnits`, 25,000
## per own-context solver) charges it 3.4M + 426 * 25,000 = 14.0M.
##
## RFC-0016 int6 D1d: a pruning check a kept model satisfies is no longer
## searched (`refuteStatus`) and the charge is re-measured at 20,000, so
## unroll 3 is 270 solvers, 170,863 visits and 338,515 Z3 units: 338,515 +
## 170,863 * 15 + 270 * 20,000 = 8.30M, still twice the cut below.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc filterNested(o0: seq[seq[int]]; k: int) =
  ## A clean loop: every path through `filterIt` is modelled, and the label
  ## after it is reached only once the k-unroll has built each path.
  var o = o0
  let m = o.filterIt(it.len > 0)
  if m.len >= 0: symexTarget("hit")

proc mkUnwind3(limit: uint): SymexSettings =
  result = pinSettingsConst
  result.budget.maxLoopUnwind = 3
  result.budget.walkRLimit = limit

## 4M units: about 1 s at the calibrated rate, a third of what unroll 3
## costs in wall. Before the query charge the walk was charged 3.39M and
## ended in a trusted `sxSat` under it; charged for its 426 contexts it is
## 14.0M, so a limit between the two (here 4M, with room on both sides)
## ends it on the budget. Since D1d: 2.90M without its 270 contexts, 8.30M
## with them.
const cut = mkUnwind3(4_000_000)
## The default budget: the same walk's answer stands.
const whole = mkUnwind3(defaultSymexSettings().budget.walkRLimit)

suite "int6 D1b: the walk budget charges each query's fixed cost":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 464

  test "a clean exploding loop ends on the budget, classified":
    let r = symexFind(filterNested, tLabel("hit"), cut)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check not r.trusted
    check r.errors.named(beBudgetExhaustedPrune)
    check r.errors.anyIt(it.kind == beBudgetExhaustedPrune and
                         "walk work cap" in it.msg)
    pinCap(filterNested, "ckWalkWork", tLabel("hit"), cut)

  test "within the budget the answer is unchanged":
    let r = symexFind(filterNested, tLabel("hit"), whole)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check r.trusted
