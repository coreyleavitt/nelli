## RFC-0016 int6 D1d. A pruning check a kept model already satisfies is not
## searched.
##
## int6 D1b charged each own-context solver its fixed cost
## (`walkerContextUnits`): a fresh Z3 context, the default solver's set-up and
## the check's own passes, about 6.5 ms whatever the query. That cost cannot
## be shared away: the context is fresh so that a search is a function of its
## query alone (RFC-0005 S8bm), and a reused context keeps the ids of freed
## terms and the plugins' caches, the history S8bm removed. What can go is
## the search itself. A pruning check (`loopArmInfeasible`, `pathInfeasible`,
## `decideUndefined`, ..) acts only on UNSAT, and at a fork the parent's model
## satisfies one arm: `refuteStatus` evaluates the query's new roots in the
## models it kept (`satByModel`) and answers SAT without a search when one
## fits. Measured on c, podman (int6 D1d, 2026-11-19), the `filterIt` over a
## `seq[seq[int]]` below (`tsymex_0016_k9cg_unbacked_p`'s FilterIt shape):
##   unroll 3:   426 solvers,  14.0M units charged  ->  270 solvers,  8.30M
##   unroll 4: 3,906 solvers, 141.4M units charged  ->  2,417 solvers, 86.0M
## (1,489 of 3,125 pruning checks decided by a kept model at unroll 4).
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc filterNested(o0: seq[seq[int]]; k: int) =
  var o = o0
  let m = o.filterIt(it.len > 0)
  if m.len >= 0: symexTarget("hit")

proc mkUnwind4(limit: uint): SymexSettings =
  result = pinSettingsConst
  result.budget.maxLoopUnwind = 4
  result.budget.walkRLimit = limit

## 120M units: under what unroll 4 was charged when every pruning check was
## searched (43.8M Z3 units and term visits + 3,906 solvers * 25,000 =
## 141.4M), over what it is charged now (86.0M, with `walkerContextUnits`
## re-measured at 20,000), with room on both sides.
const within = mkUnwind4(120_000_000)

suite "int6 D1d: a pruning check a kept model satisfies is not searched":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 472

  test "unroll 4 of a forking loop is decided within the budget":
    # pinFind: the same call, with the sxSat reproduced on this build
    let r = pinFind(filterNested, tLabel("hit"), within)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check r.trusted
    check not r.errors.named(beBudgetExhaustedPrune)
