## Phase 2 — ADR-0001 end-to-end soundness validation.
##
## The SUT `wrapNeeded` has a path reachable only via integer wrap
## (`x + 1 < x` is BV-SAT exactly when `x = int8.high`; Int-UNSAT).
## The three integer-semantics modes are tested:
##
##   * `isExact`     — BV[W] always. Sound. Finds witness x = 127.
##   * `isOptimised` — same answer here (no range info, no abstraction).
##   * `isLoose`     — Z3Int everywhere. Unsound. Reports `sxUnsat`
##                     because the Int solver thinks x+1 > x always.
##                     This is the **false negative** ADR-0001 warns
##                     about: real overflow bugs go undetected.
##
## R16-4 / ADR-0012 NOTE: under the default arithChecks=all-on settings,
## x+1 at x=127 (int8.high) now RAISES OverflowDefect instead of wrapping
## silently. The BV wrap-soundness demonstration therefore uses `arithChecks={}`
## explicitly — a deliberate test-regime choice to observe silent-wrap SEMANTICS.
## The default-regime behaviour (the wrap raises) is pinned by the final test.
import std/unittest
import nelli/symex

proc wrapNeeded(x: int8) =
  if x + 1 < x:
    symexTarget("wrap-needed")

## Settings helpers — pure procs so they evaluate as `static SymexSettings`
## at the `symexFind` macro boundary (R16-4 / ADR-0012 reconciliation).
proc exactNoOverflowSettings(): SymexSettings =
  ## isExact BV mode, arithChecks off: observe silent int8 wrap semantics.
  result = defaultSymexSettings()
  result.integerSemantics = isExact
  result.arithChecks = {}

proc optimisedNoOverflowSettings(): SymexSettings =
  ## isOptimised (no range info → stays BV), arithChecks off: same wrap regime.
  result = optimisedSymexSettings()
  result.arithChecks = {}

proc looseNoOverflowSettings(): SymexSettings =
  ## isLoose (Z3Int), arithChecks off: Z3Int still says x+1 > x — false negative.
  result = looseSymexSettings()
  result.arithChecks = {}

suite "symex Phase 2 — ADR-0001 soundness validation":
  test "isExact finds the BV-only witness":
    ## arithChecks={}: run in overflow-off regime to observe the silent int8
    ## wrap that is the whole point of this test (R16-4 / ADR-0012 reconciliation).
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), exactNoOverflowSettings())
    check r.status == sxSat
    check r.witness[0] == 127

  test "isOptimised agrees with isExact (no range info → no promotion)":
    ## arithChecks={}: same overflow-off regime for BV wrap-soundness consistency.
    ## No range info on int8 → no abstraction → stays BV → same result.
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), optimisedNoOverflowSettings())
    check r.status == sxSat
    check r.witness[0] == 127
    check r.abstractions.len == 0

  test "isLoose misses the overflow-only path (false negative)":
    ## arithChecks={}: overflow-off regime for consistency; Z3Int still says
    ## x+1 > x always — the documented false negative is preserved.
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), looseNoOverflowSettings())
    check r.status == sxUnsat   ## ← UNSOUND: Int says x+1 > x always

  test "overflow-on default: the wrap now RAISES (R16-4)":
    ## Under default arithChecks=all-on, x+1 at x=127 raises OverflowDefect
    ## instead of wrapping silently. ADR-0012 target-aware shouldStop + unified
    ## verdict reduction means the sxRaised(OverflowDefect) is the headline;
    ## the label is not reachable without the wrap, so no sxSat is found.
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
    check r.raisedWitness[0] == 127
