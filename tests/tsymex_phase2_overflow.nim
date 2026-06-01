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
import std/unittest
import proptest/symex

proc wrapNeeded(x: int8) =
  if x + 1 < x:
    symexTarget("wrap-needed")

suite "symex Phase 2 — ADR-0001 soundness validation":
  test "isExact finds the BV-only witness":
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"))
    check r.status == sxSat
    check r.witness[0] == 127

  test "isOptimised agrees with isExact (no range info → no promotion)":
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), optimisedSymexSettings())
    check r.status == sxSat
    check r.witness[0] == 127
    check r.abstractions.len == 0

  test "isLoose misses the overflow-only path (false negative)":
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), looseSymexSettings())
    check r.status == sxUnsat   ## ← UNSOUND: Int says x+1 > x always
