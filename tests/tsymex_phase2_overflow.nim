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
## R16-4 / ADR-0012 NOTE: on this checks-on build x+1 at x=127 (int8.high)
## RAISES OverflowDefect instead of wrapping silently. The BV
## wrap-soundness demonstration therefore uses the unsigned twin, whose wrap
## is defined. (The explicit `arithChecks={}` regime that once observed the
## signed silent wrap went with the setting in RFC-0016 K10d; the build decides.)
## The checks-on behaviour (the signed wrap raises) is pinned by the final test.
import std/unittest
import nelli/symex
import ./s8cu_helpers

proc wrapNeeded(x: int8) =
  if x + 1 < x:
    symexTarget("wrap-needed")

## RFC-0016 W1-d2: signed wrap with checks off is undefined, so the BV/Int
## wrap-soundness demonstration (rule b: the property is the three integer
## modes' model of a DEFINED wrap) runs on the unsigned twin, under settings
## that agree with the build. The signed twin is pinned as untrusted below.
proc wrapNeededU(x: uint8) =
  if x + 1'u8 < x:
    symexTarget("wrap-needed")

## Settings helpers — pure procs so they evaluate as `static SymexSettings`
## at the `symexFind` macro boundary (R16-4 / ADR-0012 reconciliation).
proc exactSettings(): SymexSettings =
  ## isExact, the build's checks.
  result = defaultSymexSettings()
  result.integerSemantics = isExact

proc optimisedAgreeSettings(): SymexSettings =
  result = optimisedSymexSettings()

proc looseAgreeSettings(): SymexSettings =
  result = looseSymexSettingsPreset

suite "symex Phase 2 — ADR-0001 soundness validation":
  test "isExact finds the BV-only witness":
    ## Rule (b), unsigned twin: x + 1 < x holds exactly at uint8.high (255).
    let r = symexFind(wrapNeededU, tLabel("wrap-needed"), exactSettings())
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 255

  test "isOptimised agrees with isExact (no range info → no promotion)":
    ## Rule (b): no range info on uint8 → no abstraction → stays BV → same result.
    let r = symexFind(wrapNeededU, tLabel("wrap-needed"), optimisedAgreeSettings())
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 255
    check r.abstractions.len == 0

  test "isLoose misses the overflow-only path (false negative)":
    ## Rule (b): Z3Int still says x+1 > x always -- the documented false
    ## negative is preserved.
    let r = symexFind(wrapNeededU, tLabel("wrap-needed"), looseAgreeSettings())
    check r.status == sxUnsat   ## ← UNSOUND: Int says x+1 > x always

  test "overflow-on default: the wrap now RAISES (R16-4)":
    ## On a checks-on build, x+1 at x=127 raises OverflowDefect
    ## instead of wrapping silently. ADR-0012 target-aware shouldStop + unified
    ## verdict reduction means the sxRaised(OverflowDefect) is the headline;
    ## the label is not reachable without the wrap, so no sxSat is found.
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"))
    check r.status == sxRaised
    check r.raisedTypeId == "OverflowDefect"
    check r.raisedWitness[0] == 127
