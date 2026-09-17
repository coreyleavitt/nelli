## Issue #161 — promotion must not delete the OverflowDefect obligation.
##
## ADR-0001 amendment (accepted 2026-09-17): the FLOOR is the proof
## obligation, not the representation. A value may be Int-sorted only if
## every operation on it is proven non-overflowing; every promotion must
## either DISCHARGE that obligation statically or KEEP IT LIVE dynamically
## (by carrying its width so `overflowCondInt` fires). Either is sound. The
## forbidden third state -- obligation neither discharged nor kept -- is the
## bug this file pins.
##
## Before the fix, `promoteSound` params were allocated `svInt` with
## `ziWidth: 0`, so `lowerArith` pushed no `overflowCondInt` and the defect
## path silently vanished. `isExact` answered correctly, which is what made
## it a promotion bug rather than an overflow-machinery bug.

import std/unittest
import nelli/symex
import nelli/smt/canonicalize

# #161's repro, verbatim. a*b reaches 1.6e19, which does not fit int64.
# Runtime truth: mul64(4_000_000_000, 4_000_000_000) raises OverflowDefect
# under default checks -- and under -d:release, which keeps them on.
proc mul64(a, b: range[0'i64..4_000_000_000'i64]) =
  let c = a * b
  symexTarget("t")
  discard c

suite "#161 — promotion keeps the overflow obligation live":

  test "isOptimised finds the reachable OverflowDefect in a*b":
    ## The load-bearing property. Was sxUnsat (false negative) at a1ebeb1.
    let r = symexFind(mul64, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "version floor — this behaviour arrived at walker 126":
    ## Per CLAUDE.md: a walker SEMANTICS change bumps `symexWalkerVersion`
    ## and the round's test file pins the floor. 125 answered `sxUnsat`
    ## here; anything below 126 cannot have this fix.
    check symexWalkerVersion >= "126"
