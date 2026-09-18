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

# Slice 2's control. a+b reaches 2000, which fits int64 with room to spare,
# so the obligation is DISCHARGEABLE statically -- no fork need ever be built.
proc addSafe(a, b: range[0'i64..1000'i64]) =
  let c = a + b
  symexTarget("t")
  discard c

suite "#161 — promotion keeps the overflow obligation live":

  test "isOptimised finds the reachable OverflowDefect in a*b":
    ## The load-bearing property. Was sxUnsat (false negative) at a1ebeb1.
    let r = symexFind(mul64, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"

  test "a provably-safe site discharges its obligation statically":
    ## Slice 2. `a + b` over [0..1000] can reach at most 2000; interval
    ## arithmetic proves that in-window, so the obligation is discharged
    ## at lowering time and NO fork is handed to Z3. Same verdict as
    ## before, reached without the solver — which is the whole point.
    let r = symexFind(addSafe, tLabel("t"))
    check r.status == sxSat
    check r.obligations.len >= 1
    for o in r.obligations:
      check o.disposition == odDischargedStatic

  test "an unprovable site keeps its obligation live":
    ## The complement. `a * b` over [0..4e9] reaches 1.6e19 — outside
    ## int64 — so nothing is proven and the fork must survive to Z3.
    ## Note the analysis's OWN arithmetic overflows int64 here: the
    ## abstract domain has to answer "unknown" rather than raise.
    let r = symexFind(mul64, tLabel("t"))
    check r.status == sxSat
    check r.obligations.len >= 1
    var anyLive = false
    for o in r.obligations:
      if o.disposition == odLive: anyLive = true
    check anyLive

  test "version floor — this behaviour arrived at walker 126":
    ## Per CLAUDE.md: a walker SEMANTICS change bumps `symexWalkerVersion`
    ## and the round's test file pins the floor. 125 answered `sxUnsat`
    ## here; anything below 126 cannot have this fix.
    check symexWalkerVersion >= "126"
