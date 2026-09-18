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

import std/[unittest, strutils]
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

# Slice 3. Reachable ONLY if `a * b` wraps: the true product is 1.6e19,
# which as an int64 wraps to roughly -2.4e18. Under CHECKED semantics the
# multiplication raises before the comparison, so the label is unreachable;
# under UNCHECKED semantics the wrap is a defined result and it is reachable.
# The two integer modes must agree on which -- that agreement IS ADR-0001.
proc wrapProbe(a, b: range[0'i64..4_000_000_000'i64]) =
  if a * b < 0:
    symexTarget("wrapped")

const Unchecked = SymexSettings(integerSemantics: isOptimised,
                                arithChecks: {acDivByZero, acRange})
const UncheckedExact = SymexSettings(integerSemantics: isExact,
                                     arithChecks: {acDivByZero, acRange})
const Exact = SymexSettings(integerSemantics: isExact)

# Slice 4. The obligation is about the OPERATION, not about multiplication:
# addition and subtraction carry it too, in both directions.
proc addOvf(a, b: range[0'i64..9_000_000_000_000_000_000'i64]) =
  let c = a + b            # reaches 1.8e19 -- past int64.high
  symexTarget("t")
  discard c

proc subUnd(a: range[-9_000_000_000_000_000_000'i64 .. 0'i64],
            b: range[0'i64..9_000_000_000_000_000_000'i64]) =
  let c = a - b            # reaches -1.8e19 -- past int64.low
  symexTarget("t")
  discard c

# Slice 4. The propagation pin. `s` is a LOCAL, and its own computation is
# provably safe (8e9 fits int64), so the only thing that can keep `s * s`
# checkable is `arithInt` carrying `a`/`b`'s width onto `s`. Without that
# propagation `s` looks width-less and the outer multiply forks nothing.
proc chainedOvf(a, b: range[0'i64..4_000_000_000'i64]) =
  let s = a + b            # <= 8e9, safe
  let c = s * s            # <= 6.4e19, NOT safe
  symexTarget("t")
  discard c

# Slice 4. Over-ban guard: a param used only in comparisons has no
# obligation at all and must still promote.
proc cmpOnly(a, b: range[0'i64..1000'i64]) =
  if a < b:
    symexTarget("t")

# Slice 4. Nim wraps UNSIGNED overflow silently -- no OverflowDefect. The
# `ziSigned`/`signed` guards exist so the walker does not invent one.
proc uAdd(a, b: uint8) =
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

  test "under unchecked arithmetic the two integer modes still agree":
    ## Slice 3, and the load-bearing property for it. `isExact` is the
    ## oracle: BV arithmetic wraps because that is what bit-vectors DO.
    ## `isOptimised` answered sxUnsat here — it suppressed the raise fork
    ## (correct) while still modelling the product as an unbounded Int
    ## that never wraps (not correct), and so lost the path.
    let oracle = symexFind(wrapProbe, tLabel("wrapped"), UncheckedExact)
    let opt = symexFind(wrapProbe, tLabel("wrapped"), Unchecked)
    check oracle.status == sxSat
    check opt.status == oracle.status

  test "unchecked arithmetic raises no OverflowDefect":
    ## The other half of the same setting: with `acOverflow` off there is
    ## no defect to find, because overflow is defined behaviour.
    let r = symexFind(wrapProbe, tRaisedExn("OverflowDefect"), Unchecked)
    check r.status != sxRaised

  test "the unchecked ban does not leak into checked runs":
    ## Non-regression for slices 1-2: the wrap scan is gated on the
    ## setting, so a default (checked) run still promotes and still finds
    ## the defect.
    let r = symexFind(mul64, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    let safe = symexFind(addSafe, tLabel("t"))
    check safe.abstractions.len == 2

  test "addition overflow is found on a promoted param":
    let r = symexFind(addOvf, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised

  test "subtraction underflow is found on a promoted param":
    let r = symexFind(subUnd, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised

  test "the obligation survives a safe intermediate local":
    ## Pins `arithInt`'s width propagation. `s = a + b` is provably safe;
    ## `s * s` is not. If the width stopped at `s`, this would be sxUnsat.
    let r = symexFind(chainedOvf, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised

  test "a comparison-only param is not banned from promotion":
    let r = symexFind(cmpOnly, tLabel("t"))
    check r.status == sxSat
    check r.abstractions.len == 2
    check r.obligations.len == 0    ## no arithmetic, so no obligation

  test "unsigned arithmetic raises nothing — Nim wraps it silently":
    let r = symexFind(uAdd, tRaisedExn("OverflowDefect"))
    check r.status != sxRaised

  test "isExact is untouched by any of this":
    let r = symexFind(mul64, tRaisedExn("OverflowDefect"), Exact)
    check r.status == sxRaised
    let l = symexFind(mul64, tLabel("t"), Exact)
    check l.abstractions.len == 0   ## isExact never promotes

  test "version floor — this file needs walker 128":
    ## Per CLAUDE.md: a walker SEMANTICS change bumps `symexWalkerVersion`
    ## and the round's test file pins the floor. 125 answered `sxUnsat` for
    ## slice 1's fix; slice 2 (127) is what makes `r.obligations` an
    ## observable at all ("a provably-safe site discharges its obligation
    ## statically" above); slice 3 (128) is what makes the two integer modes
    ## agree under unchecked arithmetic ("under unchecked arithmetic the two
    ## integer modes still agree" above). 126 alone is not enough for this
    ## file's own tests to make sense.
    ##
    ## Compared numerically, not lexicographically: `symexWalkerVersion` is a
    ## string, and string comparison goes wrong once versions reach four
    ## digits (`"1000" < "128"`).
    check parseInt(symexWalkerVersion) >= 128
