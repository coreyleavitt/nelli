## Phase 15 code-review CR-21: `isCall` arg-lowering never drains parseIntRaiseConds.
##
## The `isCall` arm in the walker lowered actual arguments in a loop, but after the
## loop never called `drainParseIntRaises`. This meant that if any argument
## expression contained a `parseInt(s)` call:
##
##   * The raise predicates accumulated in `w.parseIntRaiseConds` during the arg
##     loop were DROPPED (never forked into ValueError raise paths).
##   * The caller-dispatch proceeded as if parseInt always succeeded.
##   * For non-digit inputs, a spurious non-raise path survived (false-safe).
##
## In addition, the threadvar `parseIntRaiseConds` was not reset to `@[]` before
## the arg loop (only `w.parseIntRaiseConds` was reset), so stale conditions from
## a prior statement could bleed into the arg loop's drain.
##
## FIX (CR-21):
##   1. Add `parseIntRaiseConds = @[]` alongside `w.parseIntRaiseConds = @[]` at
##      the top of the per-path arg-lowering block (line ~5194).
##   2. After `drainPendingLowerEffects(p)`, call `drainParseIntRaises(pd, w)` and
##      wrap the callee dispatch in a `for p in drainParseIntRaises(pd, w):` loop.
##
## Verdict change: `parseInt(s)` in an argument position now correctly surfaces
## sxRaised(ValueError) when `s` is non-digit. Stale cache entries (version "16")
## would have silently proceeded past the raise. Version bump to "17" required.
##
## DoD:
##   1. foo(parseInt(s)) where s == "abc" (definitely non-digit) → sxRaised(ValueError).
##      RED before fix: sxUnsat or sxSat for unreachable body (parseInt raise dropped).
##   2. foo(parseInt(s)) where s == "42" (digits) → sxSat reaching the target.
##      Must not regress: the digits-continuation still flows through to the callee.
##   3. Two-arg call with parseInt in second arg also surfaces the raise.
##      Verifies the drain covers ALL args, not just the first.

import std/[unittest, strutils]
import nelli/symex

# --- helper proc called with a parsed argument ---
proc addOne(n: int): int = n + 1

proc calleeReachable(n: int) =
  symexTarget("hit")

# --- SUT 1: foo(parseInt(s)) — non-digit input must raise ValueError in arg position ---
proc callWithParseIntArg(s: string) =
  if s == "abc":
    calleeReachable(parseInt(s))   ## parseInt("abc") should raise ValueError

# --- SUT 2: foo(parseInt(s)) — digit input, callee must be reachable ---
proc callWithParseIntArgDigits(s: string) =
  if s == "42":
    calleeReachable(parseInt(s))   ## parseInt("42") = 42, callee reachable

# --- SUT 3: two-arg call, parseInt in the second arg ---
proc twoArgHelper(a: int, b: int): int = a + b

proc callTwoArgParseInt(s: string) =
  if s == "abc":
    let r = twoArgHelper(1, parseInt(s))
    if r > 0:
      symexTarget("unreached")

suite "Phase 15 CR-21 — isCall arg-lowering drains parseIntRaiseConds":

  test "CR-21: parseInt in arg position, non-digit → sxRaised(ValueError)":
    ## Before fix: sxUnsat (parseInt raise dropped; callee unreachable because
    ## s=="abc" is non-digit so calleeReachable is never hit, but the RAISE is
    ## what should be found here). After fix: sxRaised(ValueError).
    let r = symexFind(callWithParseIntArg, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"

  test "CR-21: parseInt in arg position, digit string → callee reachable (sxSat)":
    ## The digits-continuation still flows through to the callee.
    ## Must not regress after the drain is added.
    let r = symexFind(callWithParseIntArgDigits, tLabel("hit"))
    check r.status == sxSat

  test "CR-21: parseInt in second arg of two-arg call → sxRaised(ValueError)":
    ## Verifies the drain covers ALL args, not just the first.
    ## twoArgHelper(1, parseInt("abc")) must raise ValueError.
    ## Before fix: AssertionDefect crash (binBV width mismatch) or sxUnsat.
    ## After fix: sxRaised(ValueError).
    let r = symexFind(callTwoArgParseInt, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
