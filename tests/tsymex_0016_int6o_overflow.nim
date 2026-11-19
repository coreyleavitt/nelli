## RFC-0016 int6-o: `overflowChecks` belongs to the code region it was
## compiled under, as the range, bound, field and object checks do
## (`tsymex_0016_int6p2_checkscope`). This file builds with Nim's default
## checks; `tsymex_0016_int6o_overflow_fwrapv` is its `-d:nelliFwrapv` twin.
##
## Native, probed on the pinned toolchain (c and cpp identical, x86-64 Linux):
##   * a routine declared under `{.push overflowChecks: off.}` (or `checks:
##     off`) runs the plain C operation: `high(int) + 1` is signed overflow,
##     undefined in C (gcc folds `v + 1 > v` to true; `id(high(int)) + 1`
##     computes `low(int)`), so the walker halts that side
##     (`ubSignedOverflow`), as in a `--overflowChecks:off` build
##     (`tsymex_0016_checksoff`); an `int8` sum is computed in C's `int` and
##     narrowed, a defined wrap: `127'i8 + 1` is `-128`;
##   * a callee declared outside the push keeps its own checks when called
##     from inside it (`OverflowDefect`), and one declared under it keeps the
##     push when called from checked code (no `OverflowDefect`);
##   * the checked caller's own arithmetic after such a call still raises:
##     `offNarrow(127) - 1` is `OverflowDefect`;
##   * system's integer `*=` is an `inline` routine compiled under the build's
##     options, so inside the push `x *= 2` at `high(int)` (and at `100'i8`)
##     still raises `OverflowDefect`; `+=` is the `Inc` magic, expanded under
##     the caller's options, and wraps (`low(int)`);
##   * a push inside a routine body leaves it unchecked at some positions only
##     (`innerOff(high(int))` is `-1`, no raise): neither setting, so it
##     declines `feCheckOption` (it was walked checked).
## Each was a whole-routine `feOverflowCheckOption` decline before (but the
## last, walked checked).

import std/[unittest, strutils]
import nelli/smt/arith_regime
import nelli
import nelli/symex
import ./s8cu_helpers

proc id(x: int): int {.noinline.} = x

proc checkedAdd(v: int): int = v + 1

{.push overflowChecks: off.}
proc sutAddCmp(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")

proc sutNarrow(v: int8) =
  if v > 0 and v + 1 < 0: symexTarget("hit")

proc offNarrow(v: int8): int8 = v + 1

proc offAdd(v: int): int = v + 1

proc sutCallsChecked(v: int) =
  if checkedAdd(v) == 7: symexTarget("hit")

proc sutMulEq(v: int) =
  var x = v
  x *= 2
  if x == 14: symexTarget("hit")

proc sutMulEq8(v: int8) =
  var x = v
  x *= 2
  if x == 14: symexTarget("hit")

proc sutPlusEq(v: int) =
  var x = v
  x += 1
  if x > v: discard
  else: symexTarget("hit")
{.pop.}

{.push checks: off.}
proc sutChecksOff(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")
{.pop.}

proc sutCallerAfter(v: int8) =
  let w = offNarrow(v)
  if w - 1 == 3: symexTarget("hit")

proc sutCallsUnder(v: int) =
  if offAdd(v) > v: discard
  else: symexTarget("hit")

proc sutInnerOff(v: int) =
  var r: int
  {.push overflowChecks: off.}
  r = v + 1
  {.pop.}
  if r + v == -1: symexTarget("hit")

proc nativeRaises(f: proc (v: int) {.nimcall.}; v: int): string =
  try:
    f(v)
    ""
  except OverflowDefect:
    "OverflowDefect"

template raisesOvf(fn: untyped) =
  let x = pinFind(fn, tRaisedExn("OverflowDefect"))
  checkpoint show(x.errors)
  check x.status == sxRaised

suite "int6-o: an overflow-off region in a checked build":
  test "the build checks overflow, without -fwrapv":
    check coOverflow in buildSemantics.checks
    check buildRegime() == rgChecked
    check not buildSemantics.fwrapv

  test "native: v + 1 > v at high(int) is undefined (compiler-dependent)":
    let n = nativeRun(sutAddCmp(high(int)))
    # Whether "hit" is reached is the compiler's choice (gcc folds the
    # comparison, MSVC wraps); both are legal for undefined behaviour, so only
    # the absence of a raise is pinned.
    check n.raised == ""

  test "the region's signed overflow halts as in an off build":
    pinDecline(sutAddCmp, cellKey(axDefinedness, "add/signed/pushOff/region"),
               ubSignedOverflow, excluding = {feOverflowCheckOption,
                                              feCheckOption})

  test "checks: off is walked, not declined":
    pinDecline(sutChecksOff, cellKey(axDefinedness, "add/signed/checksOffPush"),
               ubSignedOverflow, excluding = {feOverflowCheckOption,
                                              feCheckOption})

  test "an int8 sum in the region is a defined wrap: exact":
    let r = pinExact(sutNarrow, cellKey(axDefinedness, "add/signed8/pushOff"),
                     domain = sampled([0'i8, 1, 126, 127]))
    check r.status == sxSat

  test "a callee declared outside the push keeps its checks":
    check nativeRaises(sutCallsChecked, high(int)) == "OverflowDefect"
    raisesOvf(sutCallsChecked)

  test "a callee declared under the push keeps it from checked code":
    check nativeRaises(sutCallsUnder, high(int)) == ""
    pinDecline(sutCallsUnder, cellKey(axDefinedness, "add/signed/pushOff/callee"),
               ubSignedOverflow, excluding = {feOverflowCheckOption})
    let x = symexFind(sutCallsUnder, tRaisedExn("OverflowDefect"))
    checkpoint show(x.errors)
    check x.status != sxRaised

  test "the checked caller's arithmetic after the call still raises":
    check native(sutCallerAfter(127'i8)) == "OverflowDefect"
    let x = pinFind(sutCallerAfter, tRaisedExn("OverflowDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised
    let r = pinFind(sutCallerAfter, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "system's *= is the build's: it raises inside the push":
    check nativeRaises(sutMulEq, high(int)) == "OverflowDefect"
    raisesOvf(sutMulEq)
    check native(sutMulEq8(100'i8)) == "OverflowDefect"
    let x = pinFind(sutMulEq8, tRaisedExn("OverflowDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised
    let r = pinFind(sutMulEq, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "+= is the Inc magic: the caller's region, no raise":
    check nativeRaises(sutPlusEq, high(int)) == ""
    pinDecline(sutPlusEq, cellKey(axDefinedness, "inc/signed/pushOff"),
               ubSignedOverflow, excluding = {feOverflowCheckOption})
    let x = symexFind(sutPlusEq, tRaisedExn("OverflowDefect"))
    checkpoint show(x.errors)
    check x.status != sxRaised

  test "a push inside a routine body declines, it is not read as checked":
    check native(sutInnerOff(id(high(int)))) == "hit"
    pinDecline(sutInnerOff, cellKey(faGeneric, "int6o_overflow/inner"),
               feCheckOption)

suite "int6-o: walker version":
  test "walker version floor >= 467":
    check parseInt(symexWalkerVersion) >= 467
