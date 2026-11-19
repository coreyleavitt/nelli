## RFC-0016 int6-a5 (check-scope class 5): a `{.push ...checks: ....}` /
## `{.pop.}` pair inside a routine body. This file builds with Nim's default
## checks; `tsymex_0016_rangeoff` and `tsymex_0016_int6p2_checkscope_off` hold
## the pushed-on direction in builds with the checks off.
##
## The typed body keeps each push and pop as a pragma statement, and the code
## generator applies them in generation (textual) order, so the walker models
## each balanced pair as a region of its routine with its own check scope and
## arithmetic. Native, on the pinned toolchain (c backend, x86-64 Linux):
##   * nested pushes nest: an inner `push rangeChecks: on` inside a `push
##     rangeChecks: off` raises `RangeDefect` on `R(300)`, and after its pop the
##     outer region keeps 300 unchecked;
##   * after the pop the routine's own options are back (`R(300)` raises);
##   * a callee called from inside the region keeps its own options (its
##     declaration's): `convChecked(300)` raises;
##   * one push may turn off both range and overflow checks: `R(300)` keeps 300
##     and `v + 1` runs the plain C addition there (undefined at `high(int)`);
##     after the pop `v + 1` raises `OverflowDefect` again.
## Fail closed (`feCheckOption`), with the native behaviour each would need:
##   * a push in an `if` branch with no pop in that branch: the generator keeps
##     it for the rest of the routine, whether the branch runs or not
##     (`ifLeak(-3)` converts `R(-3)` after the `if` unchecked);
##   * a push that runs to the routine's end (no pop);
##   * a push inside a `when` branch of several statements, popped after it;
##   * a `defer` inside a region (its body runs at the routine's end);
##   * a push in an inline iterator's body (it lands in its caller);
##   * a routine declared inside a pushing body (its position is the push's,
##     which the module scan does not read).

import std/[unittest, strutils]
import nelli/smt/arith_regime
import nelli
import nelli/symex
import ./s8cu_helpers

type R = range[0 .. 10]

const sk = cellKey(faGeneric, "int6a5_bodypush")

proc id(x: int): int {.noinline.} = x

proc convChecked(v: int): int = int(R(v))

proc nestedOn(v: int) =
  {.push rangeChecks: off.}
  let a = R(v)
  {.push rangeChecks: on.}
  discard R(v)
  {.pop.}
  {.pop.}
  if int(a) == 300: symexTarget("hit")

proc nestedRestore(v: int) =
  {.push rangeChecks: off.}
  {.push rangeChecks: on.}
  discard id(v)
  {.pop.}
  let a = R(v)
  {.pop.}
  if int(a) == 300: symexTarget("hit")

proc afterPop(v: int) =
  {.push rangeChecks: off.}
  discard R(v)
  {.pop.}
  discard R(v)
  if v == 300: symexTarget("hit")

proc callsFromRegion(v: int) =
  {.push rangeChecks: off.}
  let x = convChecked(v)
  {.pop.}
  if x == 300: symexTarget("hit")

proc bothOff(v: int) =
  {.push rangeChecks: off, overflowChecks: off.}
  let q = R(v)
  let s = v + 1
  {.pop.}
  if int(q) == 300 and s == 301: symexTarget("hit")

proc ovfRegion(v: int) =
  var r: int
  {.push rangeChecks: off, overflowChecks: off.}
  r = v + 1
  {.pop.}
  if r + v == -1: symexTarget("hit")

proc ovfAfterPop(v: int) =
  {.push overflowChecks: off.}
  discard id(v)
  {.pop.}
  let s = v + 1
  if s == 7: symexTarget("hit")

proc ifLeak(v: int) =
  if v > 0:
    {.push rangeChecks: off.}
    discard R(v)
  let a = R(v)
  if int(a) == -3: symexTarget("hit")

proc unpopped(v: int) =
  {.push rangeChecks: off.}
  let a = R(v)
  if int(a) == 300: symexTarget("hit")

proc whenSpan(v: int) =
  when true:
    {.push rangeChecks: off.}
    let a = R(v)
  {.pop.}
  if int(a) == 300: symexTarget("hit")

proc deferInRegion(v: int) =
  {.push rangeChecks: off.}
  defer: discard R(v)
  discard R(v + 1)
  {.pop.}
  if v == 300: symexTarget("hit")

iterator offIter(v: int): int =
  {.push rangeChecks: off.}
  yield int(R(v))
  {.pop.}

proc viaIter(v: int) =
  for x in offIter(v):
    if x == 300: symexTarget("hit")

proc outerPushes(v: int) =
  {.push rangeChecks: off.}
  proc inner(w: int): int = int(R(w))
  {.pop.}
  if inner(v) == 300: symexTarget("hit")

proc nativeOvf(f: proc (v: int) {.nimcall.}; v: int): string =
  try:
    f(v)
    ""
  except OverflowDefect:
    "OverflowDefect"

template keeps(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxSat
  let x = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(x.errors)
  check x.status == sxUnsat

template raises(fn: untyped; exn: string) =
  let x = pinFind(fn, tRaisedExn(exn))
  checkpoint show(x.errors)
  check x.status == sxRaised

suite "int6-a5: a push inside a routine body is a region of its own":
  test "the build checks range and overflow":
    check coRange in buildSemantics.checks
    check coOverflow in buildSemantics.checks

  test "a nested push on raises inside a push off":
    check native(nestedOn(300)) == "RangeDefect"
    check native(nestedOn(5)) == "ran"
    raises(nestedOn, "RangeDefect")

  test "the inner pop restores the outer push off":
    check native(nestedRestore(300)) == "hit"
    keeps(nestedRestore)

  test "after the pop the routine's own checks are back":
    check native(afterPop(300)) == "RangeDefect"
    check native(afterPop(5)) == "ran"
    raises(afterPop, "RangeDefect")

  test "a callee called from the region keeps its own checks":
    check native(callsFromRegion(300)) == "RangeDefect"
    raises(callsFromRegion, "RangeDefect")

  test "one push turns off range and overflow checks":
    check native(bothOff(300)) == "hit"
    keeps(bothOff)
    let x = symexFind(bothOff, tRaisedExn("OverflowDefect"))
    checkpoint show(x.errors)
    check x.status != sxRaised

  test "the region's signed overflow is undefined, as in an off build":
    check nativeOvf(ovfRegion, id(high(int))) == ""
    pinDecline(ovfRegion, cellKey(axDefinedness, "add/signed/pushOff/bodyRegion"),
               ubSignedOverflow, excluding = {feOverflowCheckOption,
                                              feCheckOption})

  test "after an overflow-off region the routine checks overflow again":
    check nativeOvf(ovfAfterPop, high(int)) == "OverflowDefect"
    raises(ovfAfterPop, "OverflowDefect")
    let r = pinFind(ovfAfterPop, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

suite "int6-a5: shapes that fail closed":
  test "a push in a branch, unpopped there, leaks past it natively":
    check native(ifLeak(-3)) == "hit"
    check native(ifLeak(300)) == "ran"
    pinDecline(ifLeak, sk, feCheckOption, needle = "not popped in its own")

  test "a push that runs to the routine's end":
    check native(unpopped(300)) == "hit"
    pinDecline(unpopped, sk, feCheckOption, needle = "not popped in its own")

  test "a push in a when branch popped after it":
    check native(whenSpan(300)) == "hit"
    pinDecline(whenSpan, sk, feCheckOption, needle = "another statement list")

  test "a defer inside a region":
    check native(deferInRegion(300)) == "hit"
    pinDecline(deferInRegion, sk, feCheckOption, needle = "`defer`")

  test "a push in an inline iterator's body":
    check native(viaIter(300)) == "hit"
    pinDecline(viaIter, sk, feCheckOption, needle = "inlined iterator")

  test "a routine declared inside a pushing body":
    check native(outerPushes(300)) == "hit"
    pinDecline(outerPushes, sk, feCheckOption, needle = "declared inside")

suite "int6-a5: walker version":
  test "walker version floor >= 474":
    check parseInt(symexWalkerVersion) >= 474
