## RFC-0016 int6 (item 2): a check option belongs to the code region it was
## compiled under, in both directions. This file builds with Nim's default
## checks; `tsymex_0016_int6p2_checkscope_off` is its `--rangeChecks:off
## --boundChecks:off` twin.
##
## Native, on the pinned toolchain (each judged against the native binary by
## `pinFind`, `pinUndefined` for a C-undefined access):
##   * a routine declared under `{.push rangeChecks: off.}` converts without a
##     check: `R(300)` keeps 300, `int8(300)` is 44, no `RangeDefect`;
##   * system's `*=` is a routine compiled under the build's options, so in
##     that routine `v *= k` still raises `RangeDefect` when the product
##     leaves the range; the operand's hidden conversion `y: T` is the
##     caller's, unchecked (float: `v *= 1.5` at `v == 0.5` stores 0.75);
##   * a routine declared under the push and called from outside it keeps its
##     declaration's (unchecked); a routine declared outside it and called
##     from inside keeps its own (checked): a callee never inherits;
##   * a nested `push rangeChecks: on` inside the push raises, and the outer
##     push is restored after its `pop`;
##   * under `{.push boundChecks: off.}` `s[i]` is a plain C subscript: in
##     bounds exact, out of bounds undefined (`index/unchecked`), the path
##     halting there as in a `--boundChecks:off` build
##     (`tsymex_0016_boundoff`);
##   * a `push rangeChecks: off` inside a routine body leaves the routine
##     unchecked at one position only (`R(300)` keeps 300 there): RFC-0016
##     int6-a5 walks that region under its own scope (it declined
##     `feCheckOption`, and before that was walked checked, a false `sxUnsat`
##     for the label).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/definedness
import ./s8cu_helpers

type
  R = range[0 .. 10]
  U64 = range[0.0 .. 1.0]

const ik = cellKey(axDefinedness, "index/unchecked")

proc convChecked(v: int): int = int(R(v))

{.push rangeChecks: off.}
proc convOff(v: int) =
  let r = R(v)
  if int(r) == 300: symexTarget("hit")

proc narrowOff(v: int) =
  if v > 127 and int8(v) == 44'i8: symexTarget("hit")

proc mulOff(k: R) =
  var v: R = 3
  v *= k
  if int(v) == 9: symexTarget("hit")

proc fmulOff(a: float) =
  var v: U64 = 0.5
  v *= a
  if a > 1.0 and v < 1.0: symexTarget("hit")

proc convUnder(v: int): int = int(R(v))

proc callsChecked(v: int) =
  if convChecked(v) == 300: symexTarget("hit")

{.push rangeChecks: on.}
proc nestedOn(v: int) =
  discard R(v)
  if v == 300: symexTarget("hit")
{.pop.}

proc afterNested(v: int) =
  let r = R(v)
  if int(r) == 300: symexTarget("hit")
{.pop.}

proc callsUnder(v: int) =
  if convUnder(v) == 300: symexTarget("hit")

{.push boundChecks: off.}
proc idxOff(v: int) =
  let s = @[10, 20, 30]
  if s[v] == 30: symexTarget("hit")

proc idxOffOob(v: int) =
  var s = @[1, 2, 3]
  s[v] = 9
  if v < 0 or v > 2: symexTarget("hit")
{.pop.}

proc innerOff(v: int) =
  {.push rangeChecks: off.}
  let r = R(v)
  {.pop.}
  if int(r) == 300: symexTarget("hit")

template keeps(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxSat
  let x = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(x.errors)
  check x.status == sxUnsat

template raises(fn: untyped) =
  let x = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(x.errors)
  check x.status == sxRaised

suite "int6 check scopes: a pushed-off region in a checked build":
  test "the build checks ranges and bounds":
    check coRange in buildSemantics.checks
    check coBound in buildSemantics.checks
  test "the routine's own conversions keep the unchecked value":
    keeps(convOff)
    keeps(narrowOff)
  test "system's *= is the build's: it raises, the operand is the caller's":
    raises(mulOff)
    let r = pinFind(mulOff, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    raises(fmulOff)
    let f = pinFind(fmulOff, tLabel("hit"))
    checkpoint show(f.errors)
    check f.status == sxSat
  test "a callee declared outside the push keeps its own checks":
    raises(callsChecked)
  test "a callee declared under the push keeps it when called from outside":
    keeps(callsUnder)
  test "a nested push on raises, and its pop restores the push off":
    raises(nestedOn)
    keeps(afterNested)
  test "boundChecks off: in bounds exact, out of bounds undefined":
    let r = pinFind(idxOff, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    pinDecline(idxOffOob, ik, ubArrayOutOfBounds, excluding = {feCheckOption})
  test "a push inside a routine body is walked unchecked there (int6-a5)":
    check native(innerOff(300)) == "hit"
    keeps(innerOff)

suite "int6 check scopes: walker version":
  test "walker version floor >= 465":
    check parseInt(symexWalkerVersion) >= 465
