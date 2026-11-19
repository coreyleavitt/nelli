## RFC-0016 int6 (item 2): the `--rangeChecks:off --boundChecks:off` twin of
## `tsymex_0016_int6p2_checkscope` (this file's `.nim.cfg`). A check option
## belongs to the code region it was compiled under, so a pushed-on region of
## an unchecked build is checked, and system's routines keep the build's.
##
## Native, on the pinned toolchain (judged by `pinFind`):
##   * a routine declared under `{.push rangeChecks: on.}` raises `RangeDefect`
##     on `R(300)`; one under `{.push boundChecks: on.}` raises `IndexDefect`
##     on `s[5]`;
##   * system's `*=` is compiled under the build's options: under the push
##     `v *= k` stores 30 into a `range[0..10]` without a raise;
##   * a routine declared outside the push keeps the build's (unchecked) when
##     called from inside it, and one declared under it keeps the push when
##     called from outside.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

type R = range[0 .. 10]

proc convPlain(v: int): int = int(R(v))

{.push rangeChecks: on.}
proc convOn(v: int) =
  discard R(v)
  if v == 300: symexTarget("hit")

proc mulOn(k: R) =
  var v: R = 3
  v *= k
  if int(v) == 30: symexTarget("hit")

proc callsPlain(v: int) =
  if convPlain(v) == 300: symexTarget("hit")

proc convUnder(v: int): int = int(R(v))
{.pop.}

proc callsUnder(v: int) =
  if convUnder(v) == 7: symexTarget("hit")

{.push boundChecks: on.}
proc idxOn(v: int) =
  let s = @[10, 20, 30]
  if s[v] == 30: symexTarget("hit")
{.pop.}

template keeps(fn: untyped) =
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxSat
  let x = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(x.errors)
  check x.status == sxUnsat

template raises(fn: untyped; exn = "RangeDefect") =
  let x = pinFind(fn, tRaisedExn(exn))
  checkpoint show(x.errors)
  check x.status == sxRaised

suite "int6 check scopes: a pushed-on region in an unchecked build":
  test "the build has range and bound checks off":
    check coRange notin buildSemantics.checks
    check coBound notin buildSemantics.checks
  test "the routine's own conversion raises":
    raises(convOn)
  test "system's *= is the build's: it keeps the product":
    keeps(mulOn)
  test "a callee declared outside the push keeps the build's":
    keeps(callsPlain)
  test "a callee declared under the push raises when called from outside":
    raises(callsUnder)
  test "boundChecks on: s[i] raises IndexDefect":
    raises(idxOn, "IndexDefect")
    let r = pinFind(idxOn, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

suite "int6 check scopes (off build): walker version":
  test "walker version floor >= 465":
    check parseInt(symexWalkerVersion) >= 465
