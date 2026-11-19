## RFC-0016 int6-a, leaked scopes: a push open at an `import` reaches the
## module that import first compiles, and what that module first compiles.
##
## Native, on the pinned toolchain (each judged by `pinFind` against this
## binary): Nim compiles `system` first, then the import graph depth first,
## each module at the first import that reaches it, under the check options
## open there; a later import of a compiled module changes nothing, and the
## importer's options come back after it. So here:
##   * `s0016_int6a_leaked` is first imported under `{.push rangeChecks:
##     off.}`: `leakConv(300)` keeps 300. Its later plain import changes
##     nothing;
##   * `s0016_int6a_leakdeep` is first imported by `s0016_int6a_leakvia`,
##     itself first compiled under the push: `deepConv(300)` keeps 300;
##   * `s0016_int6a_leakfirst` is imported plainly first and under the push
##     after: `firstConv(300)` raises `RangeDefect`;
##   * `strutils` is compiled before any push: `cmpIgnoreStyle` is walked
##     under its own module's scope alone.
## The scan replays that order, and each leak is a position state.
## `s8cu_helpers` is compiled before the push, and its module-level
## `initLock` call is read as a proc's, which imports nothing (int6-m6); a
## template or macro called there keeps the coarse reading
## (`tsymex_0016_int6a_leakcalltpl`, `_leakcallmac`, `_leakcallmix`).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s0016_int6a_leakfirst
import ./s8cu_helpers

{.push rangeChecks: off.}
import ./s0016_int6a_leaked, ./s0016_int6a_leakfirst, ./s0016_int6a_leakvia
{.pop.}

import ./s0016_int6a_leaked

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

proc callsDeep(v: int) =
  if viaConv(v) == 300: symexTarget("hit")

proc callsFirst(v: int) =
  if firstConv(v) == 300: symexTarget("hit")

proc cmpStyle(a: string) =
  if a.len == 1 and cmpIgnoreStyle(a, "_F") == 0: symexTarget("hit")

template keeps(fn: untyped) =
  ## Natively `fn(300)` reaches the label and never raises `RangeDefect`.
  check native(fn(300)) == "hit"
  let r = pinFind(fn, tLabel("hit"))
  checkpoint show(r.errors)
  check r.status == sxSat
  check not r.errors.named(feCheckOption)
  let x = pinFind(fn, tRaisedExn("RangeDefect"))
  checkpoint show(x.errors)
  check x.status == sxUnsat

suite "int6-a leaked scopes: the compile order replayed":
  test "a module first compiled under a push is walked pushed":
    keeps(callsLeaked)
  test "what that module first compiles is walked pushed too":
    keeps(callsDeep)
  test "a module compiled before the push keeps its checks":
    check native(callsFirst(300)) == "RangeDefect"
    check native(callsFirst(5)) == "ran"
    let x = pinFind(callsFirst, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxRaised
    check not x.errors.named(feCheckOption)
  test "a stdlib module compiled before the push is not reached":
    check native(cmpStyle("f")) == "hit"
    let r = pinFind(cmpStyle, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.named(feCheckOption)

suite "int6-a leaked scopes: walker version":
  test "walker version floor >= 478":
    check parseInt(symexWalkerVersion) >= 478
