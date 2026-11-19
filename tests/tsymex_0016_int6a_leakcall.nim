## RFC-0016 int6-a, leaked scopes: a module-level call before an import under
## a push. `s8cu_helpers`, compiled first, calls `initLock` at its module
## level. A macro or template there could expand to an import, which would
## change what the push's import first compiles; `initLock` is defined, in
## every module visible at the call (`std/locks` among them), only as a
## `proc`, which imports nothing (int6-m6). Natively `s0016_int6a_leaked` is
## first compiled under the push and `leakConv(300)` keeps 300: the compile
## order is replayed past the call, and the routine is walked pushed.
## The twins that keep the coarse reading: a template, a macro, and a
## proc-and-template overload set called before the push
## (`tsymex_0016_int6a_leakcalltpl`, `_leakcallmac`, `_leakcallmix`).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/errorkind
import ./s8cu_helpers

{.push rangeChecks: off.}
import ./s0016_int6a_leaked
{.pop.}

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-m6 leaked scopes: a call of a proc before the push is replayed past":
  test "the leaked routine is walked pushed":
    check native(callsLeaked(300)) == "hit"
    let r = pinFind(callsLeaked, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check not r.errors.named(feCheckOption)
    let x = pinFind(callsLeaked, tRaisedExn("RangeDefect"))
    checkpoint show(x.errors)
    check x.status == sxUnsat

suite "int6-m6 leaked scopes: walker version":
  test "walker version floor >= 478":
    check parseInt(symexWalkerVersion) >= 478
