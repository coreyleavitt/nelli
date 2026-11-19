## RFC-0016 int6-m6, leaked scopes, a fallback: a call, before an import
## under a push, of a name defined both as a proc and as a template. Which
## one the call resolves to is overload resolution, which the scan does not
## do, and the template could import. Natively the proc is called and
## imports nothing, `s0016_int6a_leaked` is first compiled under the push,
## and `leakConv(300)` keeps 300; the compile order is not replayed past the
## call: the coarse reading stands, and the routine declines. The proc-only
## call is replayed past (`tsymex_0016_int6a_leakcall`).

import std/unittest
import nelli/symex
import nelli/smt/errorkind

proc m6Mix(x: int) = discard x
template m6Mix() = discard
m6Mix(1)

{.push rangeChecks: off.}
import ./s0016_int6a_leaked
{.pop.}

import ./s8cu_helpers

const gk = cellKey(faGeneric, "int6a_leakcallmix")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-m6 leaked scopes: a call of a proc-and-template overload set before the push keeps the coarse reading":
  test "the leaked routine declines":
    check native(callsLeaked(300)) == "hit"
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
