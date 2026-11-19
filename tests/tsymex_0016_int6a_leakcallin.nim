## RFC-0016 int6-a, leaked scopes, a fallback: a module-level call under a
## push. To a text scan the `doAssert` may be a macro or template that
## imports, and a module it imports first would be compiled under the push.
## Natively it imports nothing, `s0016_int6a_leaked` is first compiled under
## the push, and `leakConv(300)` keeps 300. The compile order is not replayed
## past such a call: the coarse reading stands, and the routine declines.

import std/unittest
import nelli/symex
import nelli/smt/errorkind

{.push rangeChecks: off.}
import ./s0016_int6a_leaked
doAssert leakConv(1) == 1
{.pop.}

import ./s8cu_helpers

const gk = cellKey(faGeneric, "int6a_leakcallin")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-a leaked scopes: a call under the push keeps the coarse reading":
  test "the leaked routine declines":
    check native(callsLeaked(300)) == "hit"
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
