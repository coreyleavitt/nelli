## RFC-0016 int6-m6, leaked scopes, a fallback: a template called at the
## module's level before an import under a push. A template expands to
## statements, an `import` among them. Natively this one imports nothing,
## `s0016_int6a_leaked` is first compiled under the push, and `leakConv(300)`
## keeps 300; the scan does not expand it, so the compile order is not
## replayed past the call: the coarse reading stands, and the routine
## declines. The proc-only call is replayed past (`tsymex_0016_int6a_leakcall`).

import std/unittest
import nelli/symex
import nelli/smt/errorkind

template m6Tick() = discard
m6Tick()

{.push rangeChecks: off.}
import ./s0016_int6a_leaked
{.pop.}

import ./s8cu_helpers

const gk = cellKey(faGeneric, "int6a_leakcalltpl")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-m6 leaked scopes: a template call before the push keeps the coarse reading":
  test "the leaked routine declines":
    check native(callsLeaked(300)) == "hit"
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
