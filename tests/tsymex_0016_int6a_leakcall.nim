## RFC-0016 int6-a, leaked scopes, a fallback: a module-level call before an
## import under a push. `s8cu_helpers`, compiled first, calls `initLock` at
## its module level; to a text scan that call may be a macro or template that
## imports, which would change what the push's import first compiles.
## Natively it is a proc, `s0016_int6a_leaked` is first compiled under the
## push, and `leakConv(300)` keeps 300. The compile order is not replayed
## past such a call: the coarse reading stands, and the routine declines.

import std/unittest
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

{.push rangeChecks: off.}
import ./s0016_int6a_leaked
{.pop.}

const gk = cellKey(faGeneric, "int6a_leakcall")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-a leaked scopes: a call before the push keeps the coarse reading":
  test "the leaked routine declines":
    check native(callsLeaked(300)) == "hit"
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
