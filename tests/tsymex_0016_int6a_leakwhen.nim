## RFC-0016 int6-a, leaked scopes, a fallback: an import under a push and
## under a `when` the scan cannot decide (a `const`). Natively the branch is
## taken, `s0016_int6a_leaked` is first compiled under the push, and
## `leakConv(300)` keeps 300. The scan cannot say whether the import happens
## there, so the compile order is not replayed: the coarse reading stands,
## and the routine declines.

import std/unittest
import nelli/symex
import nelli/smt/errorkind

const leakOn = true

{.push rangeChecks: off.}
when leakOn:
  import ./s0016_int6a_leaked
{.pop.}

import ./s8cu_helpers

const gk = cellKey(faGeneric, "int6a_leakwhen")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-a leaked scopes: an undecided when keeps the coarse reading":
  test "the leaked routine declines":
    check native(callsLeaked(300)) == "hit"
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
