## RFC-0016 int6-a, leaked scopes: `s0016_int6a_leaked` is imported first
## here, under `{.push rangeChecks: off.}`, so natively it is compiled with
## the push and `leakConv(300)` keeps 300. The scan reads an import under a
## push as possibly first compiling the module it names, and everything that
## module may import, stdlib included: the position is either way, and the
## walk declines. `strutils.cmpIgnoreStyle`, which no user module here
## compiles, declines with the same leaked `rangeChecks`: the measurement of
## how far one such import reaches.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

{.push rangeChecks: off.}
import ./s0016_int6a_leaked
{.pop.}

const gk = cellKey(faGeneric, "int6a_leak")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

proc cmpStyle(a: string) =
  if a.len == 3 and cmpIgnoreStyle(a, "F_o") == 0: symexTarget("hit")

suite "int6-a leaked scopes":
  test "a push leaked through an import declines":
    check native(callsLeaked(300)) == "hit"
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
  test "the leak is read as reaching a stdlib module too":
    check native(cmpStyle("fO_")) == "hit"
    pinDecline(cmpStyle, gk, feCheckOption, needle = "rangeChecks")
