## RFC-0016 int6-w2, leaked scopes: a definition inside a module-level pragma
## block. `{.cast(gcsafe).}: body` opens no scope: what its body defines is
## visible at the module's level after it (natively below: `w2PbVisible` is
## called outside the block, and the template there is what `w2PbTick()`
## expands, the proc of that name taking an argument).
##
## The module-level call rule (int6-m6, walker 478) reads the names each
## visible module defines from its text (`check_scan.moduleDefs`), and did not
## follow a pragma block: here it read `w2PbTick` as a proc alone, a call that
## imports nothing, and replayed the compile order past it, so
## `s0016_int6w2_leakpb` was read as first compiled under the push below and
## `leakConv(300)` as keeping 300: a trusted `sxSat`. Natively the template
## the call resolves to imports that module first, unpushed, and
## `leakConv(300)` raises `RangeDefect`. The name is now read as a template
## too, and the coarse reading stands: the routine declines.

import std/unittest
import nelli/symex
import nelli/smt/errorkind

proc w2PbTick(x: int) = discard x
{.cast(gcsafe).}:
  proc w2PbVisible(): int = 7
  template w2PbTick() =
    import ./s0016_int6w2_leakpb
w2PbTick()

{.push rangeChecks: off.}
import ./s0016_int6w2_leakpb
{.pop.}

import ./s8cu_helpers

const gk = cellKey(faGeneric, "int6w2_pragmablock")

proc callsLeaked(v: int) =
  if leakConv(v) == 300: symexTarget("hit")

suite "int6-w2: a template defined inside a module-level pragma block":
  test "natively the block's definitions are visible, and the import is unpushed":
    check w2PbVisible() == 7
    check native(callsLeaked(300)) == "RangeDefect"

  test "the call keeps the coarse reading: the leaked routine declines":
    pinDecline(callsLeaked, gk, feCheckOption, needle = "leakConv")
