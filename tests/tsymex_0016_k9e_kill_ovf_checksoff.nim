## RFC-0016 K9e: the overflow-checks-off half of `tsymex_0016_k9e_kill_ovf`.
## This file builds with `--overflowChecks:off` (its `.nim.cfg`): a signed
## `+` that overflows is undefined in C, so `depositSignedOverflow` makes it a
## `ubSignedOverflow` trap and the verdict declines. A walker that never
## deposits the trap answers a trusted `sxSat` for a label C may not reach.
import nelli
import nelli/symex
import std/unittest
import ./s8cu_helpers

proc sutAddCmp64(v: int) =
  if v + 1 > v: discard
  else: symexTarget("hit")

proc sutAddCmp32(v: int32) =
  if v + 1 > v: discard
  else: symexTarget("hit")

suite "K9e signed overflow, checks off":
  test "64-bit add: the overflow side declines (ubSignedOverflow)":
    pinDecline(sutAddCmp64, cellKey(axDefinedness, "add/signed/checksOff"),
               ubSignedOverflow)

  test "32-bit add: the overflow side declines (ubSignedOverflow)":
    pinDecline(sutAddCmp32, cellKey(axDefinedness, "add/signed/checksOff"),
               ubSignedOverflow)
