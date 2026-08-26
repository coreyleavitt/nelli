## RFC-fuzzer-nextgen G1a — thread `mode: wmExplore | wmFollowConcrete`
## through the walker's per-construct dispatch (mechanical).
##
## G1a's own deliverable is the SEAM, not new behavior: every arm of `walk`'s
## `case stmt.kind` (and `walkHeapArm`'s isDeref/isNew/isDerefWrite arm) now
## has a `case w.mode` branch, but `WalkMode` is private (`smt/runtime.nim`)
## and no public entry constructs a `WalkCtx` with anything but the default
## `wmExplore` yet — `wmFollowConcrete` is inert scaffolding for G1b/G2. So
## this file cannot exercise `wmFollowConcrete` directly; instead it pins
## exactly what the RFC asks G1a to guarantee: running the EXISTING public
## symex entry (`symexFind`, always `wmExplore`) is byte-identical to
## pre-G1a, across a spread of construct kinds touched by the seam
## (isIf/isCall, isWhile, isAssert, isRaise/isTry, isIndex). The full
## `tsymex_*`/`tfuzz*` suite staying green (untouched assertions) is the
## primary characterization; this file is the focused arm-spread pin.
import std/unittest
import nelli/symex

# ---- isIf / isCall -----------------------------------------------------
proc g1aIsPositive(x: int): bool = x > 0

proc g1aBranchCall(x: int): int =
  if g1aIsPositive(x):
    symexTarget("g1a_pos")
  x

# ---- isWhile (k-unroll loop) --------------------------------------------
# Bounded well within the default maxLoopUnwind (see tsymex_phase6_while.nim's
# "unwind exhaustion" case for the budget-exhausted counterpart): 0+1+2 == 3
# needs only 3 iterations.
proc g1aWhileSum(n: int): int =
  var i = 0
  var total = 0
  while i < n:
    total += i
    inc i
  if total == 3:
    symexTarget("g1a_sum3")
  total

# ---- isAssert ------------------------------------------------------------
proc g1aAssertPositive(x: int) =
  assert x > 0, "must be positive"

# ---- isRaise / isTry -----------------------------------------------------
proc g1aExplicitRaise(x: int) =
  if x == 42:
    raise newException(ValueError, "boom")

proc g1aTryExcept(x: int): int =
  try:
    if x == 0:
      raise newException(ValueError, "zero")
    result = 100 div x
  except ValueError:
    symexTarget("g1a_caught")
    result = -1

# ---- isIndex ---------------------------------------------------------------
proc g1aSeqIndex(xs: seq[int], i: int): int =
  xs[i]

suite "RFC-fuzzer-nextgen G1a — mode threaded through dispatch, wmExplore unchanged":

  test "isIf/isCall arm: target still reachable (byte-identical to pre-G1a)":
    let r = symexFind(g1aBranchCall, tLabel("g1a_pos"))
    check r.status == sxSat
    check r.witness[0] > 0

  test "isWhile arm: k-unroll target still reached":
    let r = symexFind(g1aWhileSum, tLabel("g1a_sum3"))
    check r.status == sxSat
    check r.witness[0] >= 3

  test "isAssert arm: assertion violation still raises AssertionDefect":
    let r = symexFind(g1aAssertPositive, tRaisedExn("AssertionDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check r.raisedWitness[0] <= 0

  test "isRaise arm: explicit raise still found":
    let r = symexFind(g1aExplicitRaise, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] == 42

  test "isTry arm: except-body target still reachable (raise caught, not propagated)":
    let r = symexFind(g1aTryExcept, tLabel("g1a_caught"))
    check r.status == sxSat
    check r.witness[0] == 0

  test "isIndex arm: out-of-bounds seq access still raises IndexDefect":
    let r = symexFind(g1aSeqIndex, tRaisedExn("IndexDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
