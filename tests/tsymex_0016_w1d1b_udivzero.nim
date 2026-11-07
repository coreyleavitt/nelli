## RFC-0016 W1-d1b -- an unsigned `div`/`mod` by zero halts through
## `haltUndefined` (section 9.1 item 1) instead of forking a
## `DivByZeroDefect`.
##
## Native, probed on the pinned toolchain (c and cpp identical, operands
## through a `noinline` identity so nothing folds), x86-64 Linux, default
## build:
##   10'u64 div 0'u64   -> SIGFPE, rc 136, no handler runs
##   10'u64 mod 0'u64   -> SIGFPE, rc 136
##   10'i64 div 0'i64   -> DivByZeroDefect (catchable)
##   10'i64 mod 0'i64   -> DivByZeroDefect (catchable)
## Nim's zero-divisor check covers the signed types only; the unsigned C
## division is undefined there. The signed side keeps its Defect fork.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutUDiv(k: uint64) =
  ## The quotient never exceeds 10 on a defined path: the target is
  ## unreachable except past the halted zero divisor.
  let r = 10'u64 div k
  if r == 11: symexTarget("hit")

proc sutUDivSat(k: uint64) =
  let r = 10'u64 div k
  if r == 5: symexTarget("hit")

proc sutUMod(k: uint64) =
  let r = 10'u64 mod k
  if r > 10: symexTarget("hit")

proc sutUDivRaised(k: uint64) =
  let r = 10'u64 div k
  discard r

proc sutUDivExcept(k: uint64) =
  try:
    let r = 10'u64 div k
    discard r
  except DivByZeroDefect:
    symexTarget("c")

proc sutUDivGuarded(k: uint64) =
  if k != 0:
    let r = 10'u64 div k
    if r == 5: symexTarget("hit")

proc sutUDivGuardedZero(k: uint64) =
  ## The zero side is ruled out by the guard: pruned, nothing recorded.
  if k != 0:
    let r = 10'u64 div k
    discard r
    if k == 0: symexTarget("hit")

proc sutSDiv(k: int) =
  let r = 10 div k
  discard r

proc udivCallee(k: uint64): uint64 = 10'u64 div k

proc sutUDivViaCall(k: uint64) =
  if udivCallee(k) == 11: symexTarget("hit")

proc sutUDiv32(k: uint32) =
  let r = 10'u32 div k
  if r == 11: symexTarget("hit")

const probeUDiv = """
proc id(x: uint64): uint64 {.noinline.} = x
echo id(10) div id(0)
"""

const probeUMod = """
proc id(x: uint64): uint64 {.noinline.} = x
echo id(10) mod id(0)
"""

const probeSDiv = """
proc id(x: int): int {.noinline.} = x
try:
  echo id(10) div id(0)
except DivByZeroDefect:
  echo "DivByZeroDefect"
  quit(0)
"""

const kDom = sampled([0'u64, 1, 2, 3, 5, 10, 11])

suite "W1-d1b unsigned division by zero":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 280

  test "native: unsigned div by zero is a SIGFPE":
    pinCrash(cellKey(axDefinedness, "div/unsigned/zero"), probeUDiv, [],
             ceDivTrap)

  test "native: unsigned mod by zero is a SIGFPE":
    pinCrash(cellKey(axDefinedness, "mod/unsigned/zero"), probeUMod, [],
             ceDivTrap)

  test "native: signed div by zero is a catchable DivByZeroDefect":
    let ok = nativeRun(sutSDiv(0))
    check ok.raised == "DivByZeroDefect"

  test "div: the zero side halts, the verdict is not a trusted sxUnsat":
    pinDecline(sutUDiv, cellKey(axDefinedness, "div/unsigned/zero"),
               ubUnsignedDivZero)

  test "mod: the same":
    pinDecline(sutUMod, cellKey(axDefinedness, "mod/unsigned/zero"),
               ubUnsignedDivZero)

  test "not a DivByZeroDefect raise":
    let r = symexFind(sutUDivRaised, tRaisedExn("DivByZeroDefect"))
    checkpoint show(r.errors)
    check r.status != sxRaised
    check not r.trusted
    check r.errors.named(ubUnsignedDivZero)

  test "an enclosing `except DivByZeroDefect` does not see the halt":
    let r = symexFind(sutUDivExcept, tLabel("c"))
    checkpoint show(r.errors)
    check not r.trusted
    check r.status != sxSat
    check r.errors.named(ubUnsignedDivZero)

  test "r == 5 at k == 2 stays sxSat (the defined side)":
    let r = symexFind(sutUDivSat, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 2'u64
    let ok = nativeRun(sutUDivSat(2))
    check "hit" in ok.hits

  test "the guard keeps a trusted sxUnsat and records nothing":
    let r = pinExact(sutUDivGuardedZero,
                     cellKey(axDefinedness, "div/unsigned/pruned"),
                     domain = kDom)
    check r.status == sxUnsat
    check r.trusted
    check not r.errors.named(ubUnsignedDivZero)

  test "the guarded defined side continues exactly":
    let r = pinExact(sutUDivGuarded,
                     cellKey(axDefinedness, "div/unsigned/guarded"),
                     domain = kDom)
    check r.status == sxSat
    check not r.errors.named(ubUnsignedDivZero)

  test "through a call":
    let r = symexFind(sutUDivViaCall, tLabel("hit"))
    checkpoint show(r.errors)
    check not r.trusted
    check r.errors.named(ubUnsignedDivZero)

  test "narrow width (uint32) halts the same":
    pinDecline(sutUDiv32, cellKey(axDefinedness, "div/unsigned32/zero"),
               ubUnsignedDivZero)

suite "W1-d1b signed division by zero is unchanged":
  test "the signed zero side is still a DivByZeroDefect fork":
    let r = pinExact(sutSDiv, cellKey(axDefinedness, "div/signed/zero"),
                     target = tRaisedExn("DivByZeroDefect"))
    check r.status == sxRaised
    check not r.errors.named(ubUnsignedDivZero)
