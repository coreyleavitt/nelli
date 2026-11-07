## RFC-0016 WA-B, the checks-off rows (`.nim.cfg`: `--overflowChecks:off`).
##
## * S3. With the overflow checks off Nim emits no zero check, so a signed
##   `x div 0` / `x mod 0` reaches the C division, which is undefined (SIGFPE
##   on x86-64, probed below). It was a definite trap that confined the
##   survivor and recorded no omission; it now halts as `ubSignedDivZero`,
##   as an unsigned divisor does (`ubUnsignedDivZero`).
## * P1. Below `int`'s width a signed `+`, `-`, `*` and negation is not
##   undefined: Nim emits `(NI8)(a op b)`, the arithmetic is done in C's
##   promoted `int` and the narrowing wraps. `int8(127) + 1` is -128. It
##   halted `ubSignedOverflow`; it is exact now. 32 bits (C's `int`) stays
##   undefined.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

proc sutDiv(y: int) =
  let r = 10 div y
  if r == 11: symexTarget("hit")

proc sutMod(y: int) =
  let r = 10 mod y
  if r > 10: symexTarget("hit")

proc sutDiv32(y: int32) =
  let r = 10'i32 div y
  if r == 11: symexTarget("hit")

proc sutDivSat(y: int) =
  let r = 10 div y
  if r == 5: symexTarget("hit")

proc sutDivGuarded(y: int) =
  ## The zero side is ruled out by the guard: pruned, nothing recorded.
  if y != 0:
    let r = 10 div y
    discard r
    if y == 0: symexTarget("hit")

proc sutDivZeroRaised(y: int) =
  let r = 10 div y
  discard r

proc sutDivExcept(y: int) =
  try:
    let r = 10 div y
    discard r
  except DivByZeroDefect:
    symexTarget("c")

proc sutI8Add(v: int8) =
  if v + 1 < v: symexTarget("hit")

proc sutI8Sub(v: int8) =
  if v - 1 > v: symexTarget("hit")

proc sutI8Mul(v: int8) =
  if v > 0 and v * 2 < 0: symexTarget("hit")

proc sutI8Neg(v: int8) =
  if v != 0 and -v == v: symexTarget("hit")

proc sutI16Add(v: int16) =
  if v + 1 < v: symexTarget("hit")

proc sutI16Neg(v: int16) =
  if v != 0 and -v == v: symexTarget("hit")

proc sutI8Unsat(v: int8) =
  ## The wrapped sum is never `v + 2` when `v < 126`: unsat on `v`, exact.
  if v + 1 == 0 and v != -1: symexTarget("hit")

proc sutI32Add(v: int32) =
  if v + 1 < v: symexTarget("hit")

const probeDiv = """
proc id(x: int): int {.noinline.} = x
echo id(10) div id(0)
"""

const probeMod = """
proc id(x: int): int {.noinline.} = x
echo id(10) mod id(0)
"""

const i8Dom = sampled([int8(-128), -127, -2, -1, 0, 1, 63, 64, 126, 127])
const i16Dom = sampled([int16(-32768), -32767, -1, 0, 1, 32766, 32767])
const yDom = sampled([0, 1, 2, 5, 10, 11, -1])

suite "WA-B S3: signed division by zero, checks off":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 286

  test "the build is checks-off":
    check coOverflow notin buildSemantics.checks

  test "native: signed div by zero is a SIGFPE":
    pinCrash(cellKey(axDefinedness, "div/signed/zero/checksOff"), probeDiv,
             ["--overflowChecks:off"], ceDivTrap)

  test "native: signed mod by zero is a SIGFPE":
    pinCrash(cellKey(axDefinedness, "mod/signed/zero/checksOff"), probeMod,
             ["--overflowChecks:off"], ceDivTrap)

  test "div: the zero side halts, the verdict is not a trusted sxUnsat":
    pinDecline(sutDiv, cellKey(axDefinedness, "div/signed/zero/checksOff"),
               ubSignedDivZero)

  test "mod: the same":
    pinDecline(sutMod, cellKey(axDefinedness, "mod/signed/zero/checksOff"),
               ubSignedDivZero)

  test "int32 halts the same":
    pinDecline(sutDiv32, cellKey(axDefinedness, "div/signed32/zero/checksOff"),
               ubSignedDivZero)

  test "the omission is recorded on the verdict":
    let r = symexFind(sutDiv, tLabel("hit"))
    check not r.trusted
    check ubSignedDivZero in undefinedKinds(r.soundness) or
          r.errors.named(ubSignedDivZero)

  test "not a DivByZeroDefect raise, and no except arm sees it":
    let r = symexFind(sutDivZeroRaised, tRaisedExn("DivByZeroDefect"))
    check r.status != sxRaised
    check not r.trusted
    check r.errors.named(ubSignedDivZero)
    let c = symexFind(sutDivExcept, tLabel("c"))
    check c.status != sxSat
    check not c.trusted

  test "r == 5 at y == 2 stays sxSat (the defined side)":
    let r = pinExact(sutDivSat, cellKey(axDefinedness, "div/signed/defined/checksOff"),
                     domain = yDom)
    check r.status == sxSat

  test "the guard keeps a trusted sxUnsat and records nothing":
    let r = pinExact(sutDivGuarded,
                     cellKey(axDefinedness, "div/signed/pruned/checksOff"),
                     domain = yDom)
    check r.status == sxUnsat
    check r.trusted
    check not r.errors.named(ubSignedDivZero)

suite "WA-B P1: signed 8 and 16 bit arithmetic wraps, checks off":
  test "native: int8(127) + 1 is -128":
    proc id8(x: int8): int8 {.noinline.} = x
    check id8(127) + 1 == -128
    check id8(-128) - 1 == 127
    check id8(64) * 2 == -128
    check -id8(-128) == -128

  test "add: int8 is exact":
    let r = pinExact(sutI8Add, cellKey(axDefinedness, "add/int8/checksOff"),
                     domain = i8Dom)
    check r.status == sxSat
    check r.witness[0] == 127'i8
    check r.trusted
    check not r.errors.named(ubSignedOverflow)

  test "sub: int8 is exact":
    let r = pinExact(sutI8Sub, cellKey(axDefinedness, "sub/int8/checksOff"),
                     domain = i8Dom)
    check r.status == sxSat
    check r.witness[0] == -128'i8
    check not r.errors.named(ubSignedOverflow)

  test "mul: int8 is exact":
    let r = pinExact(sutI8Mul, cellKey(axDefinedness, "mul/int8/checksOff"),
                     domain = i8Dom)
    check r.status == sxSat
    check not r.errors.named(ubSignedOverflow)

  test "neg: int8 is exact":
    let r = pinExact(sutI8Neg, cellKey(axDefinedness, "neg/int8/checksOff"),
                     domain = i8Dom)
    check r.status == sxSat
    check r.witness[0] == -128'i8
    check not r.errors.named(ubSignedOverflow)

  test "an unsat int8 claim is a trusted sxUnsat":
    let r = pinExact(sutI8Unsat, cellKey(axDefinedness, "add/int8/unsat/checksOff"),
                     domain = i8Dom)
    check r.status == sxUnsat
    check r.trusted

  test "add and neg: int16 are exact":
    let a = pinExact(sutI16Add, cellKey(axDefinedness, "add/int16/checksOff"),
                     domain = i16Dom)
    check a.status == sxSat
    check a.witness[0] == 32767'i16
    check not a.errors.named(ubSignedOverflow)
    let n = pinExact(sutI16Neg, cellKey(axDefinedness, "neg/int16/checksOff"),
                     domain = i16Dom)
    check n.status == sxSat
    check n.witness[0] == -32768'i16

  test "int32 stays undefined (C's int)":
    pinDecline(sutI32Add, cellKey(axDefinedness, "add/int32/checksOff"),
               ubSignedOverflow)
