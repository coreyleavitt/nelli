## RFC-0016 W3-z P17: how a `..` / `..<` / `countup` / `countdown` bound is
## read, and the unsigned counters.
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

var gBump = 0
proc bump(): int =
  inc gBump
  3

proc sLenGrow(a: int) =
  var s = @[1]
  var n = 0
  for i in 0 ..< s.len:
    s.add 0
    n += 1
    if n >= 4: break
  if n == 1 and a == 1: symexTarget("hit")

proc sExprGrow(a: int) =
  var m = 1
  var n = 0
  for i in 0 .. m + 0:
    m += 1
    n += 1
    if n >= 4: break
  if n == 2 and a == 1: symexTarget("hit")

proc sSymGrow(a: int) =
  var m = 1
  var n = 0
  for i in 0 .. m:
    m += 1
    n += 1
    if n >= 4: break
  if n == 4 and a == 1: symexTarget("hit")

proc sSymShrink(a: int) =
  var m = 3
  var n = 0
  for i in 0 .. m:
    m -= 1
    n += 1
  if n == 2 and a == 1: symexTarget("hit")

proc sLtSymShrink(a: int) =
  var m = 3
  var n = 0
  for i in 0 ..< m:
    m -= 1
    n += 1
  if n == 2 and a == 1: symexTarget("hit")

proc sSideEffect(a: int) =
  gBump = 0
  var n = 0
  for i in 0 .. bump(): n += 1
  if n == 4 and gBump == 1 and a == 1: symexTarget("hit")

proc sSideEffectLt(a: int) =
  gBump = 0
  var n = 0
  for i in 0 ..< bump(): n += 1
  if n == 3 and gBump == 1 and a == 1: symexTarget("hit")

proc sDownExprGrow(a: int) =
  var m = 4
  var n = 0
  for i in countdown(5, m - 0):
    m -= 1
    n += 1
    if n >= 4: break
  if n == 2 and a == 1: symexTarget("hit")

proc sDownSideEffect(a: int) =
  gBump = 0
  var n = 0
  for i in countdown(5, bump()): n += 1
  if n == 3 and gBump == 1 and a == 1: symexTarget("hit")

proc sUpSideEffect(a: int) =
  gBump = 0
  var n = 0
  for i in countup(0, bump(), 2): n += 1
  if n == 2 and gBump == 1 and a == 1: symexTarget("hit")

suite "W3-z P17: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 317

const dd = cellKey(faCallShape, "p17/dotdot")

suite "W3-z P17: a non-symbol bound is read once":
  test "..< s.len, body grows s": discard pinExact(sLenGrow, dd)
  test ".. m+0, body grows m": discard pinExact(sExprGrow, dd)
  test ".. m, body grows m": discard pinExact(sSymGrow, dd)
  test ".. m, body shrinks m": discard pinExact(sSymShrink, dd)
  test "..< m, body shrinks m": discard pinExact(sLtSymShrink, dd)
  test ".. bump()": discard pinExact(sSideEffect, dd)
  test "..< bump()": discard pinExact(sSideEffectLt, dd)
  test "countdown expr bound": discard pinExact(sDownExprGrow, dd)
  test "countdown bump()": discard pinExact(sDownSideEffect, dd)
  test "countup bump() step": discard pinExact(sUpSideEffect, dd)

# --- unsigned counters -------------------------------------------------------
proc uUp32(a: int) =
  var n = 0'u32
  for i in countup(1'u32, 4'u32): n += i
  if n == 10'u32 and a == 1: symexTarget("hit")

proc uUp32Step(a: int) =
  var n = 0'u32
  for i in countup(0'u32, 9'u32, 3'u32): n += i
  if n == 18'u32 and a == 1: symexTarget("hit")

proc uUp32Sym(a: int) =
  var n = 0'u32
  for i in countup(0'u32, uint32(a and 7)): n += i
  if n == 6'u32 and a > 0: symexTarget("hit")

proc uUp32Break(a: int) =
  var n = 0'u32
  for i in countup(1'u32, 10'u32):
    if i == uint32(a) and a > 2: break
    n += i
  if n == 6'u32 and a == 4: symexTarget("hit")

proc uUp32Top(a: int) =
  # the last step stays below high(uint32): no wrap
  var n = 0
  for i in countup(high(uint32) - 2'u32, high(uint32) - 1'u32): n += 1
  if n == 2 and a == 1: symexTarget("hit")

proc uUp64(a: int) =
  var n = 0'u64
  for i in countup(1'u64, 4'u64): n += i
  if n == 10'u64 and a == 1: symexTarget("hit")

proc uUp64Big(a: int) =
  # counter values above high(int64)
  var n = 0
  let b = 1'u64 shl 63
  for i in countup(b, b + 2'u64):
    if i > 5'u64: n += 1
  if n == 3 and a == 1: symexTarget("hit")

proc uUpU(a: int) =
  var n = 0'u
  for i in countup(1'u, 4'u): n += i
  if n == 10'u and a == 1: symexTarget("hit")

proc uDown32(a: int) =
  var n = 0'u32
  for i in countdown(4'u32, 1'u32): n = n * 2'u32 + i
  if n == 26'u32 and a == 1: symexTarget("hit")

proc uDown32Step(a: int) =
  var n = 0'u32
  for i in countdown(10'u32, 3'u32, 3'u32): n = n * 100'u32 + i
  if n == 100704'u32 and a == 1: symexTarget("hit")

proc uDown64Zero(a: int) =
  # `uint64` stops at `b` before stepping: no wrap at 0
  var n = 0
  for i in countdown(2'u64, 0'u64): n += 1
  if n == 3 and a == 1: symexTarget("hit")

proc uDownUZero(a: int) =
  var n = 0'u
  for i in countdown(4'u, 0'u, 2): n = n * 10'u + i
  if n == 420'u and a == 1: symexTarget("hit")

proc uDown64Sym(a: int) =
  var n = 0'u64
  for i in countdown(uint64(a and 3), 0'u64): n += i
  if n == 6'u64 and a > 0: symexTarget("hit")

proc uDown64Big(a: int) =
  var n = 0
  let b = 1'u64 shl 63
  for i in countdown(b + 1'u64, b): 
    if i > 5'u64: n += 1
  if n == 2 and a == 1: symexTarget("hit")

proc uUnsat(a: int) =
  var n = 0'u32
  for i in countup(1'u32, 4'u32): n += i
  if n == 11'u32: symexTarget("hit")

proc dd32(a: int) =
  var n = 0'u32
  for i in 1'u32 .. 4'u32: n += i
  if n == 10'u32 and a == 1: symexTarget("hit")

proc dd32Lt(a: int) =
  var n = 0'u32
  for i in 0'u32 ..< 4'u32: n += i
  if n == 6'u32 and a == 1: symexTarget("hit")

proc dd64Big(a: int) =
  var n = 0
  let b = 1'u64 shl 63
  for i in b .. b + 2'u64:
    if i > 5'u64: n += 1
  if n == 3 and a == 1: symexTarget("hit")

proc ddU(a: int) =
  var n = 0'u
  for i in 1'u .. 4'u: n += i
  if n == 10'u and a == 1: symexTarget("hit")

proc dd32Sym(a: int) =
  var n = 0'u32
  for i in 0'u32 .. uint32(a and 7): n += i
  if n == 6'u32 and a > 0: symexTarget("hit")

proc dd32Wrap(a: int) =
  # `i - 1'u32` wraps at 0
  var n = 0
  for i in 0'u32 .. 2'u32:
    if i - 1'u32 > 100'u32: n += 1
  if n == 1 and a == 1: symexTarget("hit")

const uc = cellKey(faCallShape, "p17/unsigned")

suite "W3-z P17: countup over an unsigned counter":
  test "uint32": discard pinExact(uUp32, uc)
  test "uint32 step": discard pinExact(uUp32Step, uc)
  test "uint32 symbolic bound": discard pinExact(uUp32Sym, uc)
  test "uint32 break": discard pinExact(uUp32Break, uc)
  test "uint32 near high": discard pinExact(uUp32Top, uc)
  test "uint64": discard pinExact(uUp64, uc)
  test "uint64 above high(int64)": discard pinExact(uUp64Big, uc)
  test "uint": discard pinExact(uUpU, uc)
  test "unsat": discard pinExact(uUnsat, uc)

suite "W3-z P17: countdown over an unsigned counter":
  test "uint32": discard pinExact(uDown32, uc)
  test "uint32 step": discard pinExact(uDown32Step, uc)
  test "uint64 stops at b, no wrap": discard pinExact(uDown64Zero, uc)
  test "uint stops at b, no wrap": discard pinExact(uDownUZero, uc)
  test "uint64 symbolic": discard pinExact(uDown64Sym, uc)
  test "uint64 above high(int64)": discard pinExact(uDown64Big, uc)

suite "W3-z P17: .. over an unsigned counter":
  test "uint32": discard pinExact(dd32, uc)
  test "uint32 ..<": discard pinExact(dd32Lt, uc)
  test "uint64 above high(int64)": discard pinExact(dd64Big, uc)
  test "uint": discard pinExact(ddU, uc)
  test "uint32 symbolic": discard pinExact(dd32Sym, uc)
  test "uint32 wraps in the body": discard pinExact(dd32Wrap, uc)

# --- int32 `..` steps in int32 -------------------------------------------------
proc ddI32Top(a: int) =
  # `inc` of the int32 counter at high(int32) raises
  for i in high(int32) - 1'i32 .. high(int32): discard
  symexTarget("hit")

proc ddI8Wrap(a: int) =
  var n = 0
  for i in 0'u8 .. 2'u8:
    if i - 1'u8 > 100'u8: n += 1
  if n == 1 and a == 1: symexTarget("hit")

suite "W3-z P17: .. over int32 and uint8":
  test "int32 counter overflows at high": 
    discard pinExact(ddI32Top, uc, tRaisedExn("OverflowDefect"))
  test "uint8 wraps in the body": discard pinExact(ddI8Wrap, uc)

proc cuI8Wrap(a: int) =
  var n = 0
  for i in countup(0'u8, 2'u8):
    if i - 1'u8 > 100'u8: n += 1
  if n == 1 and a == 1: symexTarget("hit")

proc cdI8Wrap(a: int) =
  var n = 0
  for i in countdown(2'u8, 0'u8):
    if i - 1'u8 > 100'u8: n += 1
  if n == 1 and a == 1: symexTarget("hit")

proc ddU16Wrap(a: int) =
  var n = 0
  for i in 0'u16 ..< 2'u16:
    if i - 1'u16 > 100'u16: n += 1
  if n == 1 and a == 1: symexTarget("hit")

suite "W3-z P17: a small unsigned counter is its own type in the body":
  test "countup uint8": discard pinExact(cuI8Wrap, uc)
  test "countdown uint8": discard pinExact(cdI8Wrap, uc)
  test "..< uint16": discard pinExact(ddU16Wrap, uc)
