## RFC-0016 K9e: pins that kill the division/modulo survivors of the
## pin-strength mutation run (`docs/rfc-data/0016-k9e.md`). Each check names
## the mutated arm and pins a verdict that arm decides against the natively
## compiled proc: a negative dividend (the Int encoding's truncation
## adjustment), an unsigned value with its high bit set (the unsigned BV
## division), a signed narrow operand, `low(int8) div -1`.
import std/[unittest, strutils]
import nelli
import nelli/symex
import ./s8cu_helpers

# The Int encoding (`truncDivInt`) is reached by a width-stamped `svInt`, which
# a scan offset is (B4: `start` feeds `readCStr`'s loop and a string query).
# The dividend is negative with a non-zero remainder, so the truncation
# adjustment fires. The sampled native domain holds -1, 1, 7 and low(int):
# `-1 div 2 == 0`, `-1 mod 2 == -1`, `-1 div -2 == 0`, `-1 mod -2 == -1`.

type ScanError = object of CatchableError

proc readCStr(data: seq[byte], offset: int): (string, int) =
  var acc = ""
  var i = offset
  while i < data.len:
    if data[i] == 0'u8:
      return (acc, i + 1)
    acc.add char(data[i])
    i.inc
  raise newException(ScanError, "unterminated")

template scan() =
  ## Makes `start` a scan offset (a width-stamped Int).
  if start < 0: return
  try:
    let (k, p) = readCStr(data, start)
    if k.len == 2 and p == start + 3: symexTarget("hit")
  except ScanError:
    discard

proc sDivPos(data: seq[byte], start: int) =
  ## the quotient moves one step toward zero (Euclid says -1)
  if start < 0 and start div 2 == 0 and start mod 2 != 0: symexTarget("t")
  scan()

proc sModPos(data: seq[byte], start: int) =
  ## the remainder keeps the dividend's sign
  if start < 0 and start mod 2 == -1: symexTarget("t")
  scan()

proc sDivNeg(data: seq[byte], start: int) =
  ## a negative divisor steps the quotient the other way (Euclid says 1)
  if start < 0 and start div -2 == 0 and start mod -2 != 0: symexTarget("t")
  scan()

proc sModNeg(data: seq[byte], start: int) =
  ## the adjustment subtracts the divisor's magnitude, not the divisor
  if start < 0 and start mod -2 == -1: symexTarget("t")
  scan()

proc sutUDiv8(x, y: uint8) =
  if x == 255'u8 and y == 2'u8 and x div y == 127'u8: symexTarget("hit")

proc sutUMod8(x, y: uint8) =
  if x == 255'u8 and y == 2'u8 and x mod y == 1'u8: symexTarget("hit")

proc sutUDiv64(x, y: uint64) =
  if x == high(uint64) and y == 2'u64 and x div y == 9223372036854775807'u64:
    symexTarget("hit")

proc sutUMod64(x, y: uint64) =
  if x == high(uint64) and y == 2'u64 and x mod y == 1'u64:
    symexTarget("hit")

proc sutSMod8(x, y: int8) =
  if x == -7'i8 and y == 2'i8 and x mod y == -1'i8: symexTarget("hit")

proc sutSDiv8(x, y: int8) =
  if x == -7'i8 and y == 2'i8 and x div y == -3'i8: symexTarget("hit")

proc sutLowDiv8(x, y: int8) =
  ## `low(int8) div -1` is Nim's OverflowDefect; no other pair raises.
  discard x div y

proc sutLowDiv8Next(x, y: int8) =
  ## `-127 div -1` is defined (127): the survivor of the division must keep it.
  discard x div y
  if x == low(int8) + 1 and y == -1'i8: symexTarget("hit")

proc sutLowDiv8ByOne(x, y: int8) =
  ## `low(int8) div 1` is defined: the survivor must keep it.
  discard x div y
  if x == low(int8) and y == 1'i8: symexTarget("hit")

suite "K9e division/modulo pin strength":
  test "Int div: a negative dividend, positive divisor, truncates toward zero":
    let r = pinFind(sDivPos, tLabel("t"))
    check r.status == sxSat
  test "Int div: a negative divisor steps the quotient the other way":
    let r = pinFind(sDivNeg, tLabel("t"))
    check r.status == sxSat
  test "Int mod: a negative dividend keeps its sign":
    let r = pinFind(sModPos, tLabel("t"))
    check r.status == sxSat
  test "Int mod: a negative divisor is subtracted by its magnitude":
    let r = pinFind(sModNeg, tLabel("t"))
    check r.status == sxSat
  test "uint8 div with the high bit set is unsigned":
    let r = pinExact(sutUDiv8, cellKey(axDefinedness, "k9e/div/u8"),
                     domain = sampled([0'u8, 1, 2, 127, 128, 255]))
    check r.status == sxSat
  test "uint8 mod with the high bit set is unsigned":
    let r = pinExact(sutUMod8, cellKey(axDefinedness, "k9e/mod/u8"),
                     domain = sampled([0'u8, 1, 2, 127, 128, 255]))
    check r.status == sxSat
  test "uint64 div with the high bit set is unsigned":
    let r = pinExact(sutUDiv64, cellKey(axDefinedness, "k9e/div/u64"),
                     domain = sampled([0'u64, 1, 2, high(uint64)]))
    check r.status == sxSat
  test "uint64 mod with the high bit set is unsigned":
    let r = pinExact(sutUMod64, cellKey(axDefinedness, "k9e/mod/u64"),
                     domain = sampled([0'u64, 1, 2, high(uint64)]))
    check r.status == sxSat
  test "int8 mod of a negative dividend is signed":
    let r = pinExact(sutSMod8, cellKey(axDefinedness, "k9e/mod/i8"),
                     domain = sampled([-7'i8, -1, 2, 7]))
    check r.status == sxSat
  test "int8 div of a negative dividend is signed":
    let r = pinExact(sutSDiv8, cellKey(axDefinedness, "k9e/div/i8"),
                     domain = sampled([-7'i8, -1, 2, 7]))
    check r.status == sxSat
  test "int8: low div -1 is the OverflowDefect, and only that pair":
    let r = pinExact(sutLowDiv8, cellKey(axDefinedness, "k9e/div/i8/low"),
                     target = tRaisedExn("OverflowDefect"),
                     domain = sampled([low(int8), -1'i8, 1, 0, 7]))
    check r.status == sxRaised
  test "int8: -127 div -1 survives the division":
    let r = pinExact(sutLowDiv8Next, cellKey(axDefinedness, "k9e/div/i8/lowNext"),
                     domain = sampled([low(int8), low(int8) + 1, -1'i8, 0, 1, 7]))
    check r.status == sxSat
  test "int8: low div 1 survives the division":
    let r = pinExact(sutLowDiv8ByOne, cellKey(axDefinedness, "k9e/div/i8/lowByOne"),
                     domain = sampled([low(int8), low(int8) + 1, -1'i8, 0, 1, 7]))
    check r.status == sxSat
