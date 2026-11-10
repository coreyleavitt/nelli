## RFC-0016 W3-z P18: a signed narrow `..` / `..<` / `countup` / `countdown`
## counter is its own type in the body (`i + 125'i8` raises OverflowDefect).
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

proc dd8(a: int) =
  for i in 0'i8 .. 3'i8:
    let j = i + 125'i8
    if j > 126'i8: symexTarget("hit")

proc dd8Lt(a: int) =
  for i in 0'i8 ..< 4'i8:
    let j = i + 125'i8
    if j > 126'i8: symexTarget("hit")

proc dd16(a: int) =
  for i in 0'i16 .. 3'i16:
    let j = i + 32765'i16
    if j > 32766'i16: symexTarget("hit")

proc cu8(a: int) =
  for i in countup(0'i8, 3'i8):
    let j = i + 125'i8
    if j > 126'i8: symexTarget("hit")

proc cd8(a: int) =
  for i in countdown(3'i8, 0'i8):
    let j = i + 125'i8
    if j > 126'i8: symexTarget("hit")

proc cu16Step(a: int) =
  for i in countup(0'i16, 9'i16, 3'i16):
    let j = i + 32765'i16
    if j > 32766'i16: symexTarget("hit")

proc dd32(a: int) =
  for i in 0'i32 .. 3'i32:
    let j = i + 2147483645'i32
    if j > 2147483646'i32: symexTarget("hit")

proc ddChar(a: int) =
  var n = 0
  for c in 'a' .. 'c':
    if ord(c) + 200 > 255: n += 1
  if n == 3 and a == 1: symexTarget("hit")

proc takes8(x: int8): int8 = x + 100'i8

proc ddArg(a: int) =
  var s = 0
  for i in 0'i8 .. 2'i8:
    s += int(takes8(i))
  if s == 303 and a == 1: symexTarget("hit")

proc ddNeg(a: int) =
  for i in -3'i8 .. 0'i8:
    if i - 126'i8 < -128'i8: symexTarget("hit")
  symexTarget("hit2")

proc ddOk(a: int) =
  var n = 0
  for i in 0'i8 .. 3'i8:
    n += int(i + 100'i8)
  if n == 406 and a == 1: symexTarget("hit")

suite "W3-z P18: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 318

const sc = cellKey(axConstruct, "for/counter/narrowSigned")

suite "W3-z P18: a signed narrow counter is its own type":
  test "int8 ..": discard pinExact(dd8, sc, tRaisedExn("OverflowDefect"))
  test "int8 ..<": discard pinExact(dd8Lt, sc, tRaisedExn("OverflowDefect"))
  test "int16 ..": discard pinExact(dd16, sc, tRaisedExn("OverflowDefect"))
  test "int8 countup": discard pinExact(cu8, sc, tRaisedExn("OverflowDefect"))
  test "int8 countdown": discard pinExact(cd8, sc, tRaisedExn("OverflowDefect"))
  test "int16 countup step": discard pinExact(cu16Step, sc, tRaisedExn("OverflowDefect"))
  test "int32 ..": discard pinExact(dd32, sc, tRaisedExn("OverflowDefect"))
  test "char": discard pinExact(ddChar, sc)
  test "passed to an int8 proc": discard pinExact(ddArg, sc)
  test "negative": discard pinExact(ddNeg, sc, tRaisedExn("OverflowDefect"))
  test "in range": discard pinExact(ddOk, sc)
