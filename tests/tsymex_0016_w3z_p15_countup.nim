## RFC-0016 W3-z P15: `countup(a, b[, step])` and `countdown(a, b[, step])`
## over an `int`-like counter are modelled by the `for` arm that walks `..`,
## not by the stdlib body (generic over `T`, stepping with `cast[T](res)`,
## which the walker does not support). Each pin is differential: a witness is
## replayed natively, an `sxUnsat` is checked against the whole domain.
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

type Color = enum cRed, cGreen, cBlue, cBlack

proc sUp(a: int) =
  var n = 0
  for i in countup(1, 4): n += i
  if n == 10 and a == 1: symexTarget("hit")

proc sDown(a: int) =
  var n = 0
  for i in countdown(4, 1): n = n * 2 + i
  if n == 26 and a == 1: symexTarget("hit")

proc sUpSym(a: int) =
  var n = 0
  for i in countup(0, a and 7): n += i
  if n == 6 and a > 0: symexTarget("hit")

proc sUpSymLo(a: int) =
  var n = 0
  for i in countup(a and 7, 7): n += 1
  if n == 3: symexTarget("hit")

proc sUpStep2(a: int) =
  var n = 0
  for i in countup(0, a and 15, 2): n += i
  if n == 12 and a >= 0: symexTarget("hit")

proc sUpStep3(a: int) =
  var n = 0
  for i in countup(1, 10, 3): n = n * 10 + i
  if n == 14710 and a == 1: symexTarget("hit")

proc sDownStep(a: int) =
  var n = 0
  for i in countdown(10, 1, 3): n = n * 100 + i
  if n == 10070401 and a == 1: symexTarget("hit")

proc sDownSym(a: int) =
  var n = 0
  for i in countdown(a and 3, 0): n += i
  if n == 6 and a > 0: symexTarget("hit")

proc sEmptyUp(a: int) =
  var n = 0
  for i in countup(5, 1): n += 1
  if n == 0 and a == 1: symexTarget("hit")

proc sEmptyDown(a: int) =
  var n = 0
  for i in countdown(1, 5, 2): n += 1
  if n == 0 and a == 1: symexTarget("hit")

proc sBreak(a: int) =
  var n = 0
  for i in countup(1, 10):
    if i == a and a > 2: break
    n += i
  if n == 6 and a == 4: symexTarget("hit")

proc sContinue(a: int) =
  var n = 0
  for i in countup(1, 6, 2):
    if i == 3: continue
    n += i
  if n == 6 and a == 1: symexTarget("hit")

proc sStepVar(a: int) =
  var n = 0
  for i in countup(1, 10, a): n += 1
  if n == 4 and a == 3: symexTarget("hit")

proc sStepRaise(a: int) =
  for i in countup(1, 3, a):
    discard
  symexTarget("hit")

proc sBoundVar(a: int) =
  # a variable bound is the inlined iterator's parameter itself: the body
  # moving `m` moves the bound (2 iterations, not 3)
  var m = 3
  var n = 0
  for i in countup(1, m):
    m -= 1
    n += 1
  if n == 2 and a == 1: symexTarget("hit")

proc sBoundExpr(a: int) =
  # any other expression is evaluated once, into a temporary
  var m = 3
  var n = 0
  for i in countup(1, m + 0):
    m -= 1
    n += 1
  if n == 3 and a == 1: symexTarget("hit")

proc sOverflow(a: int) =
  for i in countup(high(int) - 1, high(int)):
    discard
  symexTarget("hit")

proc sEnum(a: int) =
  var n = 0
  for c in countup(cRed, cBlue): n += ord(c) + 1
  if n == 6 and a == 1: symexTarget("hit")

proc sEnumDown(a: int) =
  var n = 0
  for c in countdown(cBlack, cRed, 2): n = n * 10 + ord(c)
  if n == 31 and a == 1: symexTarget("hit")

proc sChar(a: int) =
  var n = 0
  for c in countup('a', 'd'): n += ord(c) - 96
  if n == 10 and a == 1: symexTarget("hit")

proc sCharDown(a: int) =
  var n = 0
  for c in countdown('e', 'a', 2): n = n * 10 + ord(c) - 96
  if n == 531 and a == 1: symexTarget("hit")

proc sInt8(a: int) =
  var n = 0
  for i in countup(1'i8, 4'i8): n += int(i)
  if n == 10 and a == 1: symexTarget("hit")

proc sInt64(a: int) =
  var n = 0'i64
  for i in countdown(4'i64, 1'i64): n += i
  if n == 10'i64 and a == 1: symexTarget("hit")

proc sUnsatLoop(a: int) =
  var n = 0
  for i in countup(1, 4): n += i
  if n == 11: symexTarget("hit")

const up = cellKey(axConstruct, "for/countup")
const dn = cellKey(axConstruct, "for/countdown")

suite "W3-z P15: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 316

suite "W3-z P15: countup":
  test "literal bounds": discard pinExact(sUp, up)
  test "symbolic upper bound": discard pinExact(sUpSym, up)
  test "symbolic lower bound": discard pinExact(sUpSymLo, up)
  test "step 2": discard pinExact(sUpStep2, up)
  test "step 3": discard pinExact(sUpStep3, up)
  test "empty": discard pinExact(sEmptyUp, up)
  test "break": discard pinExact(sBreak, up)
  test "continue": discard pinExact(sContinue, up)
  test "a variable step": discard pinExact(sStepVar, up)
  test "a step below 1 raises RangeDefect":
    discard pinExact(sStepRaise, up, tRaisedExn("RangeDefect"))
  test "a variable bound is read each iteration": discard pinExact(sBoundVar, up)
  test "an expression bound is read once": discard pinExact(sBoundExpr, up)
  test "stepping past high(int) raises OverflowDefect":
    discard pinExact(sOverflow, up, tRaisedExn("OverflowDefect"))
  test "enum": discard pinExact(sEnum, up)
  test "char": discard pinExact(sChar, up)
  test "int8": discard pinExact(sInt8, up)
  test "unsat": discard pinExact(sUnsatLoop, up)

suite "W3-z P15: countdown":
  test "literal bounds": discard pinExact(sDown, dn)
  test "step": discard pinExact(sDownStep, dn)
  test "symbolic bound": discard pinExact(sDownSym, dn)
  test "empty": discard pinExact(sEmptyDown, dn)
  test "enum": discard pinExact(sEnumDown, dn)
  test "char": discard pinExact(sCharDown, dn)
  test "int64": discard pinExact(sInt64, dn)
