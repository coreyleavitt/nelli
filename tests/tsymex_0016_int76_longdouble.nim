## RFC-0016 INT-76: a `c_longdouble` value in a routine's body.
##
## `c_longdouble` is the C target's `long double`: x87 80-bit extended under
## gcc and clang on x86-64, a 64-bit double under MSVC and on some ARM
## targets. Nim aliases it to `float64`, so its value is the target's, not
## Nim's (K2c STY-06, the `float128` type-class row: refused). Native (Nim
## 2.2.10, gcc x86-64, c and cpp): C's `sizeof(long double)` is 16 where
## Nim's `sizeof(c_longdouble)` is 8; Nim's arithmetic casts each operand to
## `double` (`(NF)(x) + (NF)(0.2)`), but a conversion stores the C value:
## `c_longdouble(k) == 9007199254740992.0` is false at `k = 2^53 + 1` (exact
## in the x87 64-bit mantissa), where a `float64` (and MSVC's `long double`)
## rounds it to 2^53 and the comparison holds.
##
## Red at a604b3c2 (walker 434): `var x: c_longdouble; if x == 0.0` is a
## `weInternalWalkerFault` (`eqBV`: `a.kind == b.kind`), and so are `!=`,
## `<` (`cmpBV`), a conversion `c_longdouble(k) == 3.0`, and a field of the
## type (`FieldDefect`); an initialised local was walked as an IEEE double,
## a trusted `sxSat` on a type whose value is the C target's. Found by
## INT-65's zero-value follow-up.
##
## Model: every site that makes a `c_longdouble` value (a declared local,
## initialised or not; an expression of the type: a conversion, a field
## read, arithmetic) declines `feUnsupportedParamType`, the parameter site's
## kind, and halts the path, so no read meets a value of another sort. An
## object with a field of the type has no zero (the field has no sort) and
## declines with the same kind. A path no execution takes never reaches the
## decline. `float` and `float32` locals are unaffected (pinned exact).
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

type I76Box = object
  v: c_longdouble
  n: int

proc i76Eq(k: int) =
  var x: c_longdouble
  if x == 0.0: symexTarget("hit")

proc i76Ne(k: int) =
  var x: c_longdouble
  if x != 0.0 and k == 1: symexTarget("hit")

proc i76Lt(k: int) =
  var x: c_longdouble
  if x < 1.0 and k == 1: symexTarget("hit")

proc i76Arith(k: int) =
  var x: c_longdouble = 1.5
  let y = x + 2.0
  if y > 3.0 and k == 1: symexTarget("hit")

proc i76Precision(k: int) =
  # sat as float64 (and under MSVC) at k = 2^53 + 1; unsat on an x87
  # target: the walk cannot know which
  let x = c_longdouble(k)
  if x == 9007199254740992.0 and k != 9007199254740992: symexTarget("hit")

proc i76Conv(k: int) =
  if c_longdouble(k) == 3.0: symexTarget("hit")

proc i76Field(k: int) =
  var o: I76Box
  if o.v == 0.0 and k == 1: symexTarget("hit")

proc i76FieldWrite(k: int) =
  var o: I76Box
  o.v = 2.0
  if k == 1: symexTarget("hit")

proc i76FieldOther(k: int) =
  # the object's zero has a field with no sort: the local declines even
  # when only its `int` field is used
  var o: I76Box
  o.n = k
  if o.n == 3: symexTarget("hit")

proc i76Unread(k: int) =
  var x: c_longdouble
  if k == 1: symexTarget("hit")

proc i76Infeasible(k: int) =
  # the local is on no path an execution takes: the decline is never
  # reached, so the verdict is exact
  if k == 7: symexTarget("hit")
  if k > 10 and k < 5:
    var x: c_longdouble = 1.0
    if x > 0.0: symexTarget("other")

proc i76FloatEq(k: int) =
  var x: float
  if x == 0.0 and k == 1: symexTarget("hit")

proc i76FloatArith(k: int) =
  var x: float = 1.5
  let y = x + 2.0
  if y > 3.0 and k == 1: symexTarget("hit")

proc i76FloatPrecision(k: int) =
  var x = 0.1
  let y = x + 0.2
  if y == 0.30000000000000004 and k == 1: symexTarget("hit")

proc i76Float32Lt(k: int) =
  var x: float32
  if x < 1.0 and k == 1: symexTarget("hit")

proc i76Float32Arith(k: int) =
  var x: float32 = 1.5
  let y = x + 2.0
  if y == 3.5'f32 and k == 1: symexTarget("hit")

proc i76Float32Unsat(k: int) =
  var x: float32
  if x != 0.0'f32 and k == 1: symexTarget("hit")

const ldCell = cellKey(axTypeClass, "float128")
const ldDomain = sampled([0, 1, 3, 7])

suite "INT-76: a c_longdouble value declines, never faults":
  test "an uninitialised local compared with `==` (the reproducer)":
    pinDecline(i76Eq, ldCell, feUnsupportedParamType,
               needle = "c_longdouble")
  test "`!=` and `<`":
    pinDecline(i76Ne, ldCell, feUnsupportedParamType, needle = "c_longdouble")
    pinDecline(i76Lt, ldCell, feUnsupportedParamType, needle = "c_longdouble")
  test "an initialised local, and a conversion whose value is the target's":
    pinDecline(i76Arith, ldCell, feUnsupportedParamType,
               needle = "c_longdouble")
    pinDecline(i76Precision, ldCell, feUnsupportedParamType,
               needle = "c_longdouble")
  test "a conversion to the type":
    pinDecline(i76Conv, ldCell, feUnsupportedParamType, needle = "c_longdouble")
  test "a field of the type, read and written":
    pinDecline(i76Field, ldCell, feUnsupportedParamType,
               needle = "c_longdouble")
    pinDecline(i76FieldWrite, ldCell, feUnsupportedParamType,
               needle = "c_longdouble")
  test "an unread local still declines (the zero has no sort)":
    pinDecline(i76Unread, ldCell, feUnsupportedParamType,
               needle = "c_longdouble")

  test "an object holding one, used only through its other field":
    pinDecline(i76FieldOther, ldCell, feUnsupportedParamType,
               needle = "c_longdouble")

suite "INT-76: a c_longdouble local on no feasible path is never reached":
  test "the verdict is exact":
    let r = pinExact(i76Infeasible, cellKey(axTypeClass, "int"),
                     domain = ldDomain)
    check r.status == sxSat

suite "INT-76: float and float32 locals with literals are exact":
  test "float":
    discard pinExact(i76FloatEq, cellKey(axTypeClass, "float"), domain = ldDomain)
    discard pinExact(i76FloatArith, cellKey(axTypeClass, "float"), domain = ldDomain)
    let r = pinExact(i76FloatPrecision, cellKey(axTypeClass, "float"),
                     domain = ldDomain)
    check r.status == sxSat
  test "float32":
    discard pinExact(i76Float32Lt, cellKey(axTypeClass, "float32"), domain = ldDomain)
    discard pinExact(i76Float32Arith, cellKey(axTypeClass, "float32"), domain = ldDomain)
    let r = pinExact(i76Float32Unsat, cellKey(axTypeClass, "float32"),
                     domain = ldDomain)
    check r.status == sxUnsat

suite "INT-76: walker version":
  test "version floor: INT-76 bumped the walker to 435":
    check parseInt(symexWalkerVersion) >= 435
