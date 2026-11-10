## RFC-0016 K4c (section 8.1), PRC-09: every routine of `std/math`'s pushed
## `checks: off` region (math.nim:157-1116) has a row of the stdlib-body axis.
##
##   * the integer routines are walked by body and carry their check-option
##     delta; each is pinned exact, and the delta both ways where it matters
##     (the user's `x - 1` raises in a checks-on build, the stdlib body is
##     unchecked and halts on the undefined overflow);
##   * `divmod` is an opaque call (a tuple-returning generic the walker does
##     not inline): a declined row, `feOpaqueCallUnmodelled`, naming its cell;
##   * `ceilDiv` is lowered by name: exact inside its precondition; outside it
##     the asserts run or not by the options of its first instantiation, which
##     the walker cannot see, so such a path declines `feCheckOption`;
##   * a float-first call is lowered by name, never walked: the modelled
##     routines are pinned exact, and every other routine of the region is a
##     declined row (`feUnsupportedOp`) naming its cell, one pin each.
import std/[unittest, math, options]
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import nelli/smt/stdlib_rows
import nelli/smt/stdlib_models
import ./s8cu_helpers

const smallInts = sampled([-7, -5, -3, -1, 0, 1, 2, 3, 5, 7, 8, 9])
const floats = sampled([-2.5, -0.0, 0.0, 0.5, 2.5, 9.0, 4.5])

proc sNextPow2(a: int) =
  if nextPowerOfTwo(a) == 8 and a == 5: symexTarget("hit")
proc sNextPow2Min(a: int) =
  if nextPowerOfTwo(a) == 1 and a == low(int): symexTarget("hit")
proc sUserDecMin(a: int) =
  if a - 1 == 0 and a == low(int): symexTarget("hit")
proc sEuclMod(a: int) =
  if euclMod(a, 3) == 2 and a == -7: symexTarget("hit")
proc sEuclModZero(a, b: int) =
  if euclMod(a, b) == 1 and b == 0: symexTarget("hit")
proc sDivmod(a: int) =
  let (q, r) = divmod(a, 3)
  if q == 2 and r == 1 and a == 7: symexTarget("hit")
proc sSgn(a: int) =
  if sgn(a) == -1 and a == -5: symexTarget("hit")
proc sCeilDiv(a: int) =
  if ceilDiv(a, 3) == 3 and a == 7: symexTarget("hit")

# RFC-0016 PRC-09 `math.ceilDiv` (math.nim:925) computes
# `((x.UT + (y.UT - 1)) div y.UT).T`, a same-width reinterpretation and
# wrapping unsigned arithmetic, after asserting its precondition. It is a
# generic: its asserts follow `assertions` at the site that first
# instantiates it, not math.nim's `checks: off` push, so in this (debug)
# module they run. Lowered by name (`parseCeilDiv`): exact inside the precondition, a
# path outside it declined. One SUT per width; `b > 2` keeps the witness off
# the trivial divisors.
proc cdI8(a, b: int8) =
  if a > 0 and b > 2 and ceilDiv(a, b) == 3: symexTarget("hit")
proc cdI16(a, b: int16) =
  if a > 0 and b > 2 and ceilDiv(a, b) == 3: symexTarget("hit")
proc cdI32(a, b: int32) =
  if a > 0 and b > 2 and ceilDiv(a, b) == 3: symexTarget("hit")
proc cdI64(a: int) =
  if a > 0 and ceilDiv(a, 7) == 3: symexTarget("hit")
proc cdU8(a, b: uint8) =
  if a > 0 and b > 2 and ceilDiv(a, b) == 3: symexTarget("hit")
proc cdU16(a, b: uint16) =
  if a > 0 and b > 2 and ceilDiv(a, b) == 3: symexTarget("hit")
proc cdU32(a, b: uint32) =
  if a > 0 and b > 2 and ceilDiv(a, b) == 3: symexTarget("hit")
proc cdU64(a: uint64) =
  if a > 0 and ceilDiv(a, 7'u64) == 3: symexTarget("hit")
# Within the precondition it is the ceiling: no input breaks the law.
proc cdI32Law(a: int32) =
  ## A constant divisor keeps the query linear.
  if a >= 0:
    let q = ceilDiv(a, 7'i32).int64
    if q * 7 < a.int64 or (q - 1) * 7 >= a.int64: symexTarget("hit")
proc cdU8Law(a, b: uint8) =
  if b > 0 and a.int + b.int - 1 <= 255:
    let q = ceilDiv(a, b).int
    if q * b.int < a.int or (q - 1) * b.int >= a.int: symexTarget("hit")
# The unsigned precondition's boundary, `x + y - 1 <= high(T)`: 254 is the
# last `a` it admits for `b == 2`; at 255 the sum wraps to 0.
proc cdU8Edge(a: uint8) =
  if a >= 254 and ceilDiv(a, 2'u8) == 127: symexTarget("hit")
proc cdU8Wrap(a: uint8) =
  if a > 0 and ceilDiv(a, 2'u8) == 0: symexTarget("hit")
# Outside the precondition: the assert, or with it off the wrapped value.
proc cdNeg(a: int) =
  if a < 0 and a > -10 and ceilDiv(a, 3) == 6148914691236517203:
    symexTarget("hit")
proc cdI8NegDivisor(a, b: int8) =
  if a == 7 and b < 0 and ceilDiv(a, b) == 0 and b == -2: symexTarget("hit")
proc cdI8Min(a: int8) =
  if a < 0 and ceilDiv(a, 1'i8) == -128: symexTarget("hit")
# `y == 0`: the assert, or with it off the unsigned division by zero.
proc cdZeroU(a, b: uint32) =
  if ceilDiv(a, b) == 1 and b == 0: symexTarget("hit")
proc cdZeroI(a, b: int) =
  if ceilDiv(a, b) == 1 and b == 0: symexTarget("hit")

const
  cdKey = cellKey(axStdlibBody, "math.ceilDiv")
  i8s = sampled([low(int8), -2'i8, -1, 0, 1, 2, 3, 7, 9, high(int8)])
  i16s = sampled([low(int16), -1'i16, 0, 1, 3, 7, 9, high(int16)])
  i32s = sampled([low(int32), -1'i32, 0, 1, 2, 3, 7, 9, high(int32) - 1,
                  high(int32)])
  u8s = sampled([0'u8, 1, 2, 3, 7, 9, 127, 128, 253, 254, 255])
  u16s = sampled([0'u16, 1, 3, 7, 9, high(uint16)])
  u32s = sampled([0'u32, 1, 3, 7, 9, high(uint32)])
  u64s = sampled([0'u64, 1, 15, 21, 22, high(uint64)])

template decided(body: untyped) =
  ## A verdict is decided only on a verified build row; cpp under Z3 4.13.4
  ## has none by design (`feHostUnadmitted`).
  if hostAdmission().isSome:
    skipUnadmitted()
  else:
    body

suite "K4c PRC-09: the integer routines are walked, with their delta":
  test "math.nextPowerOfTwo":
    let r = pinExact(sNextPow2, cellKey(axStdlibBody, "math.nextPowerOfTwo"),
                     domain = smallInts)
    check r.status == sxSat
  test "math.nextPowerOfTwo: user `x - 1` raises, the body is unchecked":
    check native(sUserDecMin(low(int))) == "OverflowDefect"
    let u = symexFind(sUserDecMin, tLabel("hit"))
    check u.status == sxRaised
    pinDecline(sNextPow2Min, cellKey(axStdlibBody, "math.nextPowerOfTwo"),
               ubSignedOverflow)
    check symexFind(sNextPow2Min, tLabel("hit")).status != sxRaised
  test "math.euclMod":
    let r = pinExact(sEuclMod, cellKey(axStdlibBody, "math.euclMod"),
                     domain = smallInts)
    check r.status == sxSat
  test "math.euclMod: the zero divisor is undefined, not a raise":
    pinDecline(sEuclModZero, cellKey(axStdlibBody, "math.euclMod"),
               ubSignedDivZero)
    check symexFind(sEuclModZero, tLabel("hit")).status != sxRaised
  test "math.divmod is a declined row (a tuple-returning generic is opaque)":
    let c = cellKey(axStdlibBody, "math.divmod")
    pinDecline(sDivmod, c, feOpaqueCallUnmodelled, needle = render(c))
  test "math.sgn (the body trips nothing)":
    let r = pinExact(sSgn, cellKey(axStdlibBody, "math.sgn"),
                     domain = smallInts)
    check r.status == sxSat

suite "PRC-09: math.ceilDiv is lowered by name, as compiled":
  test "native: inside the precondition it is the ceiling":
    check ceilDiv(7, 3) == 3
    check ceilDiv(6, 3) == 2
    check ceilDiv(0, 3) == 0
    check ceilDiv(254'u8, 2'u8) == 127

  test "native: outside it the assert runs (instantiated here, debug)":
    expect AssertionDefect: discard ceilDiv(255'u8, 2'u8)
    expect AssertionDefect: discard ceilDiv(-7, 3)
    expect AssertionDefect: discard ceilDiv(7'i8, -2'i8)
    expect AssertionDefect: discard ceilDiv(-128'i8, 1'i8)
    expect AssertionDefect: discard ceilDiv(1'u32, 0'u32)

  test "the row is admitted at the call, not walked by body":
    check admitStdlibBody("math.ceilDiv", ssNameCall).admitted
    check not admitStdlibBody("math.ceilDiv", ssBodyWalk).admitted

  test "exact at every width":
    decided:
      check native(sCeilDiv(7)) == "hit"
      check pinExact(sCeilDiv, cdKey, domain = smallInts).status == sxSat
      check pinExact(cdI8, cdKey, domain = i8s).status == sxSat
      check pinExact(cdI16, cdKey, domain = i16s).status == sxSat
      check pinExact(cdI32, cdKey, domain = i32s).status == sxSat
      check pinExact(cdI64, cdKey, domain = smallInts).status == sxSat
      check pinExact(cdU8, cdKey, domain = u8s).status == sxSat
      check pinExact(cdU16, cdKey, domain = u16s).status == sxSat
      check pinExact(cdU32, cdKey, domain = u32s).status == sxSat
      check pinExact(cdU64, cdKey, domain = u64s).status == sxSat

  test "within the precondition it is the ceiling":
    decided:
      check pinExact(cdI32Law, cdKey, domain = i32s).status == sxUnsat
      check pinExact(cdU8Law, cdKey, domain = u8s).status == sxUnsat

  test "the unsigned precondition's boundary":
    decided:
      check native(cdU8Edge(254)) == "hit"
      let e = pinExact(cdU8Edge, cdKey, domain = u8s)
      check e.status == sxSat
      check native(cdU8Wrap(255)) == "AssertionDefect"
      pinDecline(cdU8Wrap, cdKey, feCheckOption, needle = render(cdKey))

  test "outside the precondition a path declines, naming the cell":
    decided:
      check native(cdNeg(-7)) == "AssertionDefect"
      pinDecline(cdNeg, cdKey, feCheckOption, needle = render(cdKey))
      check native(cdI8NegDivisor(7, -2)) == "AssertionDefect"
      pinDecline(cdI8NegDivisor, cdKey, feCheckOption, needle = render(cdKey))
      check native(cdI8Min(-128)) == "AssertionDefect"
      pinDecline(cdI8Min, cdKey, feCheckOption, needle = render(cdKey))

  test "y == 0 is outside the precondition: declined":
    decided:
      check native(cdZeroU(1, 0)) == "AssertionDefect"
      pinDecline(cdZeroU, cdKey, feCheckOption, needle = render(cdKey))
      check native(cdZeroI(1, 0)) == "AssertionDefect"
      pinDecline(cdZeroI, cdKey, feCheckOption, needle = render(cdKey))

proc fSqrt(a: float) =
  if sqrt(a) == 3.0 and a == 9.0: symexTarget("hit")
proc fFloor(a: float) =
  if floor(a) == -3.0 and a == -2.5: symexTarget("hit")
proc fCeil(a: float) =
  if ceil(a) == -2.0 and a == -2.5: symexTarget("hit")
proc fTrunc(a: float) =
  if trunc(a) == -2.0 and a == -2.5: symexTarget("hit")
proc fRound(a: float) =
  if round(a) == 3.0 and a == 2.5: symexTarget("hit")
proc fRoundEven(a: float) =
  if round(a) == 4.0 and a == 4.5: symexTarget("hit")
proc fSignbit(a: float) =
  if signbit(a) and a == 0.0: symexTarget("hit")
proc fIsNaN(a: float) =
  if isNaN(a): symexTarget("hit")
proc fCopySign(a, b: float) =
  if copySign(a, b) == -2.5 and a == 2.5: symexTarget("hit")
proc fClassify(a: float) =
  if classify(a) == fcNegZero: symexTarget("hit")
proc fRoundPlaces(a: float) =
  if round(a, 1) == 2.5 and a == 2.5: symexTarget("hit")

template floatExact(sut: untyped; key: static string) =
  test "math." & key:
    let r = pinExact(sut, cellKey(axStdlibBody, "math." & key),
                     domain = floats)
    check r.status == sxSat

suite "K4c PRC-09: the modelled float routines are pinned exact":
  floatExact(fSqrt, "sqrt")
  floatExact(fFloor, "floor")
  floatExact(fCeil, "ceil")
  floatExact(fTrunc, "trunc")
  floatExact(fRound, "round")
  floatExact(fSignbit, "signbit")
  floatExact(fIsNaN, "isNaN")
  floatExact(fCopySign, "copySign")
  floatExact(fClassify, "classify")
  test "math.round: ties go away from zero (4.5 rounds to 5.0, not 4.0)":
    check native(fRoundEven(4.5)) != "hit"
    let r = pinExact(fRoundEven, cellKey(axStdlibBody, "math.round"),
                     domain = floats)
    check r.status == sxUnsat
  test "math.round/places is a declined facet":
    let c = cellKey(axStdlibBody, "math.round/places")
    pinDecline(fRoundPlaces, c, feUnsupportedOpAborted, needle = render(c))

template declined1(sut: untyped; name: static string; expr: untyped) =
  proc sut(a {.inject.}: float) =
    if expr > 0.5: symexTarget("hit")
  test "math." & name:
    let c = cellKey(axStdlibBody, "math." & name)
    pinDecline(sut, c, feUnsupportedOpAborted, needle = render(c))

template declined2(sut: untyped; name: static string; expr: untyped) =
  proc sut(a {.inject.}, b {.inject.}: float) =
    if expr > 0.5: symexTarget("hit")
  test "math." & name:
    let c = cellKey(axStdlibBody, "math." & name)
    pinDecline(sut, c, feUnsupportedOpAborted, needle = render(c))

suite "K4c PRC-09: a libm routine is a declined row":
  declined1(dCbrt, "cbrt", cbrt(a))
  declined1(dLn, "ln", ln(a))
  declined1(dLog10, "log10", log10(a))
  declined1(dLog2, "log2", log2(a))
  declined1(dExp, "exp", exp(a))
  declined1(dSin, "sin", sin(a))
  declined1(dCos, "cos", cos(a))
  declined1(dTan, "tan", tan(a))
  declined1(dSinh, "sinh", sinh(a))
  declined1(dCosh, "cosh", cosh(a))
  declined1(dTanh, "tanh", tanh(a))
  declined1(dArcsin, "arcsin", arcsin(a))
  declined1(dArccos, "arccos", arccos(a))
  declined1(dArctan, "arctan", arctan(a))
  declined2(dArctan2, "arctan2", arctan2(a, b))
  declined1(dArcsinh, "arcsinh", arcsinh(a))
  declined1(dArccosh, "arccosh", arccosh(a))
  declined1(dArctanh, "arctanh", arctanh(a))
  declined2(dHypot, "hypot", hypot(a, b))
  declined2(dPow, "pow", pow(a, b))
  declined1(dErf, "erf", erf(a))
  declined1(dErfc, "erfc", erfc(a))
  declined1(dGamma, "gamma", gamma(a))
  declined1(dLgamma, "lgamma", lgamma(a))

suite "K4c PRC-09: a reciprocal or composition is a declined row":
  declined2(dLog, "log", log(a, b))
  declined1(dCot, "cot", cot(a))
  declined1(dSec, "sec", sec(a))
  declined1(dCsc, "csc", csc(a))
  declined1(dCoth, "coth", coth(a))
  declined1(dSech, "sech", sech(a))
  declined1(dCsch, "csch", csch(a))
  declined1(dArccot, "arccot", arccot(a))
  declined1(dArcsec, "arcsec", arcsec(a))
  declined1(dArccsc, "arccsc", arccsc(a))
  declined1(dArccoth, "arccoth", arccoth(a))
  declined1(dArcsech, "arcsech", arcsech(a))
  declined1(dArccsch, "arccsch", arccsch(a))

suite "K4c PRC-09: decompositions and float comparisons are declined rows":
  declined1(dFrexp, "frexp", frexp(a).frac)
  declined1(dSplitDecimal, "splitDecimal", splitDecimal(a).floatpart)
  declined1(dDegToRad, "degToRad", degToRad(a))
  declined1(dRadToDeg, "radToDeg", radToDeg(a))
  declined2(dMod, "mod", a mod b)

proc dAlmostEq(a, b: float) =
  if almostEqual(a, b): symexTarget("hit")
suite "K4c PRC-09: almostEqual":
  test "math.almostEqual":
    let c = cellKey(axStdlibBody, "math.almostEqual")
    pinDecline(dAlmostEq, c, feUnsupportedOpAborted, needle = render(c))

suite "K4c PRC-09: the modelled names agree with the lowering":
  test "the modelled float names are rows admitted at ssFloatCall":
    for n in ["sqrt", "floor", "ceil", "trunc", "round", "signbit", "isNaN",
              "copySign", "classify"]:
      check n in mathFpModeledOps
      check admitStdlibBody("math." & n, ssFloatCall).admitted
  test "a math name the lowering models has an admitted row, or none":
    for n in mathFpModeledOps:
      if stdlibAxis.hasRow("math." & n):
        check admitStdlibBody("math." & n, ssFloatCall).admitted

# --- W3-z E2b: the allowlisted float rows, pinned exact ----------------------
#
# `abs`, `min` and `max` are std/system routines. `isInf`, `isFinite` and
# `isNormal` are NOT in std/math on this toolchain (see the `compiles` facts
# below), so their rows are never cells; a SUT routine of that name is a user
# routine, walked as its own body (tsymex_0016_p10_floatnames).
# `toFloat32`/`toFloat64` are the lowering's names for `float32(x)` and
# `float(x)` on a float operand (dsl_parser `convertFloatWidth`), not routines.
const
  narrow = sampled([-2.5'f32, -0.0'f32, 0.0'f32, 0.5'f32, 2.5'f32, 9.0'f32])

proc fAbs(a: float) =
  if abs(a) == 2.5 and a < 0.0: symexTarget("hit")
proc fMin(a, b: float) =
  if min(a, b) == -2.5 and b == 0.5: symexTarget("hit")
proc fMax(a, b: float) =
  if max(a, b) == 2.5 and b == 0.5: symexTarget("hit")

proc fTo32Exact(a: float) =
  if float32(a) == 2.5'f32 and a == 2.5: symexTarget("hit")
proc fTo64(a: float32) =
  if float(a) == 2.5 and a == 2.5'f32: symexTarget("hit")

suite "W3-z E2b: the allowlisted float rows are pinned exact":
  test "math.abs":
    check pinExact(fAbs, cellKey(axStdlibBody, "math.abs"),
                   domain = floats).status == sxSat
  test "math.min":
    check pinExact(fMin, cellKey(axStdlibBody, "math.min"),
                   domain = floats).status == sxSat
  test "math.max":
    check pinExact(fMax, cellKey(axStdlibBody, "math.max"),
                   domain = floats).status == sxSat
  test "math.toFloat32 (float32(x) on a float operand)":
    check pinExact(fTo32Exact, cellKey(axStdlibBody, "math.toFloat32"),
                   domain = floats).status == sxSat
  test "math.toFloat64 (float(x) on a float32 operand)":
    check pinExact(fTo64, cellKey(axStdlibBody, "math.toFloat64"),
                   domain = narrow).status == sxSat

suite "W3-z P10: math.isInf/isFinite/isNormal are not in std/math here":
  test "the three are never cells, nrPlatform":
    var x = 1.5
    pinNever(cellKey(axStdlibBody, "math.isInf"), not compiles(isInf(x)),
             "std/math (Nim 2.2.10) has no isInf")
    pinNever(cellKey(axStdlibBody, "math.isFinite"), not compiles(isFinite(x)),
             "std/math (Nim 2.2.10) has no isFinite")
    pinNever(cellKey(axStdlibBody, "math.isNormal"), not compiles(isNormal(x)),
             "std/math (Nim 2.2.10) has no isNormal")
    for n in ["isInf", "isFinite", "isNormal"]:
      check not admitFloatCall(n, 1).admitted
      check n notin mathFpModeledOps

suite "W3-z E2b: math.nextafter is not in std/math here":
  test "math.nextafter is a never cell, nrPlatform":
    var x = 1.5
    let named = compiles(nextafter(x, 2.0))
    pinNever(cellKey(axStdlibBody, "math.nextafter"), not named,
             "std/math (Nim 2.2.10) has no nextafter: compiles(nextafter(x, y)) is " &
             $named)
    check not admitFloatCall("nextafter", 2).admitted
