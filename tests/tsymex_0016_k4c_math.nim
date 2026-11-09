## RFC-0016 K4c (section 8.1), PRC-09: every routine of `std/math`'s pushed
## `checks: off` region (math.nim:157-1116) has a row of the stdlib-body axis.
##
##   * the integer routines are walked by body and carry their check-option
##     delta; each is pinned exact, and the delta both ways where it matters
##     (the user's `x - 1` raises in a checks-on build, the stdlib body is
##     unchecked and halts on the undefined overflow);
##   * `divmod` is an opaque call (a tuple-returning generic the walker does
##     not inline) and `ceilDiv` converts through unsigned types, whose range checks the push
##     turns off: a declined row, `feCheckOption`, naming its cell;
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
  test "math.ceilDiv is a declined row (unsigned conversions, range checks)":
    check native(sCeilDiv(7)) == "hit"
    let c = cellKey(axStdlibBody, "math.ceilDiv")
    pinDecline(sCeilDiv, c, feCheckOption, needle = render(c))

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
