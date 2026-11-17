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
##
## Split (RFC-0016 INT-51) into three files so each compiles inside the CI
## ceiling: `tsymex_0016_k4c_math_int` (the integer routines and `ceilDiv`),
## `tsymex_0016_k4c_math_float` (the modelled float routines, the allowlisted
## float rows and the names std/math lacks) and `tsymex_0016_k4c_math_libm`
## (the declined float rows). Every pin of the one file is in exactly one of
## them.
import std/[unittest, math]
import nelli/symex
import nelli/smt/errorkind
import nelli/smt/admission
import ./s8cu_helpers

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
