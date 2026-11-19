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
import nelli/smt/stdlib_rows
import nelli/smt/stdlib_models
import ./s8cu_helpers

const floats = sampled([-2.5, -0.0, 0.0, 0.5, 2.5, 9.0, 4.5])

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
