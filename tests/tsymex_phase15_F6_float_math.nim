import std/unittest
import std/math
import proptest/symex

# Phase 15 — Cluster F cycle F6: std/math float ops + FP predicates.
# All modeled ops are Z3-FP-native (no transcendentals). Math/predicate calls
# in float-bearing SUTs lower through the iekMathCall path:
#   abs->fpAbs, sqrt->sqrt(rmRNE), min->fpMin, max->fpMax,
#   floor->roundToIntegral(rmRTN), ceil->rmRTP, round->rmRNE, trunc->rmRTZ,
#   signbit->isNegative, isNaN->isNaN predicate.
# Phase 16 A5 promoted classify/copySign to fully modeled (sxSat, not sxUnknown).
# The F6 tests for classify/copySign are updated to reflect this (see below).
# Deferred (Invariant 3 — never silent UNSAT): any unmodeled math.<name>
# (e.g. ln/sin/nextafter) -> sxUnknown with errors[0].kind == feUnsupportedOp.
#
# RFC DEVIATION: the RFC's predicate table assumed std/math exposes
# `isInf`/`isFinite`/`isNormal`/`nextafter`. Nim's std/math (2.2.x) ships
# `isNaN`, `signbit`, `classify`, `copySign` only — there are no `isInf`/
# `isFinite`/`isNormal`/`nextafter` procs to call, so those SUTs are not
# expressible. The runtime still models `isInf`/`isFinite`/`isNormal` (the
# nim-z3 wrappers `isInf`/`isFinite`/`isNormal` exist) for forward
# compatibility, but they are unreachable from a real Nim SUT and so untested
# here. The nim-z3 predicate wrappers are `isNaN`/`isNegative`/`isInf`/
# `isNormal`/`isFinite` (NOT the RFC's `fpIsNaN`/`fpIsNegative`/... names).

proc fSqrt(x: float) =
  if sqrt(x) > 2.0: symexTarget("sqrt")          # sat for x > 4.0
proc fFloor(x: float) =
  if floor(x) == 3.0: symexTarget("floor")       # sat for x in [3.0, 4.0)
proc fAbs(x: float) =
  if abs(x) == 5.0: symexTarget("abs")           # sat for x == ±5.0
proc fMin(x, y: float) =
  if min(x, y) == 1.0: symexTarget("min")        # sat
proc fMax(x, y: float) =
  if max(x, y) == 9.0: symexTarget("max")        # sat
proc fCeil(x: float) =
  if ceil(x) == 4.0: symexTarget("ceil")         # sat for x in (3.0, 4.0]
proc fRound(x: float) =
  if round(x) == 2.0: symexTarget("round")       # sat
proc fTrunc(x: float) =
  if trunc(x) == 2.0: symexTarget("trunc")       # sat for x in [2.0, 3.0)

proc fSignNeg(x: float) =
  if signbit(x): symexTarget("signneg")          # sat with a negative witness
proc fSignPos(x: float) =
  if not signbit(x): symexTarget("signpos")      # sat with a non-negative witness

proc fIsNaN(x: float) =
  if not isNaN(x) and x == x: symexTarget("notnan")   # sat (finite witness)

# float32 symmetry
proc fSqrt32(x: float32) =
  if sqrt(x) > 2.0'f32: symexTarget("sqrt32")    # sat

# Phase 16 A5: classify and copySign are now modeled (sxSat).
proc fClassify(x: float) =
  if classify(x) == fcNan: symexTarget("classify")
proc fCopySign(x, y: float) =
  if copySign(x, y) == 1.0: symexTarget("copysign")
# Deferred ops — must emit feUnsupportedOp (sxUnknown), never silent UNSAT.
proc fLog(x: float) =
  if ln(x) == 0.0: symexTarget("log")            # math.ln — unmodeled transcendental

suite "symex Phase 15 — F6 std/math float ops + FP predicates":

  test "sqrt(x) > 2.0 -> sat (witness x > 4.0)":
    check symexFind(fSqrt, tLabel("sqrt")).status == sxSat
  test "floor(x) == 3.0 -> sat (witness in [3.0, 4.0))":
    check symexFind(fFloor, tLabel("floor")).status == sxSat
  test "abs(x) == 5.0 -> sat":
    check symexFind(fAbs, tLabel("abs")).status == sxSat
  test "min(x, y) == 1.0 -> sat":
    check symexFind(fMin, tLabel("min")).status == sxSat
  test "max(x, y) == 9.0 -> sat":
    check symexFind(fMax, tLabel("max")).status == sxSat
  test "ceil(x) == 4.0 -> sat":
    check symexFind(fCeil, tLabel("ceil")).status == sxSat
  test "round(x) == 2.0 -> sat":
    check symexFind(fRound, tLabel("round")).status == sxSat
  test "trunc(x) == 2.0 -> sat":
    check symexFind(fTrunc, tLabel("trunc")).status == sxSat

  test "signbit(x) -> sat (negative witness)":
    check symexFind(fSignNeg, tLabel("signneg")).status == sxSat
  test "not signbit(x) -> sat (non-negative witness)":
    check symexFind(fSignPos, tLabel("signpos")).status == sxSat

  test "not isNaN(x) and x == x -> sat (finite witness), no errors":
    let r = symexFind(fIsNaN, tLabel("notnan"))
    check r.status == sxSat
    check r.errors.len == 0

  test "float32: sqrt(x) > 2.0 -> sat":
    check symexFind(fSqrt32, tLabel("sqrt32")).status == sxSat

  test "classify(x)==fcNan is sat (Phase 16 A5: classify now modeled)":
    ## Phase 16 A5: classify promoted from deferred to fully modeled (svBV64 ite-chain).
    let r = symexFind(fClassify, tLabel("classify"))
    check r.status == sxSat
  test "copySign(x, y)==1.0 is sat (Phase 16 A5: copySign now modeled)":
    ## Phase 16 A5: copySign promoted from deferred to modeled (ite over isNegative).
    let r = symexFind(fCopySign, tLabel("copysign"))
    check r.status == sxSat
  test "unmodeled math.ln emits feUnsupportedOp (sxUnknown)":
    let r = symexFind(fLog, tLabel("log"))
    check r.status == sxUnknown
    check r.errors[0].kind == feUnsupportedOp
    check r.errors[0].severity == sevError
