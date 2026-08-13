import std/unittest
import std/math
import std/sequtils
import nelli/symex

# Phase 16 A5 — model classify() + copySign(); nextafter stays unsupported.
#
# classify(x) lowers to a Z3 bitvector ordinal (svBV64, signed) via an
# ite-chain over Z3 FP predicates, matching Nim's FloatClass enum:
#   fcNormal=0, fcSubnormal=1, fcZero=2, fcNegZero=3, fcNan=4, fcInf=5, fcNegInf=6
#
# probeProto for "classify" returns svBV64 so enum-ordinal literals also lower
# to BV64 (F5-safety: keeps the comparison in QF_BVFP, not Int+BV+FP).
#
# copySign(x, y) returns a float of x's width with y's sign.
#
# nextafter: NOT available in Nim std/math (2.2.x) — no SUT can be written.
# The engine still routes any "nextafter" math call to feUnsupportedOp via
# the existing else-branch in lowerMathCall (Invariant 3, documented bound).
# See also: RFC DEVIATION note in tsymex_phase15_F6_float_math.nim.

# ---------------------------------------------------------------------------
# classify() SUTs
# ---------------------------------------------------------------------------

proc classifyIsNan(x: float) =
  ## classify(x) == fcNan iff x is NaN.
  if classify(x) == fcNan: symexTarget("classifyIsNan")

proc classifyNanContradiction(x: float) =
  ## isNaN(x) and classify(x) == fcNormal is unsatisfiable.
  if isNaN(x) and classify(x) == fcNormal: symexTarget("classifyNanContradiction")

proc classifyIsInf(x: float) =
  ## classify(x) == fcInf iff x is +Inf.
  if classify(x) == fcInf: symexTarget("classifyIsInf")

proc classifyIsNegInf(x: float) =
  ## classify(x) == fcNegInf iff x is -Inf.
  if classify(x) == fcNegInf: symexTarget("classifyIsNegInf")

proc classifyIsZero(x: float) =
  ## classify(x) == fcZero iff x is +0.0.
  if classify(x) == fcZero: symexTarget("classifyIsZero")

proc classifyIsNegZero(x: float) =
  ## classify(x) == fcNegZero iff x is -0.0.
  ## Z3: fp.isZero(-0.0)=true, fp.isNegative(-0.0)=true → ordinal 3.
  if classify(x) == fcNegZero: symexTarget("classifyIsNegZero")

proc classifyIsNormal(x: float) =
  ## classify(x) == fcNormal for an ordinary finite non-subnormal value.
  if classify(x) == fcNormal: symexTarget("classifyIsNormal")

proc classifyIsSubnormal(x: float) =
  ## classify(x) == fcSubnormal for a denormal value.
  if classify(x) == fcSubnormal: symexTarget("classifyIsSubnormal")

# ---------------------------------------------------------------------------
# copySign() SUTs
# ---------------------------------------------------------------------------

proc copySignNeg(x: float) =
  ## copySign(3.0, x) < 0.0 is sat when x is negative (sign taken from x).
  if copySign(3.0, x) < 0.0: symexTarget("copySignNeg")

proc copySignPos(x: float) =
  ## copySign(3.0, x) > 0.0 is sat when x is positive.
  if copySign(3.0, x) > 0.0: symexTarget("copySignPos")

# ---------------------------------------------------------------------------
# Suites
# ---------------------------------------------------------------------------

suite "symex Phase 16 A5 — classify() tracer bullet: fcNan":

  test "A5-1a: classify(x)==fcNan is sat (x can be NaN)":
    let r = symexFind(classifyIsNan, tLabel("classifyIsNan"))
    check r.status == sxSat

  test "A5-1b: isNaN(x) and classify(x)==fcNormal is unsat (contradiction)":
    let r = symexFind(classifyNanContradiction, tLabel("classifyNanContradiction"))
    check r.status == sxUnsat

suite "symex Phase 16 A5 — classify() infinities and zeros":

  test "A5-2a: classify(x)==fcInf is sat (+Inf is reachable)":
    let r = symexFind(classifyIsInf, tLabel("classifyIsInf"))
    check r.status == sxSat

  test "A5-2b: classify(x)==fcNegInf is sat (-Inf is reachable)":
    let r = symexFind(classifyIsNegInf, tLabel("classifyIsNegInf"))
    check r.status == sxSat

  test "A5-3a: classify(x)==fcZero is sat (+0.0 is reachable)":
    let r = symexFind(classifyIsZero, tLabel("classifyIsZero"))
    check r.status == sxSat

  test "A5-3b: classify(x)==fcNegZero is sat (-0.0 is reachable)":
    ## Z3 fp.isZero(−0.0)=true and fp.isNegative(−0.0)=true, so the ite-chain
    ## should witness −0.0 (ordinal 3) distinct from +0.0 (ordinal 2).
    let r = symexFind(classifyIsNegZero, tLabel("classifyIsNegZero"))
    check r.status == sxSat

suite "symex Phase 16 A5 — classify() normal and subnormal":

  test "A5-4a: classify(x)==fcNormal is sat (ordinary finite value reachable)":
    let r = symexFind(classifyIsNormal, tLabel("classifyIsNormal"))
    check r.status == sxSat

  test "A5-4b: classify(x)==fcSubnormal is sat (subnormal reachable)":
    let r = symexFind(classifyIsSubnormal, tLabel("classifyIsSubnormal"))
    check r.status == sxSat

suite "symex Phase 16 A5 — copySign()":

  test "A5-5a: copySign(3.0, x) < 0.0 is sat (sign from x, which can be negative)":
    let r = symexFind(copySignNeg, tLabel("copySignNeg"))
    check r.status == sxSat

  test "A5-5b: copySign(3.0, x) > 0.0 is sat (sign from x, which can be positive)":
    let r = symexFind(copySignPos, tLabel("copySignPos"))
    check r.status == sxSat
