import std/unittest
import std/math
import proptest/symex

# Phase 15 — Cluster F cycle F7: eval-side bit-exact float witness extraction.
# Replaces the F1 extractLeaf stub: when Z3 returns a SAT model, svFloat32 /
# svFloat64 SymVals are evaluated through nim-z3's evalFloat64Opt /
# evalFloat32Opt (with modelCompletion = true) into new RawWitness float
# tables, exposed to callers as concrete `r.witness[0]` values. The DoD is
# that special values (NaN, ±Inf) and ordinary numerals round-trip exactly.

proc fPi(x: float) =
  if x == 3.14: symexTarget("pi")             # x == 3.14 exactly
proc fNan(x: float) =
  if not (x == x): symexTarget("nan")         # satisfied only by NaN
proc fPosInf(x: float) =
  if x > 0.0 and 1.0 / x == 0.0: symexTarget("posinf")   # only +Inf
proc fNegInf(x: float) =
  if x < 0.0 and 1.0 / x == 0.0: symexTarget("neginf")   # only -Inf

proc fPi32(x: float32) =
  if x == 3.14'f32: symexTarget("pi32")       # float32 numeral round-trip
proc fNan32(x: float32) =
  if not (x == x): symexTarget("nan32")       # float32 NaN
proc fPosInf32(x: float32) =
  if x > 0.0'f32 and 1.0'f32 / x == 0.0'f32: symexTarget("posinf32")

suite "symex Phase 15 — F7 float witness extraction":

  test "float extraction: witness bit-pattern round-trip for float64":
    let r = symexFind(fPi, tLabel("pi"))
    check r.status == sxSat
    check r.witness[0] == 3.14          # exact float64 equality, not approximate

  test "float extraction: NaN witness extracted and round-tripped":
    let r = symexFind(fNan, tLabel("nan"))
    check r.status == sxSat
    check classify(r.witness[0]) == fcNan

  test "float extraction: +Inf witness extracted correctly":
    let r = symexFind(fPosInf, tLabel("posinf"))
    check r.status == sxSat
    check classify(r.witness[0]) == fcInf

  test "float extraction: -Inf witness extracted correctly":
    let r = symexFind(fNegInf, tLabel("neginf"))
    check r.status == sxSat
    check classify(r.witness[0]) == fcNegInf

  test "float32 extraction: witness round-trip at reduced precision":
    let r = symexFind(fPi32, tLabel("pi32"))
    check r.status == sxSat
    check r.witness[0] == 3.14'f32

  test "float32 extraction: NaN witness extracted and round-tripped":
    let r = symexFind(fNan32, tLabel("nan32"))
    check r.status == sxSat
    check classify(float(r.witness[0])) == fcNan

  test "float32 extraction: +Inf witness extracted correctly":
    let r = symexFind(fPosInf32, tLabel("posinf32"))
    check r.status == sxSat
    check classify(float(r.witness[0])) == fcInf
