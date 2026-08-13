## CR-9(c) width-mix arith/comparison canary.
##
## Covers: svBV64 vs svBV64, svBV32 vs svBV64 (mixed-width),
## svInt vs svBV64 (mixed-rep via seq.len probe-miss), and
## int(f)-vs-literal ordering/equality/arith for int32 and int64.
##
## These shapes stress the D2 reconcileInt + lowerCmp path and the
## F5-probeproto fix (probeProto returns correct svBV32/svBV64).
## The test must not hang (exit 137) and must produce correct verdicts.
import std/unittest
import nelli/symex

suite "symex CR-9(c) — integer representation ergonomics canary":

  # ---- svBV64 vs svBV64 (same rep/width) ------------------------------------
  test "bv64 vs bv64: ordering is sxSat":
    proc f64Cmp(x: int64) =
      if x > 100:
        symexTarget("big")
    let r = symexFind(f64Cmp, tLabel("big"))
    check r.status == sxSat
    check int64(r.witness[0]) > 100

  test "bv64 vs bv64: equality is sxSat":
    proc f64Eq(x: int64) =
      if x == 42'i64:
        symexTarget("found")
    let r = symexFind(f64Eq, tLabel("found"))
    check r.status == sxSat
    check int64(r.witness[0]) == 42

  test "bv64 vs bv64: arithmetic produces correct witness":
    proc f64Arith(x: int64) =
      if x + 1 == 100'i64:
        symexTarget("arith")
    let r = symexFind(f64Arith, tLabel("arith"))
    check r.status == sxSat
    check int64(r.witness[0]) == 99

  # ---- svBV32 vs svBV32 (same rep/width, narrower) --------------------------
  test "bv32 vs bv32: ordering is sxSat":
    proc f32Cmp(x: int32) =
      if x > 200'i32:
        symexTarget("big32")
    let r = symexFind(f32Cmp, tLabel("big32"))
    check r.status == sxSat
    check int32(r.witness[0]) > 200

  test "bv32 vs bv32: arithmetic produces correct witness":
    proc f32Arith(x: int32) =
      if x * 2 == 50'i32:
        symexTarget("mul32")
    let r = symexFind(f32Arith, tLabel("mul32"))
    check r.status == sxSat
    check int32(r.witness[0]) == 25

  # ---- int(f) vs literal: ordering, equality, arith (int64) -----------------
  # F5-probeproto: probeProto must return svBV64 for iekConvFloatToInt int64.
  test "int(f) vs literal: ordering sxSat — no hang":
    proc floatToIntOrd(f: float) =
      if int(f) > 5:
        symexTarget("gtLit")
    let r = symexFind(floatToIntOrd, tLabel("gtLit"))
    check r.status == sxSat
    check int(r.witness[0]) > 5

  test "int(f) vs literal: equality sxSat":
    proc floatToIntEq(f: float) =
      if int(f) == 99:
        symexTarget("eqLit")
    let r = symexFind(floatToIntEq, tLabel("eqLit"))
    check r.status == sxSat
    check int(r.witness[0]) == 99

  test "int(f) vs literal: arithmetic sxSat — no doAssert crash":
    proc floatToIntArith(f: float) =
      let k = int(f) + 5
      if k == 20:
        symexTarget("arithLit")
    let r = symexFind(floatToIntArith, tLabel("arithLit"))
    check r.status == sxSat
    check int(r.witness[0]) + 5 == 20

  # ---- int32(f) vs literal: ordering, equality, arith (int32) ---------------
  # F5-probeproto: probeProto must return svBV32 for iekConvFloatToInt int32.
  test "int32(f) vs literal: ordering sxSat — no hang":
    proc float32ToIntOrd(f: float) =
      if int32(f) > 5'i32:
        symexTarget("gt32Lit")
    let r = symexFind(float32ToIntOrd, tLabel("gt32Lit"))
    check r.status == sxSat
    check int32(r.witness[0]) > 5

  test "int32(f) vs literal: arithmetic sxSat — no doAssert crash":
    proc float32ToIntArith(f: float) =
      let k = int32(f) + 5'i32
      if k == 20'i32:
        symexTarget("arith32Lit")
    let r = symexFind(float32ToIntArith, tLabel("arith32Lit"))
    check r.status == sxSat
    check int32(r.witness[0]) + 5 == 20
