import std/unittest
import std/math
import nelli/symex

# Phase 15 — Cluster F cycle F9a: array[N, float32/float64] element type-bridge
# audit + array-derived NaN extraction.
#
# F9a is a COMPLETENESS audit. The Phase-4 array walker allocates elements by
# recursing `allocateSym(elemTy)`, so float element kinds (svFloat32/svFloat64
# from F1) should slot in without new machinery; `classifyType` recurses on the
# element type, so `array[4, float64]` classifies as itArray(itFloat64, 4);
# and `emitTyAndReader` recurses per element, routing float elements to F7's
# readFloat/readFloat32. These tests are regression guards confirming the F1/F7
# additions reach the array element-access (iekArrayGet) and witness paths.
#
# The classifyType -> itArray(itFloat64, 4) shape is exercised transitively:
# a sort-mismatch in the type bridge would surface as a non-sxSat status or a
# raised "unsupported element kind" in allocateSym, so the end-to-end SUTs
# below are a faithful audit of the full array-of-float bridge.

proc fArr64(xs: array[4, float64]) =
  if xs[2] > 0.0: symexTarget("a64")
proc fArr32(xs: array[4, float32]) =
  if xs[2] > 0.0'f32: symexTarget("a32")
proc fArrNan(xs: array[4, float64]) =
  if not (xs[0] == xs[0]): symexTarget("anan")   # satisfied only by NaN

suite "symex Phase 15 — F9a array[N, float] element completeness":

  test "array[4, float64] SUT: element access returns svFloat64 witness":
    let r = symexFind(fArr64, tLabel("a64"))
    check r.status == sxSat
    check r.witness[0][2] > 0.0

  test "array[4, float32] SUT: element access returns svFloat32 witness":
    let r = symexFind(fArr32, tLabel("a32"))
    check r.status == sxSat
    check r.witness[0][2] > 0.0'f32

  test "array[4, float64] SUT: NaN element extraction via model_completion":
    let r = symexFind(fArrNan, tLabel("anan"))
    check r.status == sxSat
    check classify(r.witness[0][0]) == fcNan
