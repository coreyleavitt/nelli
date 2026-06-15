import std/unittest
import std/math
import proptest/symex

# Phase 15 — Cluster F cycle F9b: seq[float32]/seq[float64] SUT parameter type.
#
# Extends the Phase-5 dynamic-seq machinery (Z3Array[Z3Int, sortOf(T)] + len)
# from int/bool elements to float elements: allocateSeqDataRaw + the seq-index
# walker path + extractSeqElements + the seq witness reader (emitTyAndReader /
# readSeqFloat64 / readSeqFloat32), mirroring the existing seq[int] plumbing.

proc fSeqNan(xs: seq[float64]) =
  if xs.len > 0 and xs[0] != xs[0]: symexTarget("snan")   # only NaN
proc fSeq32(xs: seq[float32]) =
  if xs.len > 0 and xs[0] > 1.0'f32: symexTarget("s32")
proc fSeqOrd(xs: seq[float64]) =
  if xs.len > 1 and xs[0] < xs[1]: symexTarget("sord")

suite "symex Phase 15 — F9b seq[float] parameter support":

  test "seq[float64] SUT: NaN element witness":
    let r = symexFind(fSeqNan, tLabel("snan"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check classify(r.witness[0][0]) == fcNan

  test "seq[float32] SUT: basic constraint":
    let r = symexFind(fSeq32, tLabel("s32"))
    check r.status == sxSat
    check r.witness[0].len > 0
    check r.witness[0][0] > 1.0'f32

  test "seq[float64] SUT: multi-element ordering constraint":
    let r = symexFind(fSeqOrd, tLabel("sord"))
    check r.status == sxSat
    check r.witness[0].len > 1
    check r.witness[0][0] < r.witness[0][1]
