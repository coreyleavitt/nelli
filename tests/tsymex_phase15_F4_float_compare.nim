import std/unittest
import nelli/symex

# Phase 15 — Cluster F cycle F4: float ordering comparison (< <= > >=).
# IEEE ordering via Z3 FP theory: all ordering comparisons are false when an
# operand is NaN (so `x < x` is unsatisfiable — irreflexive even for NaN).

proc fLt(x: float) =
  if x < 5.0: symexTarget("lt")
proc fGe(x: float) =
  if x >= 5.0: symexTarget("ge")
proc fRange(x: float) =
  if x > 2.0 and x < 4.0: symexTarget("range")   # x == 3.0 works
proc fIrreflexive(x: float) =
  if x < x: symexTarget("never")                 # always false (incl. NaN)

suite "symex Phase 15 — F4 float ordering comparison":

  test "x < 5.0 -> sat":
    check symexFind(fLt, tLabel("lt")).status == sxSat
  test "x >= 5.0 -> sat":
    check symexFind(fGe, tLabel("ge")).status == sxSat
  test "2.0 < x < 4.0 -> sat":
    check symexFind(fRange, tLabel("range")).status == sxSat
  test "x < x -> unsat (IEEE ordering irreflexive, NaN<NaN false)":
    check symexFind(fIrreflexive, tLabel("never")).status == sxUnsat
