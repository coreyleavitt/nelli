import std/unittest
import nelli/symex

# Phase 15 — Cluster F cycle F3: float arithmetic (+ - * / and unary -).
# IEEE arithmetic via Z3 FP theory (round-to-nearest-even).

proc fAdd(x: float) =
  if x + 1.0 == 5.0: symexTarget("add")      # x == 4.0
proc fSub(x: float) =
  if x - 2.0 == 3.0: symexTarget("sub")      # x == 5.0
proc fMul(x: float) =
  if x * 2.0 == 10.0: symexTarget("mul")     # x == 5.0
proc fDiv(x: float) =
  if x / 2.0 == 4.0: symexTarget("div")      # x == 8.0
proc fNeg(x: float) =
  if -x == 5.0: symexTarget("neg")           # x == -5.0
proc fMulZero(x: float) =
  if x * 0.0 == 5.0: symexTarget("never")    # unreachable: x*0 is 0 or NaN

suite "symex Phase 15 — F3 float arithmetic":

  test "x + 1.0 == 5.0 -> sat":
    check symexFind(fAdd, tLabel("add")).status == sxSat
  test "x - 2.0 == 3.0 -> sat":
    check symexFind(fSub, tLabel("sub")).status == sxSat
  test "x * 2.0 == 10.0 -> sat":
    check symexFind(fMul, tLabel("mul")).status == sxSat
  test "x / 2.0 == 4.0 -> sat":
    check symexFind(fDiv, tLabel("div")).status == sxSat
  test "unary -x == 5.0 -> sat":
    check symexFind(fNeg, tLabel("neg")).status == sxSat
  test "x * 0.0 == 5.0 -> unsat (arithmetic is real, not skipped)":
    check symexFind(fMulZero, tLabel("never")).status == sxUnsat
