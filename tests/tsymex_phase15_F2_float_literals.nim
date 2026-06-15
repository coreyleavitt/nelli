import std/unittest
import std/math
import proptest/symex

# Phase 15 — Cluster F cycle F2: float literal lifts (incl. Inf/NaN/-0.0) +
# IEEE ==/!= (reconciled: testing a literal needs equality; F4 adds ordering).

proc fInf(f: float) =
  if f == Inf: symexTarget("inf")
proc fNaN(f: float) =
  if f == NaN: symexTarget("nan")
proc fNegZero(f: float) =
  if f == -0.0: symexTarget("negzero")
proc fPi(f: float) =
  if f == 3.14: symexTarget("pi")
proc fZero(f: float) =
  if f == 0.0: symexTarget("zero")

suite "symex Phase 15 — F2 float literals":

  test "f == Inf is satisfiable":
    check symexFind(fInf, tLabel("inf")).status == sxSat

  test "f == NaN is UNSAT (IEEE: NaN != NaN) — ADR-0005":
    check symexFind(fNaN, tLabel("nan")).status == sxUnsat

  test "f == -0.0 is satisfiable":
    check symexFind(fNegZero, tLabel("negzero")).status == sxSat

  test "f == 3.14 is satisfiable":
    check symexFind(fPi, tLabel("pi")).status == sxSat

  test "f == 0.0 is satisfiable":
    check symexFind(fZero, tLabel("zero")).status == sxSat
