import std/unittest
import proptest/symex

# Phase 15 — Cluster F (float) cycle F1: type-bridge.
# Reconciled RED: the RFC's `x > 0.0` SUT needs float literals (F2) and float
# comparison (F4); F1 is only the type-bridge. So the pure type-bridge test is a
# float-param SUT reaching a target — the param is classified itFloat64,
# allocated svFloat64 (mkFloat64Var), and a stub (not-yet-bit-exact) float
# witness is extracted -> sxSat. Bit-exact extraction lands in F7.

proc f64sut(x: float) =
  symexTarget("hit")

proc f32sut(x: float32) =
  symexTarget("hit32")

suite "symex Phase 15 — F1 float type-bridge":

  test "float64 SUT: symexFind returns sxSat (float param allocated + extracted)":
    let r = symexFind(f64sut, tLabel("hit"))
    check r.status == sxSat

  test "float32 SUT: symexFind returns sxSat":
    let r = symexFind(f32sut, tLabel("hit32"))
    check r.status == sxSat
