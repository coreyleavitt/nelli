import std/unittest
import proptest

suite "targeted PBT":
  test "target() captures a score and a passing property still passes":
    proc prop(x: int) =
      target(float(x))
      ensure x >= 0
    let r = forAll(integers(0, 100), prop)
    check r.outcome == otPassed

  test "target() guides toward a narrow falsifying region":
    # Property holds unless x+y > 1900 (~0.5% of the joint range);
    # with target(x+y), hill-climb pushes toward the boundary.
    proc prop(t: (int, int)) =
      target(float(t[0] + t[1]))
      ensure t[0] + t[1] <= 1900
    let r = forAll(tuples2(integers(0, 1000), integers(0, 1000)), prop,
                   Settings(maxExamples: 80, maxRejections: 1000, seed: 1))
    check r.outcome == otFalsified
    check r.counterexample[0] + r.counterexample[1] > 1900
