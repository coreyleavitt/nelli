import std/unittest
import proptest

suite "shrinker: lexicographic lowering":
  test "shrinker minimizes a failing integer toward shrinkTowards":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x < 50)
    check r.outcome == otFalsified
    check r.counterexample == 50  # the minimum value that still fails

  test "shrinker leaves a passing run alone":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x >= 0)
    check r.outcome == otPassed
