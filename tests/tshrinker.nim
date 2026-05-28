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

suite "shrinker: deletion (lists)":
  test "shrinker minimizes a failing list to the smallest counterexample":
    let r = forAll(lists(integers(0, 9), maxLen = 20),
                   proc(xs: seq[int]) = ensure xs.len < 3)
    check r.outcome == otFalsified
    check r.counterexample == @[0, 0, 0]  # min length × min elements
