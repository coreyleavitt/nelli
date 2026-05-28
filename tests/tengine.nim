import std/unittest
import proptest

suite "engine: forAll":
  test "passes when the property always holds":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x + 0 == x)
    check r.outcome == otPassed
    check r.examples == 100

  test "reports a counterexample when the property fails":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x < 50)
    check r.outcome == otFalsified
    check r.counterexample >= 50          # the failing input
    check r.choices.len >= 1              # the failing choice sequence is captured

  test "assume rejects examples; an over-strict assumption exhausts the budget":
    let r = forAll(integers(0, 100), proc(x: int) = (assume false),
                   Settings(maxExamples: 100, maxRejections: 30, seed: 1))
    check r.outcome == otExhausted

  test "runs are deterministic in the seed":
    proc prop(x: int) = ensure x < 30
    let st = Settings(maxExamples: 100, maxRejections: 1000, seed: 42)
    let a = forAll(integers(0, 100), prop, st)
    let b = forAll(integers(0, 100), prop, st)
    check a.outcome == otFalsified
    check a.counterexample == b.counterexample
    check a.choices == b.choices

  test "a crashing property (an IndexDefect) is caught as a falsification":
    proc prop(x: int) =
      let s = @[1, 2, 3]
      discard s[x]  # IndexDefect once x > 2
    let r = forAll(integers(0, 100), prop,
                   Settings(maxExamples: 200, maxRejections: 1000, seed: 7))
    check r.outcome == otFalsified
