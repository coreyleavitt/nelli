import std/unittest
import std/[strutils, options]
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

suite "engine: forAll":
  test "passes when the property always holds":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x + 0 == x)
    check r.outcome == otPassed
    check r.examples == 100

  test "reports a counterexample when the property fails":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x < 50)
    check r.outcome == otFalsified
    # `counterexample` is `Option[T]` — `some(value)` for a normal
    # property-fails-on-x falsification; `none` only when the strategy
    # itself raised before producing a value.
    check r.counterexample.isSome
    check r.counterexample.get >= 50      # the failing input
    check r.choices.len >= 1              # the failing choice sequence is captured

  test "repro() formats counterexample-as-Option correctly":
    # `some(x)` falsification → "counterexample=<value>".
    let r1 = forAll(integers(0, 100), proc(x: int) = ensure x < 50)
    check "counterexample=" in repro(r1)
    check "counterexample=<none" notin repro(r1)
    # Passing run → no counterexample line at all.
    let r2 = forAll(integers(0, 100), proc(x: int) = ensure x >= 0)
    check "counterexample" notin repro(r2)

  test "passing / exhausted reports carry no counterexample":
    let pass = forAll(integers(0, 100), proc(x: int) = ensure x >= 0)
    check pass.outcome == otPassed
    check pass.counterexample.isNone
    let exh = forAll(integers(0, 100), proc(x: int) = (assume false),
                     Settings(maxExamples: 100, maxRejections: 30, seed: 1))
    check exh.outcome == otExhausted
    check exh.counterexample.isNone

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

  test "a non-deterministic property is reported as otFlaky":
    var calls = 0
    proc flaky(x: int) =
      inc calls
      if calls == 1:
        ensure false  # fails only on its very first invocation
      # subsequent invocations return normally — i.e. the same input
      # produces a different outcome → flaky
    let r = forAll(integers(0, 100), flaky)
    check r.outcome == otFlaky

  test "post-shrink invariant catches flakiness even when pre-shrink retries are disabled":
    var calls = 0
    proc flaky(x: int) =
      inc calls
      if calls == 1: ensure false
    let s = Settings(maxExamples: 100, maxRejections: 1000, seed: 1,
                     flakyRetries: 0)
    let r = forAll(integers(0, 100), flaky, s)
    check r.outcome == otFlaky

  test "a crashing property (an IndexDefect) is caught as a falsification":
    proc prop(x: int) =
      let s = @[1, 2, 3]
      discard s[x]  # IndexDefect once x > 2
    let r = forAll(integers(0, 100), prop,
                   Settings(maxExamples: 200, maxRejections: 1000, seed: 7))
    check r.outcome == otFalsified

  test "Report carries the seed used and repro() formats key fields":
    let s = Settings(maxExamples: 100, maxRejections: 1000, seed: 42'u64,
                     flakyRetries: 5)
    let r = forAll(integers(0, 100), proc(x: int) = (ensure x < 50), s)
    check r.seed == 42'u64
    let line = repro(r)
    check "seed=42" in line
    check "counterexample" in line
    check "otFalsified" in line
