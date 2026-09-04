import std/unittest
import std/[strutils, options]
import nelli
import nelli/[int128, choice, serialize, rng, datasource, shrinker]
import zerofill  # RFC-0010 A1 pin; removed by A3

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

  test "Report.notes carries the (label, value) pairs from the failing run":
    proc prop(x: int) =
      note("input", x)
      note("doubled", x * 2)
      ensure x < 50
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 50, seed: 1)))
    check r.outcome == otFalsified
    check r.notes.len == 2
    check r.notes[0][0] == "input"
    check r.notes[1][0] == "doubled"
    # The shrunk counterexample is 50 (smallest still-failing x).
    check r.notes[0][1] == "50"
    check r.notes[1][1] == "100"

  test "repro() emits note[label]=value lines on falsification":
    proc prop(x: int) =
      note("x", x)
      note("doubled", x * 2)
      ensure x < 50
    let r = forAll(integers(0, 100), prop, zeroFilled(Settings(maxExamples: 100, seed: 5)))
    let text = repro(r)
    check "note[x]=50" in text
    check "note[doubled]=100" in text

  test "Report.notes reflects the SHRUNK example's notes, not the originally-found one":
    # Property fails at x >= 50. The random phase might find a large
    # falsifier (e.g. x=87); the shrinker minimizes it to x=50. The
    # Report's notes must contain "50", not "87".
    proc prop(x: int) =
      note("x", x)
      ensure x < 50
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 100, seed: 999)))
    check r.outcome == otFalsified
    check r.counterexample.get == 50
    check r.notes.len == 1
    check r.notes[0] == ("x", "50")

  test "notes from earlier passing runs don't leak into the failing run":
    # Each example must start with an empty noteStack. A property that
    # always calls `note("x", x)` should have exactly one note in its
    # Report (the failing x), not all the earlier passing values too.
    proc prop(x: int) =
      note("x", x)
      ensure x < 50
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 100, seed: 7)))
    check r.outcome == otFalsified
    check r.notes.len == 1   # only the failing example's note, not 99 of them

  test "note() in a property body has no effect on generation or outcome":
    # A property's pass/fail outcome and shrunk counterexample should be
    # identical whether or not the body sprinkles `note(...)` calls.
    proc propPlain(x: int) = ensure x < 50
    proc propNoted(x: int) =
      note("input", x)
      note("doubled", x * 2)
      ensure x < 50
    let st = zeroFilled(Settings(maxExamples: 100, maxRejections: 1000, seed: 42))
    let plain = forAll(integers(0, 100), propPlain, st)
    let noted = forAll(integers(0, 100), propNoted, st)
    check plain.outcome == noted.outcome
    check plain.counterexample == noted.counterexample
    check plain.choices == noted.choices

  test "repro() formats counterexample-as-Option correctly":
    # `some(x)` falsification → "counterexample=<value>".
    let r1 = forAll(integers(0, 100), proc(x: int) = ensure x < 50)
    check "counterexample=" in repro(r1)
    check "counterexample=<none" notin repro(r1)
    # Passing run → no counterexample line at all.
    let r2 = forAll(integers(0, 100), proc(x: int) = ensure x >= 0)
    check "counterexample" notin repro(r2)

  test "assumeOk unwraps an isOk-shaped result; rejects when not ok":
    # Synthetic Result-like type with the `.isOk: bool` + `.get: T` shape.
    type MyResult[T] = object
      ok: bool
      value: T
    proc isOk[T](r: MyResult[T]): bool = r.ok
    proc get[T](r: MyResult[T]): T = r.value
    proc good(): MyResult[int] = MyResult[int](ok: true, value: 42)
    proc bad():  MyResult[int] = MyResult[int](ok: false, value: 0)
    # When `prop` consistently gets a good result, the property runs
    # normally and observes the unwrapped value.
    var seen = 0
    let okRun = forAll(integers(0, 0), proc(_: int) =
      let v = assumeOk(good()); seen += v)
    check okRun.outcome == otPassed
    check seen > 0  # ran at least once and saw the unwrapped 42
    # When `prop` always sees a bad result, every example is rejected and
    # the budget exhausts.
    let badRun = forAll(integers(0, 0), proc(_: int) =
      discard assumeOk(bad()),
      zeroFilled(Settings(maxExamples: 100, maxRejections: 20, seed: 1)))
    check badRun.outcome == otExhausted

  test "assumeSome unwraps Option[T]; rejects when none":
    var seen = 0
    let okRun = forAll(integers(1, 10), proc(x: int) =
      let v = assumeSome(some(x * 2)); seen += v)
    check okRun.outcome == otPassed
    check seen > 0
    let neverRun = forAll(integers(0, 0), proc(_: int) =
      discard assumeSome(none(int)),
      zeroFilled(Settings(maxExamples: 100, maxRejections: 20, seed: 1)))
    check neverRun.outcome == otExhausted

  test "passing / exhausted reports carry no counterexample":
    let pass = forAll(integers(0, 100), proc(x: int) = ensure x >= 0)
    check pass.outcome == otPassed
    check pass.counterexample.isNone
    let exh = forAll(integers(0, 100), proc(x: int) = (assume false),
                     zeroFilled(Settings(maxExamples: 100, maxRejections: 30, seed: 1)))
    check exh.outcome == otExhausted
    check exh.counterexample.isNone

  test "assume rejects examples; an over-strict assumption exhausts the budget":
    let r = forAll(integers(0, 100), proc(x: int) = (assume false),
                   zeroFilled(Settings(maxExamples: 100, maxRejections: 30, seed: 1)))
    check r.outcome == otExhausted

  test "runs are deterministic in the seed":
    proc prop(x: int) = ensure x < 30
    let st = zeroFilled(Settings(maxExamples: 100, maxRejections: 1000, seed: 42))
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
    let s = zeroFilled(Settings(maxExamples: 100, maxRejections: 1000, seed: 1,
                                flakyRetries: 0))
    let r = forAll(integers(0, 100), flaky, s)
    check r.outcome == otFlaky

  # Crash-as-falsification relies on `except Defect`, which --panics:on makes
  # statically dead (Defects become fatal/uncatchable). Skip under panics:on;
  # see engine.nim's compile-time warning.
  when not compileOption("panics"):
    test "a crashing property (an IndexDefect) is caught as a falsification":
      proc prop(x: int) =
        let s = @[1, 2, 3]
        discard s[x]  # IndexDefect once x > 2
      let r = forAll(integers(0, 100), prop,
                     zeroFilled(Settings(maxExamples: 200, maxRejections: 1000, seed: 7)))
      check r.outcome == otFalsified

  test "Report carries the seed used and repro() formats key fields":
    let s = zeroFilled(Settings(maxExamples: 100, maxRejections: 1000, seed: 42'u64,
                                flakyRetries: 5))
    let r = forAll(integers(0, 100), proc(x: int) = (ensure x < 50), s)
    check r.seed == 42'u64
    let line = repro(r)
    check "seed=42" in line
    check "counterexample" in line
    check "otFalsified" in line
