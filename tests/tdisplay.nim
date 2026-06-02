import std/[unittest, strutils, options]
import proptest

suite "Strategy.displayWith":
  test "Report.displayed renders the counterexample via the attached proc":
    # The point: `arbitrary(MyType)` whose default `$` is unreadable can be
    # decorated with a domain-specific renderer (encode → string), and the
    # falsifying example's `Report.displayed` carries that string verbatim.
    let s = integers(0, 100).displayWith(proc(x: int): string = "x=" & $x)
    let r = forAll(s,
                   proc(x: int) = (ensure x < 50),
                   Settings(maxExamples: 200, seed: 1,
                            maxShrinks: 500, flakyRetries: 5))
    check r.outcome == otFalsified
    check r.displayed.startsWith("x=")
    check r.displayed == "x=" & $r.counterexample.get

  test "displayed reflects the shrunk value, not whatever was found first":
    # `x >= 0` falsifies on any negative draw; the shrinker pulls it
    # toward 0 (shrinkTowards) → final counterexample is -1. The
    # displayed string must match the *shrunk* value, which is the
    # whole point of computing it post-shrink.
    let s = integers(-1000, 1000).displayWith(
              proc(x: int): string = "v[" & $x & "]")
    let r = forAll(s,
                   proc(x: int) = (ensure x >= 0),
                   Settings(maxExamples: 200, seed: 2,
                            maxShrinks: 500, flakyRetries: 5))
    check r.outcome == otFalsified
    check r.counterexample.get == -1
    check r.displayed == "v[-1]"

  test "repro() prefers `displayed` over the default $value":
    let s = integers(-1000, 1000).displayWith(
              proc(x: int): string = "v[" & $x & "]")
    let r = forAll(s,
                   proc(x: int) = (ensure x >= 0),
                   Settings(maxExamples: 200, seed: 3,
                            maxShrinks: 500, flakyRetries: 5))
    let text = repro(r)
    check "counterexample=v[-1]" in text
    check "counterexample=-1\n" notin text  # the default-`$` form should NOT appear

suite "Strategy.displayWith: combinator algebra":
  # The display proc is type-indexed on T. `filter` keeps T, so it
  # preserves; `map`/`flatMap` change T, so they drop — there's no
  # general way to lift a `T → string` through a `T → U`. Users
  # re-attach downstream via `displayWith` (or use the sugar).
  test "filter preserves the display (same T)":
    let base = integers(0, 100).displayWith(proc(x: int): string = "x=" & $x)
    let s = base.filter(proc(x: int): bool = x mod 2 == 0)
    check s.display != nil
    check s.display(42) == "x=42"

  test "map drops the display (type changed)":
    let base = integers(0, 100).displayWith(proc(x: int): string = "x=" & $x)
    let s = base.map(proc(x: int): string = "s" & $x)
    check s.display == nil

  test "flatMap drops the display (output type dynamic)":
    let base = integers(0, 100).displayWith(proc(x: int): string = "x=" & $x)
    let s = base.flatMap(proc(x: int): Strategy[int] = just(x * 10))
    check s.display == nil

suite "Strategy.displayWith: sugar":
  test "mapWithDisplay attaches the new-T renderer in one call":
    let s = integers(0, 100).mapWithDisplay(
              proc(x: int): string = "S" & $x,
              proc(y: string): string = "[" & y & "]")
    check s.display != nil
    check s.display("S42") == "[S42]"

  test "flatMapWithDisplay attaches the new-T renderer in one call":
    let s = integers(0, 5).flatMapWithDisplay(
              proc(x: int): Strategy[int] = just(x * 10),
              proc(y: int): string = "y=" & $y)
    check s.display != nil
    check s.display(30) == "y=30"

suite "Strategy.displayWith: oneOf":
  test "oneOf inherits the first non-nil branch display":
    let a = just(1)
    let b = integers(10, 20).displayWith(proc(x: int): string = "B" & $x)
    let c = integers(100, 200).displayWith(proc(x: int): string = "C" & $x)
    let s = oneOf(@[a, b, c])
    check s.display != nil
    check s.display(15) == "B15"   # picks b (first non-nil), not c

  test "oneOf has no display when all branches lack one":
    let s = oneOf(@[just(1), integers(10, 20)])
    check s.display == nil

suite "Strategy.displayWith: edge cases":
  test "displayed is empty when counterexample is none (strategy raised)":
    # A strategy that always raises FalsifiedError mid-generation before
    # producing a value: counterexample = none, so there is nothing to
    # render, so displayed must be the empty sentinel.
    let s = newStrategy(proc(src: var DataSource): int =
      raise newException(FalsifiedError, "no value"))
        .displayWith(proc(x: int): string = "x=" & $x)
    let r = forAll(s,
                   proc(x: int) = (ensure true),
                   Settings(maxExamples: 50, seed: 9,
                            maxShrinks: 100, flakyRetries: 5))
    check r.outcome == otFalsified
    check r.counterexample.isNone
    check r.displayed == ""

  test "no display attached → displayed stays empty on falsification":
    let s = integers(0, 100)  # no displayWith
    let r = forAll(s,
                   proc(x: int) = (ensure x < 50),
                   Settings(maxExamples: 200, seed: 5,
                            maxShrinks: 500, flakyRetries: 5))
    check r.outcome == otFalsified
    check r.displayed == ""

suite "Strategy.displayWith: DSL integration":
  test "displayCounterexample prefers displayed over default $value":
    # The DSL uses this helper to render the counterexample line on
    # falsification. Custom displays must take precedence so derived
    # types' opaque `$` doesn't surface in the test failure log.
    let r = Report[int](outcome: otFalsified, examples: 1,
                        counterexample: box(7), choices: @[],
                        displayed: "DOC{a=7}")
    check displayCounterexample(r) == "DOC{a=7}"

  test "displayCounterexample falls back to default $ when no display":
    let r = Report[int](outcome: otFalsified, examples: 1,
                        counterexample: box(7), choices: @[],
                        displayed: "")
    check displayCounterexample(r) == "7"

  test "displayCounterexample marks `none` counterexample explicitly":
    let r = Report[int](outcome: otFalsified, examples: 1,
                        counterexample: empty[int](), choices: @[],
                        displayed: "")
    check "none" in displayCounterexample(r)
