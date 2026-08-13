import std/[unittest, strutils]
import nelli

# Engine layer for `examples`: a `forAllWithExamples` that runs a list
# of explicit values through `prop` before the random phase. The DSL
# (next batch of tests) is thin syntax over it.

suite "forAllWithExamples":
  test "a failing explicit example is reported with empty choices":
    # No shrinking on explicit failures — the user said "this exact
    # value matters." choices is empty (we never drew from the
    # strategy for explicit cases), counterexample is the bad value.
    let r = forAllWithExamples(@[-1, -2],
                               integers(0, 100),
                               proc(x: int) = (ensure x >= 0),
                               Settings(maxExamples: 10, seed: 1,
                                        flakyRetries: 0, maxShrinks: 5,
                                        maxRejections: 10))
    check r.outcome == otFalsified
    check r.counterexample.get == -1     # first failing explicit
    check r.choices.len == 0             # no choice sequence for explicit
    check "explicit" in r.message.toLowerAscii

  test "all explicit examples passing → random phase runs and can falsify":
    # When explicit cases all pass, control reaches forAll. A random
    # falsification still goes through the usual shrink path → `choices`
    # is non-empty (it's a random-phase failure, not explicit).
    let r = forAllWithExamples(@[0, 1, 2],   # all pass the predicate
                               integers(0, 100),
                               proc(x: int) = (ensure x < 50),
                               Settings(maxExamples: 200, seed: 1,
                                        flakyRetries: 0, maxShrinks: 100,
                                        maxRejections: 100))
    check r.outcome == otFalsified
    check r.choices.len > 0           # random phase did its thing
    check "explicit" notin r.message  # message does NOT mention explicit

  test "all explicit + random pass → otPassed":
    let r = forAllWithExamples(@[0, 5, 99],
                               integers(0, 100),
                               proc(x: int) = (ensure x >= 0),
                               Settings(maxExamples: 50, seed: 1,
                                        flakyRetries: 0, maxShrinks: 10,
                                        maxRejections: 100))
    check r.outcome == otPassed

suite "DSL: examples":
  test "examples <bareValue> for single binding runs explicit cases first":
    var seenExplicits: seq[int]
    var explicitPhaseDone = false
    property "single-binding examples":
      examples 42
      examples 99
      given x in integers(0, 5)
      if not explicitPhaseDone:
        seenExplicits.add x
        if seenExplicits.len == 2:
          explicitPhaseDone = true
      ensure true
    # Both explicit values ran, in source order, before any random draws.
    check seenExplicits == @[42, 99]

  test "multi-binding examples destructure as tuples":
    var seen: seq[(int, string)]
    var stopRecording = false
    property "two-arg":
      examples (7, "alpha")
      examples (-3, "beta")
      given n in integers(0, 100), s in sampledFrom(@["x", "y", "z"])
      if not stopRecording:
        seen.add (n, s)
        if seen.len == 2:
          stopRecording = true
      ensure true
    check seen == @[(7, "alpha"), (-3, "beta")]
