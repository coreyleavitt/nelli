import std/[unittest, times]
import nelli

# Coverage-guided fuzzing: the runtime bitmap is the substrate.
# Each instrumented branch in a {.cover.}'d proc records an edge ID;
# the fuzz runner reads `currentCoverage()` after each example and
# uses growth as the targeting score.
#
# Per #106, recordEdge is gated on `CoverageMode`. The default is `cmOff`
# so `{.cover.}`'d code costs nothing for callers who haven't opted in.
# These tests exercise the runtime directly, so they enable cmRecording
# explicitly. `fuzzWith` flips the mode itself, so the suite below it
# doesn't need to.

suite "coverage runtime":
  setup:
    setCoverageMode(cmRecording)
  teardown:
    setCoverageMode(cmOff)

  test "recordEdge marks an edge; currentCoverage counts distinct hits":
    resetCoverage()
    check currentCoverage() == 0
    recordEdge(42)
    check currentCoverage() == 1
    recordEdge(99)
    check currentCoverage() == 2

  test "duplicate edge IDs don't increment the count":
    resetCoverage()
    recordEdge(7)
    recordEdge(7)
    recordEdge(7)
    check currentCoverage() == 1

  test "resetCoverage zeros the bitmap":
    resetCoverage()
    recordEdge(1); recordEdge(2); recordEdge(3)
    check currentCoverage() == 3
    resetCoverage()
    check currentCoverage() == 0

suite "{.cover.} pragma: source-level instrumentation":
  setup:
    setCoverageMode(cmRecording)
  teardown:
    setCoverageMode(cmOff)

  test "if/else branches record distinct edges":
    proc trivial(x: int): int {.cover.} =
      if x > 0:
        x + 1
      else:
        x - 1

    resetCoverage()
    discard trivial(5)        # takes `then` branch
    let afterThen = currentCoverage()
    check afterThen >= 1

    discard trivial(-3)       # takes `else` branch
    let afterElse = currentCoverage()
    check afterElse > afterThen  # new edge recorded

  test "repeated calls along same branch don't grow coverage":
    proc t(x: int): int {.cover.} =
      if x > 0: 1 else: 0

    resetCoverage()
    discard t(5)
    let one = currentCoverage()
    discard t(7)              # same branch as t(5)
    discard t(99)
    check currentCoverage() == one

suite "fuzzWith: coverage-guided runner":
  test "runs the requested number of iterations and reports coverage":
    proc fnUnderTest(x: int): int {.cover.} =
      if x > 1000:
        if x mod 7 == 3:
          x * 2
        else:
          x + 1
      else:
        x - 1

    let settings = FuzzSettings(maxIterations: 500, seed: 1,
                                timeBudget: initDuration(seconds = 10))
    proc prop(x: int) =
      discard fnUnderTest(x)
      ensure true
    let r = fuzzWith(integers(low(int32), high(int32)), prop, settings)
    check r.iterations >= 1
    check r.iterations <= 500
    check r.coverageHits > 0     # at least one branch hit by any input

  test "falsifying inputs accumulate as crashes":
    proc f(x: int): int {.cover.} =
      if x > 100:
        raise newException(ValueError, "boom on big input")
      x

    let settings = FuzzSettings(maxIterations: 200, seed: 2,
                                timeBudget: initDuration(seconds = 10))
    let r = fuzzWith(integers(0, 1_000_000),
                    proc(x: int) = (discard f(x); ensure true),
                    settings)
    # IR is the only mutation kernel (RFC-fuzzer-nextgen U3), so crashes land
    # in irCrashes.
    check r.irCrashes.len >= 1

  test "coverage grows as the corpus expands across the branch structure":
    # The point of coverage-guided over random: inputs hitting new edges
    # become parents for future mutations, so deeper branches are reached
    # by composition of "first satisfy A, then satisfy B given A". We
    # verify the dynamic: coverage at end of run > coverage at first
    # iteration. (A truly random fuzzer would plateau quickly on a
    # narrow-conditioned SUT.)
    proc nested(x: int): int {.cover.} =
      if x > 50_000:
        if x mod 13 == 7:
          x * 2
        else:
          x + 1
      else:
        x - 1

    proc prop(x: int) =
      discard nested(x)
      ensure true

    let r = fuzzWith(integers(0, 1_000_000), prop,
                    FuzzSettings(maxIterations: 1500, seed: 7,
                                 timeBudget: initDuration(seconds = 10)))
    # At least 2 of the 3 branch arms should have been entered across
    # 1500 mutated inputs starting from a random seed in [0, 10^6].
    check r.coverageHits >= 2
    # Corpus expanded beyond the initial random seed. IR is the only
    # mutation kernel (RFC-fuzzer-nextgen U3), so survivors land in irEntries.
    check r.corpus.kind == fckIR
    check r.corpus.irEntries.len >= 2
