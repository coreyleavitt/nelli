import std/[unittest, times, tables]
import nelli

# #107 — coverage-as-PBT-target. With `Settings.coverageGuided = true`
# the engine wraps every property call so that the per-example coverage
# delta is written into `currentFrame().scores["__coverage__"]`. The
# existing targeted-phase machinery (Pareto front, hill-climb, SA) then
# treats coverage as just-another-objective with no further changes.

proc twoArm(x: int): int {.cover.} =
  ## Two-arm instrumented SUT: x > 5000 visits one edge, otherwise
  ## another. Across maxExamples drawn from int32 we expect both arms
  ## hit, so cumulative coverage >= 2 and at least some inputs grow it.
  if x > 5000:
    x * 2
  else:
    x + 1

suite "coverage-guided forAll":
  test "no __coverage__ score appears when coverageGuided is off":
    proc prop(x: int) =
      discard twoArm(x)
      ensure true
    var s = Settings(maxExamples: 20, maxRejections: 100,
                     seed: 1, flakyRetries: 1, maxShrinks: 10,
                     useSA: false, targetedSAIters: 0,
                     deadline: initDuration(seconds = 5))
    s.coverageGuided = false
    let r = forAll(integers(0, 10000), prop, s)
    check r.outcome == otPassed
    for entry in r.paretoFront:
      check not entry.scores.hasKey("__coverage__")

  test "with coverageGuided=true, paretoFront carries __coverage__ scores":
    proc prop(x: int) =
      discard twoArm(x)
      ensure true
    var s = Settings(maxExamples: 30, maxRejections: 100,
                     seed: 1, flakyRetries: 1, maxShrinks: 10,
                     useSA: false, targetedSAIters: 0,
                     deadline: initDuration(seconds = 5))
    s.coverageGuided = true
    let r = forAll(integers(0, 10000), prop, s)
    check r.outcome == otPassed
    check r.paretoFront.len >= 1
    var seenCoverage = false
    var maxCov = 0.0
    for entry in r.paretoFront:
      if entry.scores.hasKey("__coverage__"):
        seenCoverage = true
        if entry.scores["__coverage__"] > maxCov:
          maxCov = entry.scores["__coverage__"]
    check seenCoverage
    # First-discoverer of an edge gets a positive delta.
    check maxCov >= 1.0
    # Cumulative union across the whole run, populated by finalize.
    check r.coverageHits >= 2

  test "Report.coverageHits is 0 when coverageGuided is off":
    proc prop(x: int) =
      discard twoArm(x)
      ensure true
    var s = Settings(maxExamples: 20, maxRejections: 100,
                     seed: 1, flakyRetries: 1, maxShrinks: 10,
                     useSA: false, targetedSAIters: 0,
                     deadline: initDuration(seconds = 5))
    s.coverageGuided = false
    let r = forAll(integers(0, 10000), prop, s)
    check r.coverageHits == 0

  test "coverageGuided routes through CoverageFrontier: many identical-coverage repeats never re-inflate coverageHits":
    ## RFC-fuzzer-nextgen U1: the engine now folds each example's coverage
    ## into a `CoverageFrontier` via `admit`, after peeking its Pareto-visible
    ## value via the non-mutating `score` (tfuzzfrontier.nim's U1 suite pins
    ## that contract directly). A singleton strategy (`integers(1, 1)`) makes
    ## EVERY example draw the identical value, so every one of the 10 calls
    ## hits the identical single edge (the else arm) — deterministic, no RNG
    ## variation in which arm fires. `admit`'s bucket-comparison fold means
    ## only the first call is a genuine discovery; `coverageHits` (driven by
    ## the frontier, not a raw running scalar) must land on exactly 1, not
    ## drift upward across the 9 redundant re-admits.
    proc prop(x: int) =
      discard twoArm(x)
      ensure true
    var s = Settings(maxExamples: 10, maxRejections: 100,
                     seed: 1, flakyRetries: 1, maxShrinks: 10,
                     useSA: false, targetedSAIters: 0,
                     deadline: initDuration(seconds = 5))
    s.coverageGuided = true
    let r = forAll(integers(1, 1), prop, s)
    check r.outcome == otPassed
    check r.examples == 10
    check r.coverageHits == 1
    var covScores: seq[float]
    for entry in r.paretoFront:
      if entry.scores.hasKey("__coverage__"):
        covScores.add entry.scores["__coverage__"]
    # Exactly one Pareto entry ever carries the (positive) coverage score:
    # the first discovery dominates every later zero-score repeat, so
    # `insertPareto` never keeps a redundant duplicate.
    check covScores.len == 1
    check covScores[0] >= 1.0

  test "coverageGuided=true + a property that raises a Defect: falsification reported with CrashInfo, not a crash-fatal abort (R35)":
    ## RFC-fuzzer-nextgen's original motivating bug was exactly this
    ## combination: a coverage-guided `forAll` whose property crashed
    ## (a failed `doAssert`, an `IndexDefect`, etc.) took down the whole
    ## run instead of being caught, shrunk, and reported like any other
    ## falsification. `randomPhase`'s `except Defect` arm (U0) is the same
    ## code path regardless of `coverageGuided`, and was verified correct
    ## for this combination by a throwaway run during the review — this
    ## test is the gap that throwaway run left in the committed suite.
    proc crashesAboveThreshold(x: int) =
      discard twoArm(x)   # keep the coverage instrumentation live
      doAssert x < 9000, "must stay below 9000"
    var s = Settings(maxExamples: 300, maxRejections: 100,
                     seed: 42, flakyRetries: 1, maxShrinks: 20,
                     useSA: false, targetedSAIters: 0,
                     deadline: initDuration(seconds = 5))
    s.coverageGuided = true
    let r = forAll(integers(0, 10000), crashesAboveThreshold, s)
    check r.outcome == otFalsified
    check r.counterexample.isSome
    check r.counterexample.get == 9000        # minimal still-failing x
    check r.crash.isSome
    check r.crash.get.kind == ckException
    check r.crash.get.defect == "AssertionDefect"
    # Coverage machinery ran normally alongside the crash: at least one
    # passing example (drawn before the crashing one was found) recorded
    # a `__coverage__` score, exactly as the non-crashing suites above
    # observe. Proves the crash didn't skip or corrupt the coverage-guided
    # path — it falsified through it.
    var seenCoverage = false
    for entry in r.paretoFront:
      if entry.scores.hasKey("__coverage__"): seenCoverage = true
    check seenCoverage

  test "coverageGuided restores the prior coverage mode on exit":
    setCoverageMode(cmOff)
    proc prop(x: int) =
      discard twoArm(x)
      ensure true
    var s = Settings(maxExamples: 5, maxRejections: 100, seed: 1,
                     flakyRetries: 1, maxShrinks: 10, useSA: false,
                     targetedSAIters: 0,
                     deadline: initDuration(seconds = 5))
    s.coverageGuided = true
    discard forAll(integers(0, 10000), prop, s)
    check currentCoverageMode() == cmOff
