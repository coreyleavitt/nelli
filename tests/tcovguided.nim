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
