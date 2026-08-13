import std/[unittest, tables, times]
import nelli

# #103 follow-up: thread Settings.integerBias through the engine so a
# property test can override bias on its own DataSource per-example.
# Verified end-to-end: with autoLabels on, the int-distribution buckets
# (auto.int:zero / near-lo / near-hi / other) reflect the bias.

suite "Settings.integerBias threading":
  test "all-uniform bias keeps `auto.int:zero` rare":
    # With 0% boundary and 0% small-window, every draw goes through the
    # pure-uniform branch. Over 1000 examples in a wide range, the
    # exact-zero count should be at most a few (and statistically near
    # zero — random uniform over [-1e9, 1e9] hits 0 once per 2e9 draws).
    var s = defaultSettings()
    s.maxExamples = 1000
    s.seed = 42
    s.useSA = false
    s.targetedSAIters = 0
    s.deadline = initDuration(seconds = 10)
    s.integerBias = IntegerBiasConfig(
      boundaryPercent: 0, smallWindowPercent: 0,
      smallWindowSize: 64, shrinkTowardsWeight: 50)
    let r = forAll(integers(-1_000_000_000, 1_000_000_000),
                   (proc(x: int) = ensure true), s)
    check r.outcome == otPassed
    let zeroHits = r.events.categorical.getOrDefault("auto.int:zero", 0)
    # Uniform random over a 2-billion-wide range: zero is overwhelmingly
    # improbable. Allow up to 3 by chance.
    check zeroHits <= 3

  test "all-boundary bias makes `auto.int:zero` the dominant bucket":
    var s = defaultSettings()
    s.maxExamples = 200
    s.seed = 7
    s.useSA = false
    s.targetedSAIters = 0
    s.deadline = initDuration(seconds = 10)
    # 100% boundary, 50% shrinkTowards-within-boundary — half the
    # examples should land exactly on 0 (the default shrinkTowards).
    s.integerBias = IntegerBiasConfig(
      boundaryPercent: 100, smallWindowPercent: 0,
      smallWindowSize: 64, shrinkTowardsWeight: 50)
    let r = forAll(integers(-1_000_000_000, 1_000_000_000),
                   (proc(x: int) = ensure true), s)
    check r.outcome == otPassed
    let zeroHits = r.events.categorical.getOrDefault("auto.int:zero", 0)
    # 50% expected ≈ 100 hits out of 200; allow a wide tolerance.
    check zeroHits >= 60
