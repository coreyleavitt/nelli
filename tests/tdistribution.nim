import std/unittest
import nelli/[int128, rng]
import nelli/datasource/distribution

# #103 — extract integer-bias distribution from `drawInteger`'s hot path
# into a parameterizable seam. These tests pin down the helpers'
# behavior directly, independent of the full DataSource.

suite "selectBoundaryValue":
  test "shrinkTowards is heavily favored (subroll < 50%)":
    # The boundary path picks `clamp(shrinkTowards, min, max)` with
    # `shrinkTowardsWeight%` probability and a value from
    # `integerBoundaries` otherwise. Drive it deterministically: a
    # known seed produces a known stream of rolls.
    var rng = initSplitMix64(0x1)
    let st = toInt128(42)
    var hits = 0
    let total = 200
    for _ in 0 ..< total:
      let v = selectBoundaryValue(rng, toInt128(0), toInt128(100), st,
                                  defaultIntegerBias)
      if v == st: inc hits
    # With shrinkTowardsWeight = 50, ~50% of draws should land on st.
    check hits >= 70
    check hits <= 130

  test "result always falls in [min, max]":
    var rng = initSplitMix64(0x2)
    for i in 0 ..< 500:
      let v = selectBoundaryValue(rng, toInt128(-10), toInt128(10),
                                  toInt128(0), defaultIntegerBias)
      check v >= toInt128(-10)
      check v <= toInt128(10)
