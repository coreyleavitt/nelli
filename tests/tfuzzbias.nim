import std/[unittest, times]
import nelli
import nelli/[choice, int128]

# #103 follow-up: FuzzSettings.integerBias threading. The IR fuzz
# runner's seed input is generated via newDataSource() at startup;
# user-supplied bias should be observed there. Subsequent corpus
# entries come from IR mutators (which don't use the bias), and the
# byte-mode adapter draws via bytesMode (also bias-irrelevant) — so
# the seed input is the *one* place bias matters for fuzz.

suite "FuzzSettings.integerBias threading":
  test "100% boundary bias forces the seed input to a boundary value":
    # Strategy `integers(-1_000_000, 1_000_000)`. The boundary set under
    # this constraint is {0, 1, -1, 1_000_000, -1_000_000, 999_999,
    # -999_999, shrinkTowards=0}. With 100% boundary + 50%
    # shrinkTowardsWeight, every seed input should land in this set.
    #
    # `seen` is set by the LAST `prop` call, which is the loop's one
    # mutation iteration (`maxIterations: 1`), not the raw seed draw
    # itself — this test's technique inherently assumes "one iteration ==
    # one mutation op" (true pre-RFC-fuzzer-nextgen-S3, and still true
    # under `uniformHavoc: true`). Havoc stacking is an orthogonal new axis
    # this test isn't exercising, so it's pinned off here rather than
    # loosening the boundary-set assertion itself.
    let s = FuzzSettings(
      maxIterations: 1, seed: 42,
      timeBudget: initDuration(seconds = 5),
      uniformHavoc: true,
      integerBias: IntegerBiasConfig(
        boundaryPercent: 100, smallWindowPercent: 0,
        smallWindowSize: 64, shrinkTowardsWeight: 50))
    var seen: int
    proc prop(x: int) =
      seen = x
      ensure true
    discard fuzzWith(integers(-1_000_000, 1_000_000), prop, s)
    # seen must be one of the boundary candidates.
    check seen in [0, 1, -1, 1_000_000, -1_000_000, 999_999, -999_999]
