import std/[unittest]
import proptest
import proptest/[int128, choice, datasource, shrinker, rng]

# The public `integers(int, int)` strategy never produces constraints
# wider than int64. The shrinker's 128-bit bisection path is exercised
# only via Int128-range strategies (a future feature) or direct
# construction, so we test it at the low level here.

suite "shrinker: 128-bit bisection in lowerIntegerAt":
  test "bisects through a 100-bit range to shrinkTowards = 0":
    # Build a Strategy that draws one ChoiceInt in a range strictly
    # wider than int64. Property: `value < 0`. The shrinker should
    # find the minimum positive falsifying value — anywhere `>= 0`.
    let bigHi  = toInt128(1'i64) + toInt128(int64.high)  # ~2^63 + something to push us past 64-bit width
    # Actually construct properly: range = [-2^70, 2^70].
    var hi128 = toInt128(1'i64)
    for _ in 0 ..< 70:                       # hi128 = 2^70
      hi128 = hi128 + hi128
    let lo128 = toInt128(0) - hi128          # lo128 = -2^70

    proc draw(src: var DataSource): Int128 =
      src.drawInteger(lo128, hi128, toInt128(0))

    let s = newStrategy(draw)
    proc prop(v: Int128) =
      (ensure v < toInt128(0))     # fails when v >= 0
    # Build the falsifying choice sequence: start at max (positive, way
    # past 64-bit), then shrink should land at 0 (smallest non-negative).
    var ds = newDataSource(initSplitMix64(1))
    let initial = s.generate(ds)
    check initial >= lo128 and initial <= hi128
    # Force a known falsifying value at the high end so shrinker has work.
    var falsifying = ds.recorded
    falsifying[0] = ChoiceNode(kind: ckInteger,
                               intC: IntConstraints(min: lo128, max: hi128,
                                                    shrinkTowards: toInt128(0)),
                               intVal: hi128, wasForced: false)
    let r = shrink(s, prop, falsifying, maxShrinks = 500)
    check not r.flaky
    # Shrinker should reach 0 (the smallest non-negative, which still falsifies).
    check r.example.isSome
    check r.example.get == toInt128(0)

suite "hill-climb: log-scaled perturbation set":
  test "logScaledIntDeltas covers ±2^k up to the constraint width":
    # The fixed ±{1,10,100,1000} set was useless on ranges spanning >
    # 1000; the log-scaled set adapts to the constraint width so a wide
    # range gets large-magnitude proposals that can actually cross
    # falsifying boundaries.
    let small = logScaledIntDeltas(8)
    check small == @[8'i64, -8, 4, -4, 2, -2, 1, -1]

    let wide = logScaledIntDeltas(1_000_000)
    # 2^19 = 524288 ≤ 1_000_000 < 2^20; largest k is 19.
    check wide[0] == 1'i64 shl 19
    check wide[1] == -(1'i64 shl 19)
    check wide[^1] == -1
    check wide.len == 40   # 20 magnitudes × {+, -}

    check logScaledIntDeltas(0).len == 0    # degenerate
