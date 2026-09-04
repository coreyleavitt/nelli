import std/unittest
import std/[math, sets]
import nelli
import nelli/[int128, choice, serialize, rng, datasource, shrinker]
import zerofill  # RFC-0010 A1 pin; removed by A3

suite "distribution biasing":
  test "integer boundary injection finds x=0 over the full int64 range":
    proc prop(x: int) = ensure x != 0
    let r = forAll(integers(low(int), high(int)), prop,
                   zeroFilled(Settings(maxExamples: 50, maxRejections: 1000,
                                       seed: 1, flakyRetries: 5)))
    check r.outcome == otFalsified
    check r.counterexample.get == 0

  test "small-magnitude bias finds |x| <= 100 in a wide range":
    proc prop(x: int) = ensure abs(x) > 100
    let r = forAll(integers(-1_000_000, 1_000_000), prop,
                   zeroFilled(Settings(maxExamples: 30, maxRejections: 1000,
                                       seed: 1, flakyRetries: 5)))
    check r.outcome == otFalsified
    check abs(r.counterexample.get) <= 100

  test "float boundary injection finds 0.0":
    proc prop(x: float) = ensure x != 0.0
    let r = forAll(floats(-1e9, 1e9, allowNan = false), prop,
                   zeroFilled(Settings(maxExamples: 50, maxRejections: 1000,
                                       seed: 1, flakyRetries: 5)))
    check r.outcome == otFalsified
    check r.counterexample.get == 0.0  # ±0.0 both satisfy this

  test "float boundary injection finds NaN under allowNan = true":
    proc prop(x: float) = ensure x.classify != fcNaN
    let r = forAll(floats(-1e9, 1e9, allowNan = true), prop,
                   zeroFilled(Settings(maxExamples: 50, maxRejections: 1000,
                                       seed: 1, flakyRetries: 5)))
    check r.outcome == otFalsified
    check r.counterexample.get.classify == fcNaN

  test "weighted integers heavily favor the weighted value":
    let s = integers(0, 1000, weights = @[(42, 0.5)])
    var ds = newDataSource(initSplitMix64(1))
    var count42 = 0
    for _ in 0 ..< 200:
      if s.generate(ds) == 42: inc count42
    # weight 0.5 ⇒ expected ~100 of 200; 60 is a very conservative floor.
    check count42 >= 60

  test "oneOf swarm still covers all branches and records its mask":
    let s = oneOf(@[just(0), just(1), just(2), just(3)])
    var ds = newDataSource(initSplitMix64(1))
    var saw: array[4, bool]
    for _ in 0 ..< 200:
      saw[s.generate(ds)] = true
    check saw[0] and saw[1] and saw[2] and saw[3]
    # Each oneOf call now records N mute-bools before its index, so the
    # recorded sequence is bool-heavy — confirm the mask draws happen.
    var boolCount = 0
    for n in ds.recorded:
      if n.kind == ckBoolean: inc boolCount
    check boolCount >= 200 * 4
