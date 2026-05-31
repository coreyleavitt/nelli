import std/[unittest, tables, times]
import proptest
import proptest/[rng, datasource]

# `frequency` — a weighted `oneOf`. Each branch carries an integer weight; the
# realized distribution is proportional to the weights. Unlike `oneOf` it makes
# a distributional promise, so (a) the selector is drawn *unbiased* (the
# boundary/small-window bias that `drawInteger` applies to value draws would
# skew the realized frequencies), and (b) it does no swarm muting (which would
# renormalize the weights away). Shrinking still heads toward the first branch.

suite "frequency: selection":
  test "only ever yields values from its declared branches":
    let s = frequency(@[(3, just("a")), (1, just("b"))])
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 200:
      check s.generate(ds) in ["a", "b"]

suite "frequency: distribution":
  test "realized frequencies are proportional to the weights":
    # Five equal-weight branches → ~20% each. `drawInteger`'s value-bias
    # (boundary + small-window injection) would over-pick the extreme indices,
    # so frequency must draw its selector UNBIASED to honor the weights.
    let labels = ["a", "b", "c", "d", "e"]
    let s = frequency(@[(1, just("a")), (1, just("b")), (1, just("c")),
                        (1, just("d")), (1, just("e"))])
    var ds = newDataSource(initSplitMix64(12345))
    var counts = initCountTable[string]()
    const N = 20000
    for _ in 0 ..< N:
      counts.inc s.generate(ds)
    for l in labels:
      let p = counts[l] / N
      check abs(p - 0.20) <= 0.03   # within 3 points of uniform

  test "unequal weights are honored (1:3 → ~25/75)":
    let s = frequency(@[(1, just("rare")), (3, just("common"))])
    var ds = newDataSource(initSplitMix64(999))
    var counts = initCountTable[string]()
    const N = 20000
    for _ in 0 ..< N:
      counts.inc s.generate(ds)
    check abs(counts["rare"] / N - 0.25) <= 0.03
    check abs(counts["common"] / N - 0.75) <= 0.03

suite "frequency: shrinking":
  test "shrinks toward the first branch regardless of weight":
    # "second" is 99x more likely to be generated, but the *minimal*
    # counterexample is "first" — the selector shrinks toward branch 0.
    proc prop(x: string) = ensure false
    let r = forAll(frequency(@[(1, just("first")), (99, just("second"))]), prop)
    check r.outcome == otFalsified
    check r.counterexample.get == "first"

suite "frequency: validation":
  test "rejects an empty branch list":
    var empty: seq[(int, Strategy[int])] = @[]
    expect ValueError:
      discard frequency(empty)

  test "rejects weights that are all zero":
    expect ValueError:
      discard frequency(@[(0, just(1)), (0, just(2))])

  test "rejects a negative weight":
    expect ValueError:
      discard frequency(@[(1, just(1)), (-3, just(2))])

  test "excludes zero-weight branches but keeps the positive ones":
    let s = frequency(@[(0, just("never")), (1, just("always"))])
    var ds = newDataSource(initSplitMix64(7))
    for _ in 0 ..< 200:
      check s.generate(ds) == "always"

suite "frequency: distribution visibility (auto-labels)":
  test "emits auto.frequency:branch-i so the realized split is observable":
    # Declaring weights sets intent; the auto-labels let the distribution
    # report show the *realized* split, so a user can confirm reality matches.
    proc prop(x: string) = ensure true
    var s = Settings(maxExamples: 2000, maxRejections: 10000, seed: 7,
                     flakyRetries: 1, maxShrinks: 10, useSA: false,
                     targetedSAIters: 0, deadline: initDuration(seconds = 30))
    s.autoLabels = true
    let r = forAll(frequency(@[(1, just("lo")), (4, just("hi"))]), prop, s)
    check r.outcome == otPassed
    check r.events.categorical.hasKey("auto.frequency:branch-0")
    check r.events.categorical.hasKey("auto.frequency:branch-1")
    # weight 4 branch dominates the weight 1 branch
    check r.events.categorical["auto.frequency:branch-1"] >
          r.events.categorical["auto.frequency:branch-0"]

suite "frequency: DSL":
  property "binds through the given DSL":
    given x in frequency(@[(1, just(0)), (3, integers(1, 9))])
    ensure x in 0 .. 9
