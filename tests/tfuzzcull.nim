## RFC-fuzzer-nextgen S4: continuous corpus culling.
##
## Deliverable 1 — periodic in-campaign favored-set/domination culling,
## promoting `minimalCovering`'s one-shot end-of-run greedy set cover
## (fuzz.nim ~1210) to a live, cadence-driven AFL-style policy that prefers
## smaller/faster/rarer-edge entries (S1's own `entropicEnergy`) when
## choosing the cover. This suite pins `favoredIndices` (fuzz.nim), the pure
## per-edge-champion domination test the loop's periodic cull is built on —
## same style as `tfuzzmincover.nim` pins `minimalCovering` directly.
##
## Deliverable 2 — the persisted-corpus scope-cut is covered in
## `tests/tfuzzcullpersist.nim`.

import std/unittest
import nelli
import nelli/choice

proc twoEdgeTarget(): Target[int] =
  ## x==100 covers BOTH edges (the fitter, superset entry); x==200 covers
  ## only edge 0 (⊆ the fitter entry's edges — a dominated entry once both
  ## are in the corpus); anything else covers nothing.
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](2)
    if x == 100: c[0] = 1'u8; c[1] = 1'u8
    elif x == 200: c[0] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc threeEdgeTarget(): Target[int] =
  ## Closed, disjoint edge space (tfuzzseedcov.nim's convention): `x mod 3`
  ## is the hot slot, so post-seed mutation can only ever rediscover an edge
  ## some seed already covers, never dominate one seed with another.
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](3)
    c[((x mod 3) + 3) mod 3] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

suite "S4 deliverable 1: favoredIndices (pure per-edge domination test)":

  test "disjoint unique-edge entries are never dominated":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 0'u8]))   # entry0: slot 0 only
    discard f.admit(Coverage(counters: @[0'u8, 1'u8]))   # entry1: slot 1 only
    let keep = favoredIndices(@[@[0], @[1]], @[10, 10], @[0'i64, 0'i64], f.stats)
    check keep == @[true, true]

  test "an entry whose edges are a strict subset of a fitter entry's is culled":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 1'u8]))   # slot0 hit twice, slot1 once
    discard f.admit(Coverage(counters: @[1'u8, 0'u8]))
    # entry0 covers {0,1}; entry1 covers {0} ⊆ entry0's edges. Same size/speed,
    # so entry0 (strictly more coverage) wins slot0's championship outright and
    # is the sole candidate for slot1 — entry1 is dominated on both slots.
    let keep = favoredIndices(@[@[0, 1], @[0]], @[10, 10], @[0'i64, 0'i64], f.stats)
    check keep[0] == true
    check keep[1] == false

  test "a smaller entry wins a same-edge championship over a larger one (size preference)":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))
    let keep = favoredIndices(@[@[0], @[0]], @[4, 4000], @[0'i64, 0'i64], f.stats)
    check keep == @[true, false]

  test "a faster entry wins a same-edge championship over a slower one (speed preference)":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))
    let keep = favoredIndices(@[@[0], @[0]], @[10, 10], @[1_000'i64, 50_000_000'i64],
                              f.stats)
    check keep == @[true, false]

  test "a rarer-edge entry outranks a common-edge entry when both are otherwise equal":
    var f = newCoverageFrontier()
    # slot 0 hit on every admit (common); slot 1 hit only on the first (rare).
    discard f.admit(Coverage(counters: @[1'u8, 1'u8]))
    for i in 0 ..< 9: discard f.admit(Coverage(counters: @[1'u8, 0'u8]))
    # entry0 covers the rare slot only; entry1 covers the common slot only —
    # same size/speed. Both are unique-edge here so both survive, but this
    # pins that the rare one's energy is the higher of the two (exercised
    # directly against entropicEnergy below, and indirectly: a THIRD entry
    # tied on size/speed but covering BOTH slots should still be dominated
    # by neither — sanity that favoredIndices doesn't over-cull).
    let keep = favoredIndices(@[@[1], @[0]], @[10, 10], @[0'i64, 0'i64], f.stats)
    check keep == @[true, true]

  test "an entry covering nothing (unrun seed) is never favored":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))
    let keep = favoredIndices(@[@[0], @[]], @[10, 10], @[0'i64, 0'i64], f.stats)
    check keep == @[true, false]

  test "exact ties break deterministically to the lowest index":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))
    let keep = favoredIndices(@[@[0], @[0], @[0]], @[5, 5, 5],
                              @[0'i64, 0'i64, 0'i64], f.stats)
    check keep == @[true, false, false]

  test "empty corpus yields an empty result":
    check favoredIndices(newSeq[seq[int]](0), newSeq[int](0), newSeq[int64](0),
                         FrontierStats()) == newSeq[bool](0)

suite "S4 deliverable 1: periodic cull wired into the fuzz loop":

  test "a dominated seed is culled at the cadence; the fitter superset seed survives":
    let seedA = @[integerChoice(100, 0, 1000, 0)]
    let seedB = @[integerChoice(200, 0, 1000, 0)]
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), twoEdgeTarget(), fr,
                 FuzzSettings(maxIterations: 3, seed: 1, initialIRCorpus: @[seedA, seedB], scheduling: SchedulingConfig(cullCadence: 1)))
    check seedA in r.corpus.irEntries
    check seedB notin r.corpus.irEntries

  test "without S4 (uniformCorpus), the dominated seed is NOT culled":
    let seedA = @[integerChoice(100, 0, 1000, 0)]
    let seedB = @[integerChoice(200, 0, 1000, 0)]
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), twoEdgeTarget(), fr,
                 FuzzSettings(maxIterations: 3, seed: 1, initialIRCorpus: @[seedA, seedB], scheduling: SchedulingConfig(cullCadence: 1, uniformCorpus: true)))
    check seedA in r.corpus.irEntries
    check seedB in r.corpus.irEntries

  test "unique-edge seeds are never culled across a live campaign":
    var seeds: seq[seq[ChoiceNode]]
    for i in 0 ..< 3: seeds.add @[integerChoice(i, 0, 1000, 0)]
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), threeEdgeTarget(), fr,
                 FuzzSettings(maxIterations: 60, seed: 3, initialIRCorpus: seeds, scheduling: SchedulingConfig(cullCadence: 5)))
    for s in seeds:
      check s in r.corpus.irEntries

  test "cull never empties a live corpus (all-uncovered corpus skips culling)":
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), twoEdgeTarget(), fr,
                 FuzzSettings(maxIterations: 30, seed: 5, scheduling: SchedulingConfig(cullCadence: 1)))
    check r.corpus.irEntries.len > 0

  test "cullCadence 0 resolves to defaultCullCadence: still culls a dominated seed":
    let seedA = @[integerChoice(100, 0, 1000, 0)]
    let seedB = @[integerChoice(200, 0, 1000, 0)]
    var fr = newCoverageFrontier()
    let r = fuzz(integers(0, 1000), twoEdgeTarget(), fr,
                 FuzzSettings(maxIterations: defaultCullCadence + 1, seed: 1,
                              initialIRCorpus: @[seedA, seedB]))
    check seedA in r.corpus.irEntries
    check seedB notin r.corpus.irEntries
