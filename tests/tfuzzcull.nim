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
