## Phase 2 (docs/fuzz/FUZZ_PLAN.md): the pure `Coverage` value + `CoverageFrontier`
## — AFL bucketing and the order-independent admission decision the fuzz loop asks
## per input. No C, no subprocess: pure logic over synthetic `Coverage` values.

import std/unittest
import nelli

suite "fuzz: CoverageFrontier (Phase 2)":
  test "bucketOf: 0 is the unique unseen bucket; any execution outranks it":
    check bucketOf(0) == 0'u8
    check bucketOf(1) == 1'u8                     # the 0->1 boundary: first execution is novel
    check bucketOf(1) > bucketOf(0)
    var prev = 0'u8                               # monotonic non-decreasing
    for n in 0'u8 .. 255'u8:
      check bucketOf(n) >= prev
      prev = bucketOf(n)
    check bucketOf(3) != bucketOf(4)              # AFL log boundaries
    check bucketOf(7) != bucketOf(8)
    check bucketOf(15) != bucketOf(16)
    check bucketOf(127) != bucketOf(128)
    check bucketOf(255) == bucketOf(128)          # top bucket saturates

  test "admit: a new edge is interesting; re-hitting the same bucket is not":
    var f = newCoverageFrontier("t")
    let a = f.admit(Coverage(counters: @[1'u8, 0, 0]))
    check a.interesting and a.newEdges == 1 and a.globalEdges == 1
    let b = f.admit(Coverage(counters: @[1'u8, 0, 0]))   # identical map
    check (not b.interesting) and b.newEdges == 0 and b.globalEdges == 1
    let c = f.admit(Coverage(counters: @[1'u8, 1, 0]))   # a second edge appears
    check c.interesting and c.newEdges == 1 and c.globalEdges == 2

  test "admit: a higher bucket on a known edge is new again":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))          # bucket 1
    let hi = f.admit(Coverage(counters: @[5'u8]))         # bucket 4 (> 1) -> novel
    check hi.interesting and hi.newEdges == 1

  test "admit is order-independent: a lower count never un-admits, max wins":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[5'u8]))          # bucket 4
    let lo = f.admit(Coverage(counters: @[3'u8]))         # bucket 3 (< 4) -> not novel
    check (not lo.interesting) and lo.newEdges == 0
    check f.coveredEdges == 1
    # reverse arrival order reaches the same final frontier (max bucket):
    var g = newCoverageFrontier()
    discard g.admit(Coverage(counters: @[3'u8]))
    discard g.admit(Coverage(counters: @[5'u8]))
    check g.coveredEdges == 1

  test "frontier grows when a later map has more slots":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 0]))
    check f.totalEdges == 2
    let big = f.admit(Coverage(counters: @[1'u8, 0, 1, 0]))  # a newly-loaded module
    check f.totalEdges == 4 and big.interesting and big.newEdges == 1

suite "fuzz: FrontierStats (RFC-fuzzer-nextgen S1)":
  ## S1 owns a single incrementally-maintained `FrontierStats` sub-object,
  ## folded in at the ONE `admit()` site above (coverage.nim) — never
  ## rescanned. These pin the two RED-able bookkeeping properties the RFC
  ## calls out: rarity counts increment exactly once per admit, and the
  ## last-improved sequence number only advances on a bucket-raising admit.

  test "hitCounts increments exactly once per admit, only for slots the run actually touched":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 0, 0]))   # touches slot 0
    check f.stats.hitCount(0) == 1
    check f.stats.hitCount(1) == 0
    check f.stats.totalAdmitted == 1
    discard f.admit(Coverage(counters: @[1'u8, 1, 0]))   # touches slots 0 and 1
    check f.stats.hitCount(0) == 2                        # incremented again
    check f.stats.hitCount(1) == 1                        # first hit
    check f.stats.hitCount(2) == 0                        # never touched
    check f.stats.totalAdmitted == 2
    # a re-hit at a LOWER count still counts as "touched" for rarity purposes,
    # independent of whether the bucket rose (bucket algebra is orthogonal):
    discard f.admit(Coverage(counters: @[1'u8, 0, 0]))
    check f.stats.hitCount(0) == 3
    check f.stats.hitCount(1) == 1                        # unchanged: not touched this time
    check f.stats.totalAdmitted == 3

  test "lastImprovedAt advances only on a bucket-raising admit, to that admit's sequence number":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))          # admit #1: slot 0 bucket 0->1, new
    check f.stats.lastImprovedAt(0) == 1
    discard f.admit(Coverage(counters: @[1'u8]))          # admit #2: same bucket, not new
    check f.stats.lastImprovedAt(0) == 1                  # unchanged
    discard f.admit(Coverage(counters: @[5'u8]))          # admit #3: bucket 1->4, new again
    check f.stats.lastImprovedAt(0) == 3
    check f.stats.lastImprovedAt(1) == 0                  # never touched -> never improved

suite "fuzz: FrontierStats staleness / stall detection (RFC-fuzzer-nextgen G3)":
  ## `stalled(f, k)` reads the ONE shared `FrontierStats.lastGlobalImprovedSeq`
  ## (folded at the same `admit` site as every other stat) — orchestrator-wide,
  ## not per-worker.

  test "a fresh frontier is never stalled, regardless of k":
    var f = newCoverageFrontier()
    check not f.stalled(1)
    check not f.stalled(100)

  test "k <= 0 never stalls (disabled, the inert default)":
    var f = newCoverageFrontier()
    for i in 0 ..< 5: discard f.admit(Coverage(counters: @[1'u8]))  # no further improvement
    check not f.stalled(0)
    check not f.stalled(-1)

  test "stalled fires exactly at k admits with no coverage improvement, not before":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))   # admit #1: improves (0->1)
    check f.stats.staleness == 0
    check not f.stalled(3)
    discard f.admit(Coverage(counters: @[1'u8]))   # admit #2: no improvement (staleness 1)
    check f.stats.staleness == 1
    check not f.stalled(3)
    discard f.admit(Coverage(counters: @[1'u8]))   # admit #3: no improvement (staleness 2)
    check not f.stalled(3)
    discard f.admit(Coverage(counters: @[1'u8]))   # admit #4: no improvement (staleness 3)
    check f.stats.staleness == 3
    check f.stalled(3)

  test "a fresh improvement resets staleness back to 0, un-stalling immediately":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 0'u8]))
    for i in 0 ..< 4: discard f.admit(Coverage(counters: @[1'u8, 0'u8]))  # staleness climbs to 4
    check f.stalled(3)
    discard f.admit(Coverage(counters: @[1'u8, 1'u8]))   # slot 1 newly covered: improves
    check f.stats.staleness == 0
    check not f.stalled(1)

  test "staleness counts ADMITS (every non-rejected run), not just corpus-admitted ones":
    # Matches S1's own `totalAdmitted`/`hitCounts` convention: `admit` is
    # called for every folded run, admitted-into-corpus or not (coverage.nim
    # doc on `hitCounts`) — staleness must move on that same denominator.
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))         # improves
    discard f.admit(Coverage(counters: @[1'u8]))         # re-hit, same bucket: no improvement
    discard f.admit(Coverage(counters: @[1'u8]))         # re-hit again: no improvement
    check f.stats.totalAdmitted == 3
    check f.stats.staleness == 2

suite "fuzz: Entropic energy (RFC-fuzzer-nextgen S1)":
  ## The Böhme-style information-gain weight: `-log2(hits/totalAdmitted)`,
  ## the Shannon self-information of a slot having been reached at all. 0
  ## for a slot every admitted run has hit (no information in seeing it
  ## again); grows as a slot's hit population shrinks toward "only a few
  ## inputs ever reach it."

  test "rarityWeight: a slot hit by every admit carries zero weight":
    var f = newCoverageFrontier()
    for i in 0 ..< 5: discard f.admit(Coverage(counters: @[1'u8]))  # slot 0 every time
    check f.stats.rarityWeight(0) == 0.0

  test "rarityWeight: a rarely-hit slot strictly outweighs a commonly-hit slot":
    var f = newCoverageFrontier()
    # slot 0: hit on every admit (common). slot 1: hit on only the first (rare).
    discard f.admit(Coverage(counters: @[1'u8, 1'u8]))
    for i in 0 ..< 9: discard f.admit(Coverage(counters: @[1'u8, 0'u8]))
    check f.stats.totalAdmitted == 10
    check f.stats.hitCount(0) == 10
    check f.stats.hitCount(1) == 1
    check f.stats.rarityWeight(1) > f.stats.rarityWeight(0)
    check f.stats.rarityWeight(0) == 0.0

  test "rarityWeight: no signal yet (nothing admitted) is zero, never NaN/Inf":
    var f = newCoverageFrontier()
    check f.stats.rarityWeight(0) == 0.0

  test "coveredSlots: the sparse nonzero-slot index list of a Coverage":
    check coveredSlots(Coverage(counters: @[0'u8, 3'u8, 0'u8, 1'u8])) == @[1, 3]
    check coveredSlots(Coverage(counters: @[0'u8, 0'u8])) == newSeq[int]()

  test "entropicEnergy: covering a rare edge yields strictly higher energy than only common edges":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 1'u8]))        # slot 0 common, slot 1 rare
    for i in 0 ..< 9: discard f.admit(Coverage(counters: @[1'u8, 0'u8]))
    let rareEnergy = entropicEnergy(@[1], f.stats, sizeChoices = 10, execNanos = 0)
    let commonEnergy = entropicEnergy(@[0], f.stats, sizeChoices = 10, execNanos = 0)
    check rareEnergy > commonEnergy

  test "entropicEnergy: a smaller input outranks a larger one covering the same edges":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 1'u8]))
    for i in 0 ..< 9: discard f.admit(Coverage(counters: @[1'u8, 0'u8]))
    let small = entropicEnergy(@[1], f.stats, sizeChoices = 4, execNanos = 0)
    let big = entropicEnergy(@[1], f.stats, sizeChoices = 4000, execNanos = 0)
    check small > big

  test "entropicEnergy: a faster input outranks a slower one covering the same edges":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8, 1'u8]))
    for i in 0 ..< 9: discard f.admit(Coverage(counters: @[1'u8, 0'u8]))
    let fast = entropicEnergy(@[1], f.stats, sizeChoices = 4, execNanos = 1000)
    let slow = entropicEnergy(@[1], f.stats, sizeChoices = 4, execNanos = 50_000_000)
    check fast > slow

  test "entropicEnergy: missing timing (execNanos <= 0) degrades to size-only cost, never penalizes":
    var f = newCoverageFrontier()
    discard f.admit(Coverage(counters: @[1'u8]))
    let noTiming = entropicEnergy(@[0], f.stats, sizeChoices = 4, execNanos = 0)
    let zeroTiming = entropicEnergy(@[0], f.stats, sizeChoices = 4, execNanos = -1)
    check noTiming == zeroTiming
    check noTiming > 0.0

  test "entropicEnergy is always strictly positive: no corpus entry is ever fully starved":
    var f = newCoverageFrontier()
    check entropicEnergy(@[], f.stats, sizeChoices = 0, execNanos = 0) > 0.0
