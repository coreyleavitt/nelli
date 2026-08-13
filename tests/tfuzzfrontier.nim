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
