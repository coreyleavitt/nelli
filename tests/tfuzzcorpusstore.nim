## RFC-fuzzer-nextgen R27: `FuzzCorpusStore` (fuzzcorpus.nim) exercised
## directly — no `fuzz()` campaign, no `Orchestrator`, no `Target`. Proves the
## corpus/schedule seam extracted from `fuzz[T]` (five hand-synchronized
## parallel arrays -> one collaborator) really owns its state: `add`/`cull`
## keep every array in lockstep, and `refreshEnergy`/`pickParent` reproduce
## the exact Entropic power-schedule formula the loop used inline before.

import std/unittest
import nelli/[fuzzcorpus, choice, datasource, coverage, rng]

proc cov(bytes: varargs[byte]): Coverage = Coverage(counters: @bytes)

suite "FuzzCorpusStore — add/addSeed keep every parallel array in lockstep":

  test "starts empty":
    let c = FuzzCorpusStore()
    check c.len == 0

  test "addSeed appends a placeholder (empty coverage, 0 nanos, no cmpLog)":
    var c = FuzzCorpusStore()
    addSeed(c, @[], @[])
    check c.len == 1
    check covAt(c, 0).counters.len == 0
    check nanosOf(c) == @[0'i64]
    check cmpLogAt(c, 0).len == 0
    check slotsOf(c) == @[newSeq[int](0)]

  test "add appends a fully-observed entry":
    var c = FuzzCorpusStore()
    add(c, @[], @[], cov(1'u8, 0'u8, 1'u8), 500'i64,
       @[CmpLogEntry(kind: clkInt, op: coEq, width: 8, lhsInt: 1, rhsInt: 2)])
    check c.len == 1
    check covAt(c, 0).counters == @[1'u8, 0'u8, 1'u8]
    check nanosOf(c) == @[500'i64]
    check slotsOf(c) == @[@[0, 2]]
    check cmpLogAt(c, 0).len == 1

  test "setObserved backfills a seed added via addSeed":
    var c = FuzzCorpusStore()
    addSeed(c, @[], @[])
    setObserved(c, 0, cov(0'u8, 1'u8), 42'i64, @[])
    check covAt(c, 0).counters == @[0'u8, 1'u8]
    check nanosOf(c) == @[42'i64]
    check slotsOf(c) == @[@[1]]

  test "indexing (`corpus[i]`) and `choicesAt`/`spansAt` agree":
    var c = FuzzCorpusStore()
    let ch = @[integerChoice(7, 0, 100, 0)]
    add(c, ch, @[], cov(1'u8), 0'i64)
    check c[0].choices == ch
    check choicesAt(c, 0) == ch
    check spansAt(c, 0) == c[0].spans

  test "allChoices/allCov mirror insertion order":
    var c = FuzzCorpusStore()
    add(c, @[integerChoice(1, 0, 10, 0)], @[], cov(1'u8), 0'i64)
    add(c, @[integerChoice(2, 0, 10, 0)], @[], cov(0'u8, 1'u8), 0'i64)
    check allChoices(c).len == 2
    check allChoices(c)[1] == @[integerChoice(2, 0, 10, 0)]
    check allCov(c)[1].counters == @[0'u8, 1'u8]

  test "sizesChoices reports each entry's IR length":
    var c = FuzzCorpusStore()
    add(c, @[integerChoice(1, 0, 10, 0)], @[], cov(1'u8), 0'i64)
    add(c, @[integerChoice(1, 0, 10, 0), integerChoice(2, 0, 10, 0)], @[], cov(1'u8), 0'i64)
    check sizesChoices(c) == @[1, 2]

suite "FuzzCorpusStore — refreshEnergy/pickParent (S1 Entropic schedule)":

  test "refreshEnergy matches entropicEnergy computed by hand":
    var c = FuzzCorpusStore()
    add(c, @[], @[], cov(1'u8), 0'i64)
    var f = newCoverageFrontier()
    discard f.admit(cov(1'u8))
    refreshEnergy(c, f.stats)
    check energyOf(c) == @[entropicEnergy(@[0], f.stats, 0, 0'i64)]

  test "pickParent(uniform=true) reproduces plain `rng.next mod len`, consuming rng identically":
    var c = FuzzCorpusStore()
    add(c, @[], @[], cov(1'u8), 0'i64)
    add(c, @[], @[], cov(0'u8, 1'u8), 0'i64)
    add(c, @[], @[], cov(0'u8, 0'u8, 1'u8), 0'i64)
    var rngA = initSplitMix64(99'u64)
    var rngB = initSplitMix64(99'u64)
    let picked = pickParent(c, rngA, true)
    let expected = int(rngB.next mod 3'u64)
    check picked == expected

  test "pickParent(uniform=false) with never-refreshed (still-0.0-placeholder) energy falls back to uniform":
    # `add`/`addSeed` seed `energy` at the `0.0` placeholder — refreshed only
    # by an explicit `refreshEnergy` call. Without that call, `pickParent`'s
    # `total <= 0.0` branch is exactly what the pre-R27 loop's
    # `energyWeightedIndex` fell back to for an unrefreshed/all-zero energy
    # vector: plain `rng.next mod len`.
    var c = FuzzCorpusStore()
    add(c, @[], @[], Coverage(), 0'i64)
    add(c, @[], @[], Coverage(), 0'i64)
    var rngA = initSplitMix64(7'u64)
    var rngB = initSplitMix64(7'u64)
    check pickParent(c, rngA, false) == int(rngB.next mod 2'u64)

  test "pickParent(uniform=false) is deterministic in rng and never picks an index outside range":
    var c = FuzzCorpusStore()
    for i in 0 ..< 5:
      add(c, @[], @[], cov(byte(1 shl (i mod 8))), int64(i * 100))
    var f = newCoverageFrontier()
    for i in 0 ..< 5: discard f.admit(cov(byte(1 shl (i mod 8))))
    refreshEnergy(c, f.stats)
    for seed in [1'u64, 2'u64, 3'u64, 12345'u64]:
      var rngA = initSplitMix64(seed)
      var rngB = initSplitMix64(seed)
      check pickParent(c, rngA, false) == pickParent(c, rngB, false)
      var rngC = initSplitMix64(seed)
      let idx = pickParent(c, rngC, false)
      check idx >= 0 and idx < 5

suite "FuzzCorpusStore — cull":

  test "cull filters every parallel array to the kept indices":
    var c = FuzzCorpusStore()
    add(c, @[integerChoice(1, 0, 10, 0)], @[], cov(1'u8), 10'i64,
       @[CmpLogEntry(kind: clkInt, op: coEq, width: 8, lhsInt: 1, rhsInt: 2)])
    add(c, @[integerChoice(2, 0, 10, 0)], @[], cov(0'u8, 1'u8), 20'i64)
    add(c, @[integerChoice(3, 0, 10, 0)], @[], cov(0'u8, 0'u8, 1'u8), 30'i64)
    cull(c, @[true, false, true])
    check c.len == 2
    check c[0].choices == @[integerChoice(1, 0, 10, 0)]
    check c[1].choices == @[integerChoice(3, 0, 10, 0)]
    check nanosOf(c) == @[10'i64, 30'i64]
    check slotsOf(c) == @[@[0], @[2]]
    check cmpLogAt(c, 0).len == 1
    check cmpLogAt(c, 1).len == 0

  test "cull to everything-false empties the store":
    var c = FuzzCorpusStore()
    add(c, @[], @[], cov(1'u8), 0'i64)
    add(c, @[], @[], cov(1'u8), 0'i64)
    cull(c, @[false, false])
    check c.len == 0

  test "energy is reset (to be refreshed by the next tick) after a cull":
    var c = FuzzCorpusStore()
    add(c, @[], @[], cov(1'u8), 0'i64)
    add(c, @[], @[], cov(0'u8, 1'u8), 0'i64)
    var f = newCoverageFrontier()
    discard f.admit(cov(1'u8))
    discard f.admit(cov(0'u8, 1'u8))
    refreshEnergy(c, f.stats)
    check energyOf(c)[0] > 0.0
    cull(c, @[true, false])
    check energyOf(c) == @[0.0]
