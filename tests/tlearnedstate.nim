## RFC-fuzzer-nextgen S6: `LearnedState` encode/decode (`nelli/learnedstate`),
## tested in isolation from the fuzz loop — pure round-trip + the
## ignore-on-mismatch cold-start rule. Loop-level checkpoint/resume wiring
## is proven separately in `tfuzzcheckpoint.nim`.

import std/unittest
import nelli
import nelli/rng
import nelli/binaryio

suite "LearnedState encode/decode (RFC-fuzzer-nextgen S6)":
  test "round-trips frontier stats, bandit state, and dictionary exactly":
    var frontier = newCoverageFrontier("bin1")
    var cov = Coverage(counters: newSeq[uint8](8))
    cov.counters[0] = 3'u8
    cov.counters[1] = 1'u8
    discard admit(frontier, cov)
    cov.counters[1] = 2'u8
    discard admit(frontier, cov)

    var bandit = newOperatorBandit(5)
    var rng = initSplitMix64(7)
    for i in 0 ..< 10:
      let arm = chooseOperator(bandit, rng)
      credit(bandit, arm, 1.0)

    var dict: Dictionary
    dict.entries.add DictEntry(kind: dvInt, intVal: toInt128(42))
    dict.entries.add DictEntry(kind: dvBytes, bytesVal: @[1'u8, 2'u8, 3'u8])
    dict.entries.add DictEntry(kind: dvString, strVal: "MAGIC")

    let original = newLearnedState(frontier.stats, bandit, dict)
    let encoded = encodeLearnedState(original)
    let decoded = decodeLearnedState(encoded)

    check decoded.ok
    check decoded.state.frontierHitCounts == original.frontierHitCounts
    check decoded.state.frontierLastImprovedSeq == original.frontierLastImprovedSeq
    check decoded.state.frontierTotalAdmitted == original.frontierTotalAdmitted
    check decoded.state.frontierLastGlobalImprovedSeq == original.frontierLastGlobalImprovedSeq
    check decoded.state.banditPulls == original.banditPulls
    check decoded.state.banditRewardSum == original.banditRewardSum
    check decoded.state.banditTotalPulls == original.banditTotalPulls
    check decoded.state.dictionary.entries.len == original.dictionary.entries.len
    for i in 0 ..< original.dictionary.entries.len:
      let a = original.dictionary.entries[i]
      let b = decoded.state.dictionary.entries[i]
      check a.kind == b.kind
      case a.kind
      of dvInt:    check a.intVal == b.intVal
      of dvBytes:  check a.bytesVal == b.bytesVal
      of dvString: check a.strVal == b.strVal
    # Non-trivial fixture sanity: the round-trip isn't vacuously equal zeros.
    check original.frontierTotalAdmitted == 2
    check original.dictionary.entries.len == 3

  test "an empty LearnedState round-trips too":
    let original = LearnedState()
    let decoded = decodeLearnedState(encodeLearnedState(original))
    check decoded.ok
    check decoded.state.frontierHitCounts.len == 0
    check decoded.state.dictionary.entries.len == 0

  test "a wrong-magic buffer is ignored (cold start), not a crash":
    let bogus = @[1'u8, 2, 3, 4, 5, 6, 7, 8]
    let decoded = decodeLearnedState(bogus)
    check not decoded.ok

  test "a future/unsupported version is ignored (cold start), not a crash":
    var frontier = newCoverageFrontier("bin1")
    var cov = Coverage(counters: newSeq[uint8](8))
    cov.counters[0] = 1'u8
    discard admit(frontier, cov)
    var buf = encodeLearnedState(newLearnedState(frontier.stats,
      newOperatorBandit(5), Dictionary()))
    # The version u16 sits right after the 4-byte magic — bump it past
    # anything this build understands.
    buf[4] = 0xFF'u8
    buf[5] = 0xFF'u8
    let decoded = decodeLearnedState(buf)
    check not decoded.ok

  test "truncated/corrupt bytes are ignored (cold start), not a crash":
    var frontier = newCoverageFrontier("bin1")
    var cov = Coverage(counters: newSeq[uint8](8))
    cov.counters[0] = 1'u8
    discard admit(frontier, cov)
    let full = encodeLearnedState(newLearnedState(frontier.stats,
      newOperatorBandit(5), Dictionary()))
    # Cut off mid-field: the header is valid but the body is truncated.
    let truncated = full[0 ..< full.len - 3]
    let decoded = decodeLearnedState(truncated)
    check not decoded.ok

  test "a garbage dict-entry kind byte is ignored (cold start), not a crash":
    var dict: Dictionary
    dict.entries.add DictEntry(kind: dvInt, intVal: toInt128(1))
    let full = encodeLearnedState(newLearnedState(FrontierStats(), newOperatorBandit(3), dict))
    # Corrupt the dict entry's kind byte (the last byte before the int128
    # payload) to a value outside `DictValueKind`'s range.
    var corrupted = full
    corrupted[corrupted.len - 17] = 0xFF'u8   # kind byte precedes the 16-byte Int128
    let decoded = decodeLearnedState(corrupted)
    check not decoded.ok

  test "frontierHitCounts/frontierLastImprovedSeq length mismatch is rejected (R4)":
    ## Hand-crafted blob: each length-prefixed array individually passes
    ## `readBoundedCount` (its count fits the remaining buffer), but the
    ## two PAIRED arrays disagree with each other -- 2 hit-counts against
    ## 3 last-improved-seq entries. `encodeLearnedState` can never produce
    ## this (both are always written from the same source seq -- see
    ## `frontierStatsSnapshot`); this simulates storage-layer corruption or
    ## direct tampering, per the module doc's reachability note. Before the
    ## fix this decoded with `ok: true` and a 2-vs-3 length split, which is
    ## exactly what let `coverage.admit` read `lastImprovedSeq[i]` out of
    ## bounds after a mismatched restore (R4).
    var buf: seq[byte]
    for c in "NLS0": buf.add byte(c)
    buf.putU16(learnedStateVersion)
    buf.putU64(2)                                    # nHit = 2
    buf.putI64(10); buf.putI64(20)
    buf.putU64(3)                                    # nLast = 3 (MISMATCH)
    buf.putI64(1); buf.putI64(2); buf.putI64(3)
    buf.putI64(0)                                     # frontierTotalAdmitted
    buf.putI64(0)                                     # frontierLastGlobalImprovedSeq
    buf.putU64(0)                                     # nPulls
    buf.putU64(0)                                     # nRewards
    buf.putF64(0.0)                                    # banditTotalPulls
    buf.putU64(0)                                     # nDict
    let decoded = decodeLearnedState(buf)
    check not decoded.ok

  test "banditPulls/banditRewardSum length mismatch is rejected (R5)":
    ## Same shape of bug as the R4 test above, on the bandit pair instead
    ## of the frontier pair: 2 pulls against 1 reward-sum, each individually
    ## within bounds. Before the fix this decoded with `ok: true`, which is
    ## exactly what let `bandit.chooseOperator`'s decay loop index
    ## `rewardSum[i]` out of bounds on the first operator pick after a
    ## mismatched restore (R5).
    var buf: seq[byte]
    for c in "NLS0": buf.add byte(c)
    buf.putU16(learnedStateVersion)
    buf.putU64(0)                                     # nHit
    buf.putU64(0)                                     # nLast
    buf.putI64(0)                                     # frontierTotalAdmitted
    buf.putI64(0)                                     # frontierLastGlobalImprovedSeq
    buf.putU64(2)                                     # nPulls = 2
    buf.putF64(1.0); buf.putF64(2.0)
    buf.putU64(1)                                     # nRewards = 1 (MISMATCH)
    buf.putF64(5.0)
    buf.putF64(0.0)                                    # banditTotalPulls
    buf.putU64(0)                                     # nDict
    let decoded = decodeLearnedState(buf)
    check not decoded.ok

  test "matched-but-different-length pairs across the two pairings still round-trip":
    ## Guards against an over-eager fix that compares the WRONG pair (e.g.
    ## frontier count against bandit count instead of each pair against its
    ## own sibling). A frontier of 2 slots and a bandit of 5 arms is exactly
    ## the shape the first suite's main round-trip test already uses -- this
    ## test just makes the "different pairs may differ in length from each
    ## other, only siblings must match" property explicit.
    var frontier = newCoverageFrontier("bin1")
    var cov = Coverage(counters: newSeq[uint8](8))
    cov.counters[0] = 1'u8
    discard admit(frontier, cov)
    var bandit = newOperatorBandit(5)
    var rng = initSplitMix64(3)
    for i in 0 ..< 5: discard chooseOperator(bandit, rng)
    let original = newLearnedState(frontier.stats, bandit, Dictionary())
    check original.frontierHitCounts.len != original.banditPulls.len
    let decoded = decodeLearnedState(encodeLearnedState(original))
    check decoded.ok
    check decoded.state.frontierHitCounts == original.frontierHitCounts
    check decoded.state.frontierLastImprovedSeq == original.frontierLastImprovedSeq
    check decoded.state.banditPulls == original.banditPulls
    check decoded.state.banditRewardSum == original.banditRewardSum
