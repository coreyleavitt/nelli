## RFC-fuzzer-nextgen S2: the operator bandit (`nelli/bandit.nim`), tested in
## isolation from the fuzz loop — pure `OperatorBandit`/`chooseOperator`/
## `credit`, deterministic in an explicit `SplitMix64`. The RFC's four
## RED-able properties (an operator with higher recent admission yield is
## selected strictly more often; a cold/unused operator still gets nonzero
## exploration; decay/window handles non-stationarity; the I2S arm
## participates when `enableI2S`) — the first three are proven here at the
## bandit level; the fourth (loop wiring) is proven in `tfuzzi2s.nim`/
## `tfuzzloop.nim` against the real fuzz loop.

import std/unittest
import nelli
import nelli/rng

suite "operator bandit (RFC-fuzzer-nextgen S2)":
  test "an operator with higher recent admission yield is selected strictly more often":
    var b = newOperatorBandit(5)
    var rng = initSplitMix64(1)
    var counts = newSeq[int](5)
    const N = 4000
    for i in 0 ..< N:
      let arm = chooseOperator(b, rng)
      inc counts[arm]
      if arm == 0: credit(b, arm, 1.0)   # arm 0 always "admits"; the rest never do
    check counts[0] > counts[1]
    check counts[0] > counts[2]
    check counts[0] > counts[3]
    check counts[0] > counts[4]
    # Should dominate, not just edge out — the productive arm gets the bulk
    # of post-warmup pulls.
    check counts[0] > N div 2

  test "a cold/unused operator still gets nonzero exploration (never permanently starved)":
    var b = newOperatorBandit(5)
    var rng = initSplitMix64(2)
    var counts = newSeq[int](5)
    const N = 6000
    const trailingStart = N - 1000
    for i in 0 ..< N:
      let arm = chooseOperator(b, rng)
      if i >= trailingStart: inc counts[arm]
      if arm == 0: credit(b, arm, 1.0)   # only arm 0 ever admits, for the WHOLE run
    # Every arm — including the persistently-zero-yield ones — is still
    # chosen at least once in the trailing window, long after the initial
    # one-pass cold start has ended.
    for arm in 1 ..< 5:
      check counts[arm] > 0

  test "decay/window: an operator that WAS productive but stops loses share over time (non-stationarity)":
    var b = newOperatorBandit(2)
    var rng = initSplitMix64(3)
    const half = 1500
    for i in 0 ..< half:
      let arm = chooseOperator(b, rng)
      if arm == 0: credit(b, arm, 1.0)   # arm 0 productive in phase 1
    # Phase 2: arm 0 stops yielding, arm 1 starts.
    var counts = newSeq[int](2)
    const phase2 = 1500
    const trailingStart = phase2 - 300
    for i in 0 ..< phase2:
      let arm = chooseOperator(b, rng)
      if i >= trailingStart: inc counts[arm]
      if arm == 1: credit(b, arm, 1.0)
    # By the end of phase 2, the schedule has adapted: arm 1 (now
    # productive) is favored over arm 0 (lifetime-dominant but stale) in
    # the trailing window.
    check counts[1] > counts[0]

  test "chooseOperator is deterministic in the RNG seed":
    var b1 = newOperatorBandit(6)
    var b2 = newOperatorBandit(6)
    var r1 = initSplitMix64(42)
    var r2 = initSplitMix64(42)
    for i in 0 ..< 500:
      let a1 = chooseOperator(b1, r1)
      let a2 = chooseOperator(b2, r2)
      check a1 == a2
      if a1 mod 3 == 0: credit(b1, a1, 1.0)
      if a2 mod 3 == 0: credit(b2, a2, 1.0)

  test "credit on an out-of-range arm is a no-op, not a crash":
    var b = newOperatorBandit(3)
    credit(b, -1, 1.0)
    credit(b, 99, 1.0)
    check armCount(b) == 3
