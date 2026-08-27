## RFC-fuzzer-nextgen R27: `OperatorSelector` (fuzzoperator.nim) exercised
## directly — no `fuzz()` campaign, no corpus, no `Orchestrator`. Proves the
## S2/S3 arm-space + bandit seam extracted from `fuzz[T]` really owns the
## arm list and the bandit together (an index into one always means the
## same arm in the other), and reproduces the exact pre-R27 arm-construction
## order and `rng` consumption.

import std/unittest
import nelli/[fuzzoperator, rng, bandit]

suite "OperatorSelector — arm-space construction (S2/S3)":

  test "base arm space: 5 arms, neither enableI2S nor havoc":
    let o = newOperatorSelector(enableI2S = false, uniformHavoc = true)
    check o.len == 5
    check armAt(o, 0) == maPerturbInt
    check armAt(o, 1) == maKindBoundary
    check armAt(o, 2) == maSpanSplice
    check armAt(o, 3) == maSpanDelete
    check armAt(o, 4) == maSpanDuplicate

  test "enableI2S alone (uniformHavoc still true): 6 arms, I2S appended last":
    let o = newOperatorSelector(enableI2S = true, uniformHavoc = true)
    check o.len == 6
    check armAt(o, 5) == maI2SReplace

  test "S3 on (uniformHavoc false), no I2S: 6 arms, interesting-value appended, no dict-insert":
    let o = newOperatorSelector(enableI2S = false, uniformHavoc = false)
    check o.len == 6
    check armAt(o, 5) == maInterestingValue

  test "S3 on AND enableI2S: 8 arms in construction order (I2S before interesting-value/dict-insert)":
    let o = newOperatorSelector(enableI2S = true, uniformHavoc = false)
    check o.len == 8
    check armAt(o, 0) == maPerturbInt
    check armAt(o, 1) == maKindBoundary
    check armAt(o, 2) == maSpanSplice
    check armAt(o, 3) == maSpanDelete
    check armAt(o, 4) == maSpanDuplicate
    check armAt(o, 5) == maI2SReplace
    check armAt(o, 6) == maInterestingValue
    check armAt(o, 7) == maDictInsert

suite "OperatorSelector — pick":

  test "pick(uniform=true) reproduces plain `rng.next mod len`, consuming rng identically":
    var o = newOperatorSelector(enableI2S = true, uniformHavoc = false)  # 8 arms
    var rngA = initSplitMix64(55'u64)
    var rngB = initSplitMix64(55'u64)
    check pick(o, rngA, true) == int(rngB.next mod 8'u64)

  test "pick(uniform=false) always returns a valid arm index":
    var o = newOperatorSelector(enableI2S = true, uniformHavoc = false)
    var rng = initSplitMix64(9'u64)
    for _ in 0 ..< 50:
      let p = pick(o, rng, false)
      check p >= 0 and p < o.len

  test "pick is deterministic in rng":
    var o1 = newOperatorSelector(enableI2S = false, uniformHavoc = false)
    var o2 = newOperatorSelector(enableI2S = false, uniformHavoc = false)
    var rngA = initSplitMix64(123'u64)
    var rngB = initSplitMix64(123'u64)
    for _ in 0 ..< 10:
      check pick(o1, rngA, false) == pick(o2, rngB, false)

suite "OperatorSelector — pick increments pulls; credit folds reward (bandit.nim's own split)":
  # `OperatorBandit.credit` (bandit.nim) only folds into `rewardSum`, never
  # `pulls` — `pulls` moves only via `chooseOperator`/`pick`. These tests
  # pin that `OperatorSelector` passes that split through unchanged rather
  # than accidentally conflating "picked" with "credited".

  test "pick increments the picked arm's pull count":
    var o = newOperatorSelector(enableI2S = false, uniformHavoc = true)
    var rng = initSplitMix64(3'u64)
    let p = pick(o, rng, false)
    check pullsOf(o, p) > 0.0

  test "credit alone (no prior pick) never changes any arm's pull count":
    var o = newOperatorSelector(enableI2S = false, uniformHavoc = true)
    credit(o, @[0, 1], 1.0)
    check pullsOf(o, 0) == 0.0
    check pullsOf(o, 1) == 0.0

  test "credit(picks) accepts every arm named, including repeats, without raising":
    var o = newOperatorSelector(enableI2S = false, uniformHavoc = true)
    var rng = initSplitMix64(4'u64)
    let a = pick(o, rng, false)
    let b = pick(o, rng, false)
    credit(o, @[a, b, a], 1.0)
    check pullsOf(o, a) > 0.0   # unaffected by credit, still reflects the picks above

  test "an uncredited, unpicked arm's pull count starts at 0":
    let o = newOperatorSelector(enableI2S = false, uniformHavoc = true)
    check pullsOf(o, 0) == 0.0

suite "OperatorSelector — checkpoint restore":

  test "restore replaces the bandit's learned pull counts directly":
    var o = newOperatorSelector(enableI2S = false, uniformHavoc = true)  # 5 arms
    check pullsOf(o, 0) == 0.0
    restore(o, @[5.0, 0.0, 0.0, 0.0, 0.0], @[10.0, 0.0, 0.0, 0.0, 0.0], 5.0)
    check pullsOf(o, 0) == 5.0
    check pullsOf(o, 1) == 0.0

  test "bandit() exposes the same underlying OperatorBandit `pick` mutates":
    var o = newOperatorSelector(enableI2S = false, uniformHavoc = true)
    var rng = initSplitMix64(8'u64)
    let p = pick(o, rng, false)
    check pullsOf(bandit(o), p) == pullsOf(o, p)
    check pullsOf(bandit(o), p) > 0.0
