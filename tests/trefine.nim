import std/[unittest, times]
import proptest
import proptest/[datasource, rng]

# #111 — refinement-type derive.
#
# Nim's range[lo..hi], Natural, Positive, and named range aliases
# carry compile-time refinement info the macro should consume. After
# this PR, `arbitrary(range[1..100])` produces `integers(1, 100)`
# directly, with bounds enforced by the strategy (not by post-filter).

suite "arbitrary range[lo..hi] derivation":
  test "arbitrary(range[1..10]) draws values in [1, 10]":
    let s = arbitrary(range[1..10])
    var ds = newDataSource(initSplitMix64(0x42))
    for _ in 0 ..< 200:
      let v = s.generate(ds)
      check int(v) >= 1
      check int(v) <= 10

  test "arbitrary(Natural) draws values >= 0":
    let s = arbitrary(Natural)
    var ds = newDataSource(initSplitMix64(0x99))
    for _ in 0 ..< 200:
      let v = s.generate(ds)
      check int(v) >= 0

  test "arbitrary(Positive) draws values >= 1":
    let s = arbitrary(Positive)
    var ds = newDataSource(initSplitMix64(0x77))
    for _ in 0 ..< 200:
      let v = s.generate(ds)
      check int(v) >= 1

  test "named alias `type MyR = range[5..15]` derives in [5, 15]":
    type MyR = range[5..15]
    let s = arbitrary(MyR)
    var ds = newDataSource(initSplitMix64(0x33))
    for _ in 0 ..< 200:
      let v = s.generate(ds)
      check int(v) >= 5
      check int(v) <= 15

  test "object with a range field derives the field in bounds":
    type Account = object
      balance: range[0..1_000_000]
      level: range[1..100]
    let s = arbitrary(Account)
    var ds = newDataSource(initSplitMix64(0x55))
    for _ in 0 ..< 100:
      let a = s.generate(ds)
      check int(a.balance) >= 0
      check int(a.balance) <= 1_000_000
      check int(a.level) >= 1
      check int(a.level) <= 100

  test "distinct over range preserves the bound":
    type UserId = distinct range[1..100_000]
    let s = arbitrary(UserId)
    var ds = newDataSource(initSplitMix64(0x66))
    for _ in 0 ..< 100:
      let id = s.generate(ds)
      check int(id) >= 1
      check int(id) <= 100_000
