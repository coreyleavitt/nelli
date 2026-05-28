import std/unittest
import proptest

suite "DataSource: generation":
  test "drawBoolean records a node and honors the p=0/p=1 boundary":
    var ds = newDataSource(initSplitMix64(1))
    check ds.drawBoolean(0.0) == false  # p=0 ⇒ forced false
    check ds.drawBoolean(1.0) == true   # p=1 ⇒ forced true
    check ds.recorded.len == 2
    check ds.recorded[0].kind == ckBoolean
    check ds.recorded[0].wasForced
    check ds.recorded[1].wasForced
    check ds.recorded[1].boolVal == true

  test "drawBoolean with 0<p<1 records an unforced, permitted draw":
    var ds = newDataSource(initSplitMix64(123))
    let v = ds.drawBoolean(0.5)
    check ds.recorded.len == 1
    check not ds.recorded[0].wasForced
    check ds.recorded[0].boolVal == v

  test "drawInteger returns permitted values and records them":
    var ds = newDataSource(initSplitMix64(99))
    let c = IntConstraints(min: toInt128(10), max: toInt128(20),
                           shrinkTowards: toInt128(10))
    for _ in 0 ..< 50:
      let v = ds.drawInteger(toInt128(10), toInt128(20), toInt128(10))
      check c.permits(v)
    check ds.recorded.len == 50
    check ds.recorded[0].kind == ckInteger

  test "drawInteger over a singleton range is forced":
    var ds = newDataSource(initSplitMix64(1))
    check ds.drawInteger(toInt128(7), toInt128(7), toInt128(7)) == toInt128(7)
    check ds.recorded[0].wasForced

  test "drawInteger covers the full int64 and uint64 ranges without overflow":
    var ds = newDataSource(initSplitMix64(5))
    var sawHigh = false
    for _ in 0 ..< 300:
      let v = ds.drawInteger(toInt128(0'u64), toInt128(high(uint64)), toInt128(0))
      check toInt128(0'u64) <= v and v <= toInt128(high(uint64))
      if toInt128(high(int64)) < v: sawHigh = true
    check sawHigh  # must actually reach the uint64 upper half
    var ds2 = newDataSource(initSplitMix64(8))
    for _ in 0 ..< 200:
      let v = ds2.drawInteger(toInt128(low(int64)), toInt128(high(int64)), toInt128(0))
      check toInt128(low(int64)) <= v and v <= toInt128(high(int64))
