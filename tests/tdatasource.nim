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

suite "DataSource: replay":
  test "replay reproduces the recorded values exactly":
    var gen = newDataSource(initSplitMix64(42))
    let a = gen.drawInteger(toInt128(0), toInt128(1000), toInt128(0))
    let b = gen.drawBoolean(0.5)
    let c = gen.drawInteger(toInt128(-50), toInt128(50), toInt128(0))
    let recorded = gen.recorded

    var rep = newReplaySource(recorded)
    check rep.drawInteger(toInt128(0), toInt128(1000), toInt128(0)) == a
    check rep.drawBoolean(0.5) == b
    check rep.drawInteger(toInt128(-50), toInt128(50), toInt128(0)) == c
    check rep.recorded == recorded  # replay reconstructs the sequence

  test "drawing past the end of the sequence raises Overrun":
    var rep = newReplaySource(@[integerChoice(5, 0, 10, 0)])
    discard rep.drawInteger(toInt128(0), toInt128(10), toInt128(0))
    expect Overrun:
      discard rep.drawInteger(toInt128(0), toInt128(10), toInt128(0))

  test "a kind mismatch during replay is treated as Overrun":
    var rep = newReplaySource(@[integerChoice(5, 0, 10, 0)])
    expect Overrun:
      discard rep.drawBoolean(0.5)

suite "DataSource: float draws":
  test "drawFloat returns permitted values and records them":
    var ds = newDataSource(initSplitMix64(7))
    let c = FloatConstraints(min: -1e9, max: 1e9, allowNan: false,
                             smallestNonzeroMagnitude: 1e-6)
    for _ in 0 ..< 300:
      let v = ds.drawFloat(-1e9, 1e9, allowNan = false,
                           smallestNonzeroMagnitude = 1e-6)
      check c.permits(v)
    check ds.recorded.len == 300
    check ds.recorded[0].kind == ckFloat

  test "drawFloat replays bit-exactly (NaN and signed zero included)":
    var gen = newDataSource(initSplitMix64(3))
    for _ in 0 ..< 80:
      discard gen.drawFloat(-1e30, 1e30, allowNan = true,
                            smallestNonzeroMagnitude = 1e-300)
    var rep = newReplaySource(gen.recorded)
    for _ in 0 ..< 80:
      discard rep.drawFloat(-1e30, 1e30, allowNan = true,
                            smallestNonzeroMagnitude = 1e-300)
    check rep.recorded == gen.recorded

suite "DataSource: bytes and string draws":
  test "drawBytes returns permitted values and records them":
    var ds = newDataSource(initSplitMix64(11))
    let c = BytesConstraints(minSize: 2, maxSize: 6)
    for _ in 0 ..< 200:
      check c.permits(ds.drawBytes(2, 6))
    check ds.recorded.len == 200
    check ds.recorded[0].kind == ckBytes

  test "drawString returns permitted values and records them":
    var ds = newDataSource(initSplitMix64(13))
    let iv = intervals([(0x61'i32, 0x7a'i32), (0x30'i32, 0x39'i32)])  # a-z, 0-9
    let c = StringConstraints(intervals: iv, minSize: 0, maxSize: 8)
    for _ in 0 ..< 200:
      check c.permits(ds.drawString(iv, 0, 8))
    check ds.recorded[0].kind == ckString

  test "bytes and string replay exactly":
    var gen = newDataSource(initSplitMix64(21))
    let iv = intervals([(0x61'i32, 0x7a'i32)])
    for _ in 0 ..< 30:
      discard gen.drawBytes(0, 10)
      discard gen.drawString(iv, 0, 10)
    var rep = newReplaySource(gen.recorded)
    for _ in 0 ..< 30:
      discard rep.drawBytes(0, 10)
      discard rep.drawString(iv, 0, 10)
    check rep.recorded == gen.recorded
