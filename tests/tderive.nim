import std/unittest
import proptest

suite "derive: arbitrary primitives":
  test "arbitrary(int) produces an integer strategy":
    let s = arbitrary(int)
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 100:
      discard s.generate(ds)
    check ds.recorded.len == 100
    check ds.recorded[0].kind == ckInteger

  test "arbitrary(bool) yields both values":
    let s = arbitrary(bool)
    var ds = newDataSource(initSplitMix64(1))
    var sawT, sawF = false
    for _ in 0 ..< 100:
      if s.generate(ds): sawT = true else: sawF = true
    check sawT and sawF

  test "arbitrary(float) produces a float strategy":
    let s = arbitrary(float)
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 50:
      discard s.generate(ds)
    check ds.recorded[0].kind == ckFloat

  test "arbitrary(string) produces a string strategy":
    let s = arbitrary(string)
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 20:
      discard s.generate(ds)
    check ds.recorded[0].kind == ckString

suite "derive: compound types":
  test "arbitrary(seq[int]) recurses on the element type":
    let s = arbitrary(seq[int])
    var ds = newDataSource(initSplitMix64(1))
    var maxLen = 0
    for _ in 0 ..< 50:
      let v = s.generate(ds)
      if v.len > maxLen: maxLen = v.len
    check maxLen > 0  # generated at least one non-empty seq
