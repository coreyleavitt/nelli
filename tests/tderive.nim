import std/unittest
import proptest

type
  Pair = object
    x: int
    y: int

  Person = object
    name: string
    age: int

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

  test "arbitrary(Pair) derives a strategy for a plain object":
    let s = arbitrary(Pair)
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 20:
      discard s.generate(ds)
    check ds.recorded.len == 40  # 2 int draws per Pair × 20

  test "arbitrary(Person) works with mixed primitive field types":
    let s = arbitrary(Person)
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      discard v.name
      discard v.age
    check ds.recorded.len == 20  # 1 string + 1 int per Person × 10

  # Note: nested compound field types (e.g. seq[int] inside an object) hit a
  # runtime issue in the generated closure capture and are deferred.
