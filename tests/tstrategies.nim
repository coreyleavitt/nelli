import std/unittest
import std/[math, unicode, tables, sets]
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

suite "built-in strategies: booleans and floats":
  test "booleans() yields both values and records a boolean choice":
    var ds = newDataSource(initSplitMix64(1))
    var sawTrue, sawFalse = false
    let s = booleans()
    for _ in 0 ..< 100:
      if s.generate(ds): sawTrue = true else: sawFalse = true
    check sawTrue and sawFalse
    check ds.recorded[0].kind == ckBoolean

  test "floats(lo,hi) stays within a finite range":
    var ds = newDataSource(initSplitMix64(2))
    let s = floats(-100.0, 100.0, allowNan = false)
    for _ in 0 ..< 300:
      let v = s.generate(ds)
      check v >= -100.0 and v <= 100.0
    check ds.recorded[0].kind == ckFloat

suite "built-in strategies: lists":
  test "lists respects length bounds and element constraints":
    var ds = newDataSource(initSplitMix64(7))
    let s = lists(integers(0, 9), minLen = 2, maxLen = 5)
    for _ in 0 ..< 300:
      let xs = s.generate(ds)
      check xs.len >= 2 and xs.len <= 5
      for x in xs:
        check x >= 0 and x <= 9

  test "lists is generated element-at-a-time (a continue-bool per element)":
    var ds = newDataSource(initSplitMix64(11))
    let xs = lists(integers(0, 9), minLen = 0, maxLen = 8).generate(ds)
    # one boolean precedes each element, plus one terminating boolean (unless capped)
    var bools, ints = 0
    for n in ds.recorded:
      if n.kind == ckBoolean: inc bools
      elif n.kind == ckInteger: inc ints
    check ints == xs.len
    check bools >= xs.len  # a continue-draw before each element

suite "built-in strategies: strings":
  test "strings stays within codepoint-length bounds":
    var ds = newDataSource(initSplitMix64(3))
    let s = strings(1, 10)
    for _ in 0 ..< 200:
      let v = s.generate(ds)
      check v.runeLen >= 1 and v.runeLen <= 10
    check ds.recorded[0].kind == ckString

suite "built-in strategies: tuples (variadic)":
  test "tuples(...) produces mixed-type tuples drawn from each strategy":
    let s = tuples(integers(1, 5), strings(1, 3), booleans())
    var ds = newDataSource(initSplitMix64(11))
    for _ in 0 ..< 50:
      let v = s.generate(ds)
      check v[0] in 1 .. 5
      check v[1].runeLen in 1 .. 3
      # v[2] is a bool — always valid
      discard v[2]

suite "built-in strategies: tables and sets":
  test "tables(keyStrat, valStrat) yields Table[K, V] with entries from each":
    let s = tables(integers(0, 9), strings(1, 3), minSize = 1, maxSize = 5)
    var ds = newDataSource(initSplitMix64(7))
    for _ in 0 ..< 30:
      let t = s.generate(ds)
      check t.len in 1 .. 5
      for k, v in t:
        check k in 0 .. 9
        check v.runeLen in 1 .. 3

  test "sets(elemStrat) yields HashSet[T] with elements from the strategy":
    let s = sets(integers(0, 9), minSize = 1, maxSize = 5)
    var ds = newDataSource(initSplitMix64(13))
    for _ in 0 ..< 30:
      let xs = s.generate(ds)
      check xs.len in 1 .. 5
      for x in xs:
        check x in 0 .. 9

suite "built-in strategies: arrays":
  test "arrays[N,T] always yields exactly N elements drawn from the inner strategy":
    let s = arrays[4, int](integers(0, 9))
    var ds = newDataSource(initSplitMix64(19))
    for _ in 0 ..< 50:
      let xs = s.generate(ds)
      # Static length is encoded in the type — the value is array[4, int],
      # so .len is the compile-time 4. Elements obey the inner constraint.
      check xs.len == 4
      for x in xs:
        check x in 0 .. 9
    # Exactly N draws per generated array — no continue-bool overhead.
    check ds.recorded.len == 50 * 4
    check ds.recorded[0].kind == ckInteger
