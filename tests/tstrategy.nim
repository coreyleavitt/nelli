import std/unittest
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

suite "Strategy: sampledFromWhere":
  test "draws only values satisfying the predicate":
    # The point of `sampledFromWhere` over `Strategy.filter` is that the
    # filter happens **at construction**, not at draw time. The rejection
    # budget isn't touched for non-matching items.
    let s = sampledFromWhere(@[1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
                             proc(x: int): bool = x mod 3 == 0)
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 40:
      let v = s.generate(ds)
      check v mod 3 == 0
      check v in @[3, 6, 9]

  test "raises ValueError at construction when no items match":
    expect ValueError:
      discard sampledFromWhere(@[1, 2, 3], proc(x: int): bool = x > 100)

suite "Strategy: just":
  test "just(x) always generates x and draws nothing":
    var ds = newDataSource(initSplitMix64(1))
    let s = just(42)
    check s.generate(ds) == 42
    check s.generate(ds) == 42
    check ds.recorded.len == 0  # a constant consumes no choices

suite "Strategy: integers":
  test "integers(lo,hi) draws within range and records one integer choice each":
    var ds = newDataSource(initSplitMix64(7))
    let s = integers(1, 6)
    for _ in 0 ..< 100:
      let v = s.generate(ds)
      check v >= 1 and v <= 6
    check ds.recorded.len == 100
    check ds.recorded[0].kind == ckInteger

suite "Strategy: map":
  test "map transforms values while preserving the underlying draw":
    var ds = newDataSource(initSplitMix64(1))
    let s = integers(0, 9).map(proc(x: int): string = $x)
    let v = s.generate(ds)
    check v.len >= 1
    check ds.recorded.len == 1          # the int choice is still recorded
    check ds.recorded[0].kind == ckInteger

  test "map composes on a constant":
    var ds = newDataSource(initSplitMix64(1))
    check just(21).map(proc(x: int): int = x * 2).generate(ds) == 42

suite "Strategy: filter":
  test "filter returns values that satisfy the predicate":
    var ds = newDataSource(initSplitMix64(1))
    let s = just(4).filter(proc(x: int): bool = x mod 2 == 0)
    check s.generate(ds) == 4

  test "filter raises Rejection when the predicate fails":
    var ds = newDataSource(initSplitMix64(1))
    let s = just(3).filter(proc(x: int): bool = x mod 2 == 0)
    expect Rejection:
      discard s.generate(ds)

suite "Strategy: flatMap":
  test "flatMap feeds the first value into the dependent strategy":
    var ds = newDataSource(initSplitMix64(5))
    let s = integers(1, 5).flatMap(proc(n: int): Strategy[int] = just(n * 100))
    let v = s.generate(ds)
    check ds.recorded.len == 1  # n drew once; just() draws nothing
    let n = toInt64(ds.recorded[0].intVal).int
    check n >= 1 and n <= 5
    check v == n * 100          # dependent strategy saw the real n

  test "flatMap's dependent strategy can itself draw":
    var ds = newDataSource(initSplitMix64(9))
    let s = integers(1, 3).flatMap(proc(n: int): Strategy[int] = integers(0, n))
    let v = s.generate(ds)
    check ds.recorded.len == 2
    let n = toInt64(ds.recorded[0].intVal).int
    check v >= 0 and v <= n

suite "Strategy: oneOf / sampledFrom":
  test "sampledFrom picks one of the given values and records an index":
    var ds = newDataSource(initSplitMix64(3))
    let s = sampledFrom(@["a", "b", "c"])
    for _ in 0 ..< 50:
      check s.generate(ds) in ["a", "b", "c"]
    check ds.recorded[0].kind == ckInteger

  test "oneOf chooses among strategies":
    var ds = newDataSource(initSplitMix64(4))
    let s = oneOf(@[just(1), integers(10, 20), just(99)])
    for _ in 0 ..< 50:
      let v = s.generate(ds)
      check v == 1 or v == 99 or (v >= 10 and v <= 20)

suite "Strategy: recursive":
  test "recursive(base, extend, maxDepth) bounds the recursion depth":
    # A self-referential "depth counter": base = 0; extend chooses leaf-or-grow.
    # Stand-in for any recursive structure (tree, AST, linked list, …).
    proc leaf(): Strategy[int] = just(0)
    proc extend(child: Strategy[int]): Strategy[int] =
      newStrategy(proc(src: var DataSource): int =
        if src.drawBoolean(0.5): 0          # stop here
        else: 1 + child.run(src))           # grow one level deeper
    let s = recursive(leaf(), extend, maxDepth = 4)
    var ds = newDataSource(initSplitMix64(1))
    var maxSeen = 0
    for _ in 0 ..< 200:
      let v = s.generate(ds)
      check v in 0 .. 4                     # depth cannot exceed maxDepth
      if v > maxSeen: maxSeen = v
    check maxSeen > 0                       # extension actually fired
