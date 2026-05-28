import std/[unittest, tables, sets]
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

type
  Pair = object
    x: int
    y: int

  Person = object
    name: string
    age: int

  WithList = object
    label: string
    items: seq[int]

  Color = enum
    red, green, blue

  Direction = enum
    north, south, east, west

  HoleEnum = enum
    heA = 1
    heB = 3
    heC = 5
    heD = 11

  RefP = ref object
    x: int
    y: int

  Node = ref object
    value: int
    name: string

  ShapeKind = enum skCircle, skSquare, skTriangle

  Shape = object
    case kind: ShapeKind
    of skCircle: radius: float
    of skSquare: side: float
    of skTriangle:
      base: float
      height: float

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

  test "arbitrary(WithList) handles a seq[int] field inside an object":
    let s = arbitrary(WithList)
    var ds = newDataSource(initSplitMix64(1))
    var sawAny = false
    for _ in 0 ..< 30:
      let v = s.generate(ds)
      if v.items.len > 0 or v.label.len > 0: sawAny = true
    check sawAny

suite "derive: enums":
  test "arbitrary(Color) eventually yields every enum value":
    let s = arbitrary(Color)
    var ds = newDataSource(initSplitMix64(1))
    var got: set[Color]
    for _ in 0 ..< 50: got.incl s.generate(ds)
    check got == {red, green, blue}

  test "arbitrary(Direction) covers all four values":
    let s = arbitrary(Direction)
    var ds = newDataSource(initSplitMix64(7))
    var got: set[Direction]
    for _ in 0 ..< 100: got.incl s.generate(ds)
    check got == {north, south, east, west}

  test "arbitrary(HoleEnum) yields only declared values and covers all of them":
    # Ordinals 0, 2, 4, 6..10, 12+ are NOT declared values; only 1, 3, 5, 11 are.
    let s = arbitrary(HoleEnum)
    var ds = newDataSource(initSplitMix64(3))
    var got: set[HoleEnum]
    for _ in 0 ..< 400:
      let v = s.generate(ds)
      check ord(v) in {1, 3, 5, 11}  # never an undeclared ordinal
      got.incl v
    check got == {heA, heB, heC, heD}  # eventually all declared values appear

suite "derive: ref objects":
  test "arbitrary(RefP) returns a non-nil ref with fields drawn":
    let s = arbitrary(RefP)
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      check not v.isNil
      discard v.x
      discard v.y
    check ds.recorded.len == 20  # 2 ints per ref × 10

  test "arbitrary(Node) handles a ref with a string field":
    let s = arbitrary(Node)
    var ds = newDataSource(initSplitMix64(2))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      check not v.isNil
      discard v.value
      discard v.name

suite "derive: tuples":
  test "arbitrary(tuple[a, b: int]) yields named-tuple values":
    let s = arbitrary(tuple[a: int, b: int])
    var ds = newDataSource(initSplitMix64(1))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      discard v.a
      discard v.b
    check ds.recorded.len == 20

  test "arbitrary(tuple) with mixed primitive fields":
    let s = arbitrary(tuple[name: string, age: int])
    var ds = newDataSource(initSplitMix64(2))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      discard v.name
      discard v.age

suite "derive: object variants":
  test "arbitrary(Shape) draws the discriminator first and matches the branch":
    let s = arbitrary(Shape)
    var ds = newDataSource(initSplitMix64(1))
    var saw: set[ShapeKind]
    for _ in 0 ..< 50:
      let v = s.generate(ds)
      saw.incl v.kind
      case v.kind
      of skCircle: discard v.radius
      of skSquare: discard v.side
      of skTriangle:
        discard v.base
        discard v.height
    check saw.len >= 2  # variants are actually being chosen
    check ds.recorded[0].kind == ckInteger  # discriminator drawn first

suite "derive: arrays / tables / sets":
  test "arbitrary(array[4, int]) yields fixed-length int arrays":
    let s = arbitrary(array[4, int])
    var ds = newDataSource(initSplitMix64(2))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      check v.len == 4
    check ds.recorded.len == 40
    check ds.recorded[0].kind == ckInteger

  test "arbitrary(set[Color]) yields a Nim bitset with elements drawn from the enum":
    let s = arbitrary(set[Color])
    var ds = newDataSource(initSplitMix64(13))
    var sawNonEmpty, sawEmpty = false
    for _ in 0 ..< 100:
      let v = s.generate(ds)
      # Static type guarantees set[Color]; just confirm membership is valid.
      for c in v: check c in {red, green, blue}
      if v.len > 0: sawNonEmpty = true else: sawEmpty = true
    check sawNonEmpty and sawEmpty

  test "arbitrary(HashSet[int]) recurses on element type":
    let s = arbitrary(HashSet[int])
    var ds = newDataSource(initSplitMix64(8))
    var sawAny = false
    for _ in 0 ..< 30:
      let h = s.generate(ds)
      if h.len > 0: sawAny = true
    check sawAny

  test "arbitrary(Table[int, string]) recurses on key and value types":
    let s = arbitrary(Table[int, string])
    var ds = newDataSource(initSplitMix64(5))
    var sawAny = false
    for _ in 0 ..< 30:
      let t = s.generate(ds)
      if t.len > 0:
        sawAny = true
        for k, v in t:
          discard k
          discard v
    check sawAny

suite "derive: distinct types":
  type
    UserId = distinct int
    Email = distinct string

  test "arbitrary(distinct int) draws an int and wraps it":
    let s = arbitrary(UserId)
    var ds = newDataSource(initSplitMix64(4))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      discard int(v)
    check ds.recorded.len == 10
    check ds.recorded[0].kind == ckInteger

  test "arbitrary(distinct string) draws a string and wraps it":
    let s = arbitrary(Email)
    var ds = newDataSource(initSplitMix64(7))
    for _ in 0 ..< 5:
      let v = s.generate(ds)
      discard string(v)
    check ds.recorded[0].kind == ckString

suite "derive: generic instantiation":
  type
    Box[T] = object
      v: T
    Pair2[A, B] = object
      a: A
      b: B

  test "arbitrary(Box[int]) instantiates a generic object":
    let s = arbitrary(Box[int])
    var ds = newDataSource(initSplitMix64(9))
    for _ in 0 ..< 10:
      let v = s.generate(ds)
      discard v.v
    check ds.recorded.len == 10
    check ds.recorded[0].kind == ckInteger

  test "arbitrary(Pair2[int, string]) instantiates a two-param generic":
    let s = arbitrary(Pair2[int, string])
    var ds = newDataSource(initSplitMix64(11))
    for _ in 0 ..< 5:
      let v = s.generate(ds)
      discard v.a
      discard v.b
    check ds.recorded.len == 10  # one int + one string per Pair2 × 5

suite "derive: recursive types":
  # Direct self-reference: auto-derive synthesizes a leaf wherever possible
  # (variant non-recursive branches; nil for recursive ref fields; empty for
  # collection fields of self).
  type
    RecTreeKind = enum rtLeaf, rtBranch
    RecTree = ref object
      case kind: RecTreeKind
      of rtLeaf: value: int
      of rtBranch:
        left: RecTree
        right: RecTree

  proc depth(t: RecTree): int =
    if t.isNil: return 0
    case t.kind
    of rtLeaf: 1
    of rtBranch: 1 + max(depth(t.left), depth(t.right))

  test "auto-derive refuses mutually-recursive types at compile time":
    # Without compile-time detection of the cycle, the generated strategy
    # for A would recurse through arbitrary(B) which recurses through
    # arbitrary(A), infinite-looping the macro expansion or — worse —
    # generating code that infinite-loops at runtime. The macro must spot
    # the cycle and emit a compile-time error.
    type
      MutA = ref object
        bs: seq[MutB]
      MutB = ref object
        a: MutA
    check not compiles(arbitrary(MutA))
    check not compiles(arbitrary(MutB))

  test "auto-derive synthesizes recursive() for a variant ref tree":
    let s = arbitrary(RecTree)
    var ds = newDataSource(initSplitMix64(17))
    var sawBranch = false
    for _ in 0 ..< 50:
      let v = s.generate(ds)
      check not v.isNil
      check depth(v) <= 8  # bounded depth — never blows up
      if v.kind == rtBranch: sawBranch = true
    check sawBranch  # extends past the leaf at least once
