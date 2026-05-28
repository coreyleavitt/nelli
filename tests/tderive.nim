import std/unittest
import proptest

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

suite "derive: recursive types":
  # Direct self-reference: auto-derive must reject these with a helpful error.
  type
    RecTreeKind = enum rtLeaf, rtBranch
    RecTree = ref object
      case kind: RecTreeKind
      of rtLeaf: value: int
      of rtBranch:
        left: RecTree
        right: RecTree

  test "auto-derive refuses a directly-recursive type at compile time":
    check not compiles(arbitrary(RecTree))
