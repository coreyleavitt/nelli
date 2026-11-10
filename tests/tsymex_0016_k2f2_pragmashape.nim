## RFC-0016 K2F-2 (section 8.1): every shape of type a pragma-carrying type
## can reach `typePragmaHit` / `layoutPragmaOf` through. A type whose pragma
## the walk does not see is admitted, so a verdict over it is trusted though
## native's layout differs (`{.union.}` overlays `lo` and `all`).
import std/[unittest, strutils, options, tables, macros]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/canonicalize
import nelli/smt/pragmaaxes
import nelli/smt/errorkind
import nelli/smt/dsl_typebridge
import ./s8cu_helpers

type
  Un {.union.} = object
    lo: int32
    all: int64
  UnAlias = Un
  UnGen[T] {.union.} = object
    lo: T
    all: int64
  UnRef = ref Un
  UnKid = object
    u: Un
  UnTup = tuple[a: int, u: Un]
  Bit = object
    f {.bitsize: 3.}: int
  BitGen[T] = object
    f {.bitsize(3).}: T
  BitRef = ref object
    f {.bitsize: 3.}: int
  BitParent = object of RootObj
    f {.bitsize: 3.}: int
  BitChild = object of BitParent
    g: int
  BitRefChild = ref object of RootObj
    f {.bitsize: 3.}: int
  BitCase = object
    case k: bool
    of true:
      f {.bitsize: 3.}: int
    of false:
      h: int

type
  PackedAligned {.packed.} = object
    case k: bool
    of true:
      f {.align: 8.}: int32
    of false:
      h: int8
  PackedUnion {.packed, union.} = object
    a: int32
    b: int64
  PackedOnly {.packed.} = object
    case k: bool
    of true:
      f: int32
    of false:
      h: int8
  CaseOnlyBit = object
    case k: bool
    of true:
      f {.bitsize: 3.}: int
    of false:
      h: int

macro layoutOf(t: typedesc): string =
  let sym = t.getTypeInst[1]
  let impl = sym.getImpl
  newLit(layoutPragmaOf(sym, impl[2][2]))

macro nameOfShape(kind: static NimNodeKind): string =
  ## `pragmaName` of an entry of the given kind with one child `align`.
  let n = newNimNode(kind)
  if kind == nnkDotExpr: n.add ident"m"
  n.add ident"align"
  newLit(pragmaName(n))

proc varParam(u: var Un; x: int) =
  u.lo = int32(x)
  if u.all == 5: symexTarget("hit")

proc aliasLocal(x: int) =
  var u: UnAlias
  u.all = 0
  u.lo = int32(x)
  if u.all == 5: symexTarget("hit")

proc seqLocal(x: int) =
  var s = newSeq[Un](1)
  s[0].all = 0
  s[0].lo = int32(x)
  if s[0].all == 5: symexTarget("hit")

proc arrLocal(x: int) =
  var s: array[1, Un]
  s[0].all = 0
  s[0].lo = int32(x)
  if s[0].all == 5: symexTarget("hit")

proc optLocal(x: int) =
  var o = some(Un())
  o.get.all = 0
  o.get.lo = int32(x)
  if o.get.all == 5: symexTarget("hit")

proc refLocal(x: int) =
  var r = UnRef()
  r.all = 0
  r.lo = int32(x)
  if r.all == 5: symexTarget("hit")

proc genLocal(x: int) =
  var u: UnGen[int32]
  u.all = 0
  u.lo = int32(x)
  if u.all == 5: symexTarget("hit")

proc tupLocal(x: int) =
  var t: UnTup
  t.u.all = 0
  t.u.lo = int32(x)
  if t.u.all == 5: symexTarget("hit")

proc openArr(s: openArray[Un]; x: int) =
  if s.len > 0 and s[0].all == 5 and x == 1: symexTarget("hit")

proc varSeq(s: var seq[Un]; x: int) =
  if s.len > 0 and s[0].all == 5 and x == 1: symexTarget("hit")

proc sinkParam(u: sink Un; x: int) =
  if u.all == 5 and x == 1: symexTarget("hit")

proc lentParam(u: Un; x: int) =
  if u.all == 5 and x == 1: symexTarget("hit")


proc bitGen(x: int) =
  var o: BitGen[int]
  o.f = x
  if o.f != x: symexTarget("hit")

proc bitRef(x: int) =
  var o = BitRef()
  o.f = x
  if o.f != x: symexTarget("hit")

proc bitChild(x: int) =
  var o: BitChild
  o.f = x
  if o.f != x: symexTarget("hit")

proc bitRefChild(x: int) =
  var o = BitRefChild()
  o.f = x
  if o.f != x: symexTarget("hit")

proc bitCase(x: int) =
  var o = BitCase(k: true)
  o.f = x
  if o.f != x: symexTarget("hit")



suite "RFC-0016 K2F-2: type shapes the type pragma walk must reach":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 316

  test "native: the union overlays lo and all":
    var u: Un
    u.all = 0
    u.lo = 5
    check u.all == 5

  test "a var parameter of a union type declines":
    pinDecline(varParam, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "an alias of a union type is never trusted":
    check not symexFind(aliasLocal, tLabel("hit")).trusted
  test "a seq of a union type declines":
    pinDecline(seqLocal, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "an array of a union type declines":
    pinDecline(arrLocal, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "an Option of a union type is never trusted":
    check not symexFind(optLocal, tLabel("hit")).trusted
  test "a ref to a union type declines":
    pinDecline(refLocal, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "a generic union instance declines":
    pinDecline(genLocal, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "a tuple holding a union declines":
    pinDecline(tupLocal, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "an openArray of a union type declines":
    pinDecline(openArr, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "a var seq of a union type declines":
    pinDecline(varSeq, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "a sink parameter of a union type declines":
    pinDecline(sinkParam, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
  test "a by-value parameter of a union type declines":
    pinDecline(lentParam, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")

  test "a bitsize field of a generic object declines":
    pinDecline(bitGen, cellKey(axPragma, "field/bitsize"), feUnsupportedOp,
               needle = "pragma:field/bitsize")
  test "a bitsize field of a ref object declines":
    pinDecline(bitRef, cellKey(axPragma, "field/bitsize"), feUnsupportedOp,
               needle = "pragma:field/bitsize")
  test "a bitsize field of the parent object declines":
    pinDecline(bitChild, cellKey(axPragma, "field/bitsize"), feUnsupportedOp,
               needle = "pragma:field/bitsize")
  test "a bitsize field of a ref object's parent declines":
    pinDecline(bitRefChild, cellKey(axPragma, "field/bitsize"),
               feUnsupportedOp, needle = "pragma:field/bitsize")
  test "a bitsize field of a variant arm declines":
    pinDecline(bitCase, cellKey(axPragma, "field/bitsize"), feUnsupportedOp,
               needle = "pragma:field/bitsize")


suite "RFC-0016 K2F-2: layoutPragmaOf and pragmaName read every entry":
  test "a packed type with an align field is not the packed layout":
    check layoutOf(PackedAligned) == "align"
  test "packed beside union is the union, not the packed layout":
    check layoutOf(PackedUnion) == "union"
  test "a bare packed variant is packed":
    check layoutOf(PackedOnly) == "packed"
  test "a bitsize field in a body that is one case":
    check layoutOf(CaseOnlyBit) == "bitsize"
  test "pragmaName names the shapes a pragma entry takes":
    check nameOfShape(nnkCall) == "align"
    check nameOfShape(nnkExprColonExpr) == "align"
    check nameOfShape(nnkCallStrLit) == "align"
    check nameOfShape(nnkBracketExpr) == "align"
    check nameOfShape(nnkDotExpr) == "align"
  test "pragmaName answers the unnamed sentinel for a shape with no name":
    check nameOfShape(nnkPar) == unnamedPragma
    check unnamedPragma == "?"
    check admitPragma(ppType, unnamedPragma, psTypeDecl).decline[0] ==
      some(feUnadmitted)
    check admitPragma(ppField, unnamedPragma, psFieldDecl).decline[0] ==
      some(feUnadmitted)
