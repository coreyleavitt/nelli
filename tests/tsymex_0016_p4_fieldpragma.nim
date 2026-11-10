## RFC-0016 W3-z P4 (finding A3): a field's own pragma list is a place of the
## pragma axis. `f {.bitsize: 3.}: int` keeps three bits of every store, so a
## verdict over the full-width slot the object model keeps is not native's;
## `bitsize` and `align` decline until modelled, a name with no row declines,
## and the benign ones (`deprecated`, `requiresInit`) are exact.
import std/[unittest, strutils, options]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/canonicalize
import nelli/smt/pragmaaxes
import nelli/smt/errorkind
import ./s8cu_helpers

{.pragma: narrow, bitsize: 3.}
{.pragma: lay, union.}

type
  BitObj = object
    f {.bitsize: 3.}: int
  AlignObj = object
    pad: int8
    f {.align: 8.}: int32
  Inner = object
    g {.bitsize: 3.}: int
  Outer = object
    inner: Inner
  Variant = object
    case k: bool
    of true:
      f {.bitsize: 3.}: int
    of false:
      h: int
  NarrowObj = object
    f {.narrow.}: int
  DepObj = object
    f {.deprecated.}: int
    g*: int
  InitObj = object
    f {.requiresInit.}: int
  AliasU {.lay.} = object
    lo: int32
    all: int64

proc bitsizeRoundTrip(x: int) =
  var o: BitObj
  o.f = x
  if o.f != x: symexTarget("hit")

proc alignRoundTrip(x: int) =
  var o: AlignObj
  o.f = int32(x)
  if o.f != int32(x): symexTarget("hit")

proc nestedBitsize(x: int) =
  var o: Outer
  o.inner.g = x
  if o.inner.g != x: symexTarget("hit")

proc variantBitsize(x: int) =
  var o = Variant(k: true)
  o.f = x
  if o.f != x: symexTarget("hit")

proc aliasedBitsize(x: int) =
  var o: NarrowObj
  o.f = x
  if o.f != x: symexTarget("hit")

proc deprecatedField(x: int) =
  var o: DepObj
  o.f = x
  o.g = x
  if o.f != o.g: symexTarget("hit")

proc requiresInitField(x: int) =
  let o = InitObj(f: x)
  if o.f == 5: symexTarget("hit")

proc aliasUnion(x: int) =
  var u: AliasU
  u.all = 0
  u.lo = int32(x)
  if u.all == 5: symexTarget("hit")

suite "RFC-0016 W3-z P4: the field place of the pragma axis":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 315

  test "native: a 3-bit field loses a store of 8 (the hit the walk must not refute)":
    var o: BitObj
    o.f = 8
    check o.f != 8

  test "the table has a field place; bitsize and align decline":
    check admitPragma(ppField, "bitsize", psFieldDecl).decline[0] ==
      some(feUnsupportedOp)
    check admitPragma(ppField, "align", psFieldDecl).decline[0] ==
      some(feUnsupportedOp)
    check admitPragma(ppField, "deprecated", psFieldDecl).admitted
    check admitPragma(ppField, "neverHeardOfIt", psFieldDecl).decline[0] ==
      some(feUnadmitted)

  test "a bitsize field of a plain record declines":
    pinDecline(bitsizeRoundTrip, cellKey(axPragma, "field/bitsize"),
               feUnsupportedOp, needle = "pragma:field/bitsize")

  test "an align field of a plain record declines":
    pinDecline(alignRoundTrip, cellKey(axPragma, "field/align"),
               feUnsupportedOp, needle = "pragma:field/align")

  test "a bitsize field of a record nested in another declines":
    pinDecline(nestedBitsize, cellKey(axPragma, "field/bitsize"),
               feUnsupportedOp, needle = "pragma:field/bitsize")

  test "a bitsize field of a variant arm declines":
    pinDecline(variantBitsize, cellKey(axPragma, "field/bitsize"),
               feUnsupportedOp, needle = "pragma:field/bitsize")

  test "A6: a field pragma alias is expanded by getImpl, so it declines too":
    pinDecline(aliasedBitsize, cellKey(axPragma, "field/bitsize"),
               feUnsupportedOp, needle = "pragma:field/bitsize")

  test "a deprecated field and an exported field are exact":
    discard pinExact(deprecatedField, cellKey(axPragma, "field/deprecated"))

  test "a requiresInit field is exact":
    discard pinExact(requiresInitField, cellKey(axPragma, "field/requiresInit"))

  test "A6: a pragma alias carrying union reaches the type place":
    pinDecline(aliasUnion, cellKey(axPragma, "type/union"), feUnsupportedOp,
               needle = "pragma:type/union")
