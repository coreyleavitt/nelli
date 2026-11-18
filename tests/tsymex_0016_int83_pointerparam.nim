## RFC-0016 INT-83 (precision): the walker declined a `pointer` parameter
## and a `pointer` field of a by-value parameter (`feUnsupportedParamType`),
## where a `ref` or `ptr` one is modelled. Found converting the ref family
## (K9d-10): `pinFind` generates a `pointer` domain (nil and the addresses of
## `ref int` cells), so every verdict below is pinned natively.
##
## A `pointer` is an address of its own sort, related to each typed sort by
## the casts (`cast[pointer](r)`, `pointer(q)`, `cast[ptr T](p)`), which keep
## the address both ways (heap_model.nim, the `pointer` section). The bar: a
## `pointer` parameter, field or element is nil or an address, compared with
## nil, with another `pointer` and with a typed address as Nim does; a read
## through `cast[ptr T](p)` is a cell of `T`; two objects of different types
## are two addresses; a location read at two types declines by name.
import std/[unittest, strutils]
import nelli/symex
from ./s8cu_helpers import pinFind

type
  PHolder = object
    tag: bool
    p: pointer
  A83 = object
    a: int
  B83 = object
    b: int

proc pNonNil(x: pointer) =
  if x != nil: symexTarget("hit")

proc pBothNil(x, y: pointer) =
  if x == nil and y == nil: symexTarget("hit")

proc pNeverBoth(x: pointer) =
  if x == nil and x != nil: symexTarget("hit")

proc pField(h: PHolder) =
  if h.tag and h.p == nil: symexTarget("hit")

proc pFieldNonNil(h: PHolder) =
  if not h.tag and h.p != nil and h.p.isNil: symexTarget("hit")

proc pSame(x, y: pointer) =
  if x != nil and x == y: symexTarget("hit")

proc pRead(x: pointer) =
  if x != nil and cast[ptr int](x)[] == 42: symexTarget("hit")

proc pRoundTrip(x: pointer) =
  if cast[pointer](cast[ptr int](x)) != x: symexTarget("hit")

proc pViaTyped(x: pointer; q: ptr int) =
  if q != nil and x == cast[pointer](q) and cast[ptr int](x)[] != q[]:
    symexTarget("hit")

proc pWriteThrough(x: pointer; q: ptr int) =
  if q != nil and x == pointer(q):
    q[] = 7
    if cast[ptr int](x)[] == 7: symexTarget("hit")

proc pWriteMissed(x: pointer; q: ptr int) =
  if q != nil and x == pointer(q):
    cast[ptr int](x)[] = 5
    if q[] != 5: symexTarget("hit")

proc pRefView(x: pointer; r: ref int) =
  if r != nil and cast[pointer](r) == x and cast[ref int](x)[] != r[]:
    symexTarget("hit")

proc pCrossType(a: ref A83; b: ref B83) =
  if a != nil and cast[pointer](a) == cast[pointer](b): symexTarget("hit")

proc pCrossNil(a: ref A83; b: ref B83) =
  if cast[pointer](a) == cast[pointer](b): symexTarget("hit")

proc pFresh(x: pointer) =
  let n = new int
  if x == cast[pointer](n): symexTarget("hit")

proc takesNil(x: pointer): bool = x == nil

proc pPassTyped(q: ptr int) =
  if not takesNil(q): symexTarget("hit")

proc pSeq(s: seq[pointer]) =
  if s.len == 2 and s[0] != nil and s[1] == nil: symexTarget("hit")

proc pPunned(x: pointer) =
  if x != nil and cast[ptr int](x)[] == 1 and cast[ptr float](x)[] == 0.0:
    symexTarget("hit")

template verdict(fn: typed): SymexStatusKind =
  ## the pinned verdict, its declines on a failure
  block:
    let r = pinFind(fn, tLabel("hit"))
    checkpoint $r.errors
    r.status

suite "INT-83: a pointer parameter is modelled, not declined":
  test "a pointer parameter compared with nil is sat, pinned on its witness":
    let r = pinFind(pNonNil, tLabel("hit"))
    checkpoint $r.errors
    check r.status == sxSat

  test "two pointer parameters":
    check verdict(pBothNil) == sxSat

  test "an impossible pointer test is unsat, pinned over the domain":
    check verdict(pNeverBoth) == sxUnsat

  test "a pointer field of a by-value parameter":
    check verdict(pField) == sxSat

  test "isNil of a non-nil pointer field is unsat":
    check verdict(pFieldNonNil) == sxUnsat

  test "two pointer parameters at one address":
    check verdict(pSame) == sxSat

  test "a read through cast[ptr int] is a cell of int":
    check verdict(pRead) == sxSat

  test "cast to ptr and back is the address":
    check verdict(pRoundTrip) == sxUnsat

  test "a pointer equal to a ptr reads that ptr's cell":
    check verdict(pViaTyped) == sxUnsat

  test "a write through the ptr is read through the pointer":
    check verdict(pWriteThrough) == sxSat

  test "a write through the pointer is read through the ptr":
    check verdict(pWriteMissed) == sxUnsat

  test "a pointer equal to a ref reads that ref's object":
    check verdict(pRefView) == sxUnsat

  test "objects of two types are two addresses":
    check verdict(pCrossType) == sxUnsat

  test "two nils of two types are one address":
    check verdict(pCrossNil) == sxSat

  test "a pointer parameter is no object the SUT allocates":
    check verdict(pFresh) == sxUnsat

  test "a ptr passed as a pointer keeps its address":
    check verdict(pPassTyped) == sxSat

  test "a seq of pointers declines by name (its witness is not rendered)":
    let r = pinFind(pSeq, tLabel("hit"))
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedWitnessType: named = true
    check named

  test "a location read at two types declines by name":
    let r = pinFind(pPunned, tLabel("hit"))
    check r.status == sxUnknown
    var named = false
    checkpoint $r.errors
    for e in r.errors:
      if e.kind == heUnresolvedRef: named = true
    check named

  test "the walker version is at least INT-83's":
    check parseInt(symexWalkerVersion) >= 443
