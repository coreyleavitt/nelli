## RFC-0016 INT-90 (precision): two `ptr` parameters of different pointee
## types at one address (`a: ptr int`, `b: ptr float`,
## `cast[pointer](a) == cast[pointer](b)`) hold one cell's bytes, but the walk
## kept a separate heap per pointee sort and did not relate them at a shared
## address. `a[] == 5 and b[] > 1.0` is natively unreachable (the int 5's bits
## read as a float are a subnormal far below 1.0), yet the walker answered an
## untrusted, lossy `sxSat` (INT-88 marks the witness lossy, so the replay
## settles it) instead of `sxUnsat`. Left by INT-88, whose witness builder
## made the shared cell one allocation.
##
## The bar: a value constrained or written at one sort determines the read at
## another sort at the same address, so the cross-sort target is `sxUnsat`,
## pinned natively by pinFind over the `ptr` domains (which put the two
## parameters at one address); a cross-sort target the bytes do admit stays
## `sxSat`. Fixed in the walk (451): a read or a write of an exact-layout
## view (a fixed-width integer, a float, a flat padding-free object of those)
## at an address the run also holds at another exact sort relates the two
## sorts' heaps byte-wise at that address (`crossSortLink`, read; a store
## is spliced into every other sort's heap, `crossSortPropagate`), with the
## target's layout (`sizeof`, field offsets, endianness) checked natively
## below. A pair the model cannot relate exactly (a bool, an enum, a ref, a
## string, an object with padding or a run-type header) keeps INT-88's lossy,
## untrusted verdict.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type
  Pair = object
    lo, hi: int32
  Rec = object
    a, b: uint16
    c: float32

# ---- int <-> float at one address --------------------------------------------

proc crossSortHeap(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 5 and b[] > 1.0:
    symexTarget("hit")

proc crossSortAlias(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    symexTarget("hit")

proc crossSortZero(a: ptr int; b: ptr float) =
  # the bytes of the int 0 are the float +0.0: reachable
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 0 and b[] == 0.0:
    symexTarget("hit")

proc crossSortFloatFirst(a: ptr int; b: ptr float) =
  # the float view constrains the int view: 1.0 is 0x3FF0_0000_0000_0000
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     b[] == 1.0 and a[] != 0x3FF0_0000_0000_0000:
    symexTarget("hit")

# ---- an int32 pair <-> int64 ---------------------------------------------------

proc pairLow(p: ptr Pair; q: ptr int64) =
  # `lo` is the low half on a little-endian target: no other int64 holds it
  if p != nil and q != nil and cast[pointer](p) == cast[pointer](q) and
     p.lo == 1 and p.hi == 0 and q[] != 1:
    symexTarget("hit")

proc pairBoth(p: ptr Pair; q: ptr int64) =
  if p != nil and q != nil and cast[pointer](p) == cast[pointer](q) and
     p.lo == 1 and p.hi == 1 and q[] == 0x1_0000_0001'i64:
    symexTarget("hit")

# ---- an object of mixed scalars <-> int64 ---------------------------------------

proc recLow(r: ptr Rec; q: ptr int64) =
  # `c == 1.0` names one bit pattern (`0.0` would admit -0.0's sign bit too)
  if r != nil and q != nil and cast[pointer](r) == cast[pointer](q) and
     r.a == 1 and r.b == 0 and r.c == 1.0 and
     q[] != ((0x3F80_0000'i64 shl 32) or 1):
    symexTarget("hit")

proc recFloat(r: ptr Rec; q: ptr int64) =
  # the float32 1.0 (0x3F80_0000) sits in the high half
  if r != nil and q != nil and cast[pointer](r) == cast[pointer](q) and
     r.a == 0 and r.b == 0 and r.c == 1.0 and q[] == (0x3F80_0000'i64 shl 32):
    symexTarget("hit")

# ---- signedness ---------------------------------------------------------------

proc signedUnsat(a: ptr int32; b: ptr uint32) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == -1 and b[] != high(uint32):
    symexTarget("hit")

proc signedSat(a: ptr int32; b: ptr uint32) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == -1 and b[] == high(uint32):
    symexTarget("hit")

# ---- a mismatched-size pair ---------------------------------------------------

proc narrowUnsat(a: ptr int32; b: ptr int64) =
  # the int32 is the low four bytes of the int64
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 7 and (b[] and 0xFFFF_FFFF'i64) != 7:
    symexTarget("hit")

proc narrowSat(a: ptr int32; b: ptr int64) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 7 and b[] == 7:
    symexTarget("hit")

proc narrowHighFree(a: ptr int32; b: ptr int64) =
  # the int64's high four bytes are no part of the int32: free
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 7 and b[] != 7:
    symexTarget("hit")

# ---- a write at one sort ----------------------------------------------------------

proc writeUnsat(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    a[] = 5
    if b[] > 1.0:
      symexTarget("hit")

proc writeSat(a: ptr int; b: ptr float) =
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    a[] = 0
    if b[] == 0.0:
      symexTarget("hit")

proc writeAfterRead(a: ptr int; b: ptr float) =
  # the entry float is read before the int write: both are the program's
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b):
    let f0 = b[]
    a[] = 5
    if f0 == 2.0 and a[] == 5:
      symexTarget("hit")

suite "INT-90: two sorts' heaps at one address":
  test "natively: the target's layout is the model's":
    check sizeof(int) == 8
    check sizeof(float) == 8
    check cpuEndian == littleEndian
    check sizeof(Pair) == 8
    check offsetOf(Pair, lo) == 0
    check offsetOf(Pair, hi) == 4
    check sizeof(Rec) == 8
    check offsetOf(Rec, a) == 0
    check offsetOf(Rec, b) == 2
    check offsetOf(Rec, c) == 4

  test "natively: the int 5 read as a float is no float above 1.0":
    var x = 5
    let a = addr x
    let b = cast[ptr float](addr x)
    check cast[pointer](a) == cast[pointer](b)
    check a[] == 5
    check not (b[] > 1.0)
    var one = 1.0
    check cast[ptr int](addr one)[] == 0x3FF0_0000_0000_0000

  test "natively: an int32 pair and an object are the int64's bytes":
    var q: int64 = 1
    let p = cast[ptr Pair](addr q)
    check p.lo == 1 and p.hi == 0
    let r = cast[ptr Rec](addr q)
    check r.a == 1 and r.b == 0 and r.c == 0.0
    q = (0x3F80_0000'i64 shl 32) or 1
    check r.a == 1 and r.b == 0 and r.c == 1.0'f32
    q = 0x1_0000_0001'i64
    check p.lo == 1 and p.hi == 1
    q = 0x3F80_0000'i64 shl 32
    check r.c == 1.0'f32
    var m: int32 = -1
    check cast[ptr uint32](addr m)[] == high(uint32)
    var w: int64 = 0x1_0000_0007'i64
    check cast[ptr int32](addr w)[] == 7

  test "the alias alone is reachable (the control)":
    check pinFind(crossSortAlias, tLabel("hit")).status == sxSat

  test "a value at one sort constrains the other sort's read":
    let r = pinFind(crossSortHeap, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "the bytes both views admit are reachable":
    let r = pinFind(crossSortZero, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted

  test "the float view constrains the int view":
    let r = pinFind(crossSortFloatFirst, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat

  test "an int32 pair is the int64's two halves":
    let r = pinFind(pairLow, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let s = pinFind(pairBoth, tLabel("hit"))
    checkpoint show(s.errors)
    check s.status == sxSat
    check s.trusted

  test "an object of mixed scalars is the int64's bytes":
    let r = pinFind(recLow, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let s = pinFind(recFloat, tLabel("hit"))
    checkpoint show(s.errors)
    check s.status == sxSat
    check s.trusted

  test "signedness: one bit pattern, two values":
    let r = pinFind(signedUnsat, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let s = pinFind(signedSat, tLabel("hit"))
    checkpoint show(s.errors)
    check s.status == sxSat
    check s.trusted

  test "a narrower view is the low bytes of the wider":
    let r = pinFind(narrowUnsat, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let s = pinFind(narrowSat, tLabel("hit"))
    checkpoint show(s.errors)
    check s.status == sxSat
    # the wider view's other bytes are free (the model admits it; the witness
    # cell is built from one view's bytes, so the sat is not pinned)
    let f = symexFind(narrowHighFree, tLabel("hit"))
    checkpoint show(f.errors)
    check f.status != sxUnsat

  test "a write at one sort is read at the other":
    let r = pinFind(writeUnsat, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
    let s = pinFind(writeSat, tLabel("hit"))
    checkpoint show(s.errors)
    check s.status == sxSat
    check s.trusted

  test "a read before the write keeps the entry bytes":
    let r = pinFind(writeAfterRead, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat
    check r.trusted

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 451
