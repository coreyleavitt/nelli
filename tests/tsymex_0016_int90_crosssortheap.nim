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
##
## INT-90d (456): the padded object's store-then-read (`padWrite`) and its
## free padding (`padGap`) took 143-198 s to an `sxUnknown` and over 345 s
## to no answer: the splice was stored at the mapped address
## `@fromAddr_U(@toAddr_T(p))` while the program read `q`, so the read was
## an array alias Z3 had to search for under an `int2bv` of a `bv2int`.
## A view's fact and splice now use the program's own alias where the path
## holds it (`crossSortAddr`), and a splice into an Int-sorted cell records
## its bit-vector (`bitsAsLeaf`): both answer in well under a second.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type
  Pair = object
    lo, hi: int32
  Rec = object
    a, b: uint16
    c: float32
  Pad = object        # natural layout: `a` at 0, three padding bytes, `b` at 4
    a: int8
    b: int32
  Mixed = object      # 0, 8, 16; size 24 (seven bytes after `c`)
    a: int16
    b: int64
    c: int8
  Outer = object      # a nested object: `inner` at 4
    x: int8
    inner: Pair
  Packed {.packed.} = object   # no padding: `b` at 1, size 5
    a: int8
    b: int32
  Two = object        # 0, 8: two int64s
    x, y: int64

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

# ---- a padded object (its natural C layout, padding bytes free) ----------------

proc padLow(p: ptr Pad; q: ptr int64) =
  # `a` is byte 0 and `b` bytes 4..7 of the int64
  if p != nil and q != nil and cast[pointer](p) == cast[pointer](q) and
     p.a == 1 and p.b == 2 and (q[] and 0xFF) != 1:
    symexTarget("hit")

proc padHigh(p: ptr Pad; q: ptr int64) =
  if p != nil and q != nil and cast[pointer](p) == cast[pointer](q) and
     p.a == 1 and p.b == 2 and (q[] shr 32) != 2:
    symexTarget("hit")

proc padGap(a: ptr int64; p: ptr Pad) =
  # the padding bytes 1..3 are no part of `Pad`: any value
  if a != nil and p != nil and cast[pointer](a) == cast[pointer](p) and
     p.a == 1 and p.b == 2 and a[] == ((2'i64 shl 32) or 0x7701):
    symexTarget("hit")

proc padWrite(p: ptr Pad; q: ptr int64) =
  if p != nil and q != nil and cast[pointer](p) == cast[pointer](q):
    p.b = 3
    if (q[] shr 32) != 3:
      symexTarget("hit")

proc mixedMid(a: ptr array[3, int64]; m: ptr Mixed) =
  # `b` is the second eight bytes; an array is no view, so lossy
  if a != nil and m != nil and cast[pointer](a) == cast[pointer](m) and
     m.b == 9 and a[1] != 9:
    symexTarget("hit")

proc padBytes(p: ptr Pad; q: ptr array[8, uint8]) =
  # a byte array is no view the model spells: the pair keeps the lossy verdict
  if p != nil and q != nil and cast[pointer](p) == cast[pointer](q) and
     p.a == 1 and q[0] != 1:
    symexTarget("hit")

proc packedLow(p: ptr Packed; q: ptr int64) =
  if p != nil and q != nil and cast[pointer](p) == cast[pointer](q) and
     p.a == 1 and p.b == 2 and (q[] and 0xFF_FFFF_FFFF'i64) != 0x2_01:
    symexTarget("hit")

# ---- a wider view than its owner -------------------------------------------------

proc wideTail(a: ptr int32; b: ptr int64) =
  # the int32 owns the cell; the int64's high bytes are past it
  if a != nil and b != nil and cast[pointer](a) == cast[pointer](b) and
     a[] == 7 and b[] == 0x5_0000_0007'i64:
    symexTarget("hit")

proc widePad(a: ptr int32; p: ptr Pad) =
  # `p.b` is past the int32 owner
  if a != nil and p != nil and cast[pointer](a) == cast[pointer](p) and
     a[] == 1 and p.b == 9:
    symexTarget("hit")

proc widePadGap(a: ptr Pad; q: ptr int64) =
  # the int64 constrains the owner's padding, which the owner does not hold
  if a != nil and q != nil and cast[pointer](a) == cast[pointer](q) and
     a.a == 1 and a.b == 2 and q[] == ((2'i64 shl 32) or 0x7701):
    symexTarget("hit")

# ---- a write before the casts ------------------------------------------------------

proc lateCast(a: ptr int; b: ptr float; c: bool) =
  # the write precedes the sorts' casts, so it is spliced into no other
  # sort; the path that skips it reads the float's entry bytes, 2.0's
  if a != nil and b != nil:
    if c: a[] = 5
    if cast[pointer](a) == cast[pointer](b) and b[] == 2.0:
      symexTarget("hit")

# ---- a store through a pointer into a view object's field --------------------

proc famStore(a: ptr Two; b: ptr float; c: ptr int64) =
  # `c` may address `a.x` (a field the path read): its store reaches the
  # object's field heap, not the float's, so the float read before it is
  # still 2.0 while `a.x` is 5 (`c = addr a.x`). It was spliced into no
  # other sort and did not desync: a false `sxUnsat`.
  if a != nil and b != nil and c != nil and
     cast[pointer](a) == cast[pointer](b):
    let f0 = b[]
    if a.x != 7:
      c[] = 5
      if f0 == 2.0 and a.x == 5:
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
    check sizeof(Pad) == 8
    check offsetOf(Pad, a) == 0
    check offsetOf(Pad, b) == 4
    check sizeof(Mixed) == 24
    check offsetOf(Mixed, b) == 8
    check offsetOf(Mixed, c) == 16
    check sizeof(Outer) == 12
    check offsetOf(Outer, inner) == 4
    check sizeof(Packed) == 5
    check offsetOf(Packed, b) == 1

  test "natively: a padded object's padding is bytes no field holds":
    var q: int64 = (2'i64 shl 32) or 0x7701
    let p = cast[ptr Pad](addr q)
    check p.a == 1 and p.b == 2
    p.b = 3
    check (q shr 32) == 3
    var arr: array[3, int64] = [0'i64, 9, 0]
    check cast[ptr Mixed](addr arr).b == 9
    var w: int64 = 0x5_0000_0007'i64
    check cast[ptr int32](addr w)[] == 7

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
    check s.trusted
    # the wider view's other bytes are free
    let f = pinFind(narrowHighFree, tLabel("hit"))
    checkpoint show(f.errors)
    check f.status == sxSat
    check f.trusted

  test "a padded object is its natural layout; its padding is free":
    template unsat(f: untyped) =
      let t = pinFind(f, tLabel("hit"))
      checkpoint astToStr(f) & ": " & show(t.errors)
      check t.status == sxUnsat
    unsat(padLow)
    unsat(padHigh)
    unsat(padWrite)
    let s = pinFind(padGap, tLabel("hit"))
    checkpoint show(s.errors)
    check s.status == sxSat
    check s.trusted

  test "a byte array is no view: the pair keeps the lossy verdict":
    let r = pinFind(padBytes, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnsat or not r.trusted
    # an int64 array beside a padded object: likewise (its `b` is a[1])
    let m = pinFind(mixedMid, tLabel("hit"))
    checkpoint show(m.errors)
    check m.status == sxUnsat or not m.trusted

  test "a {.packed.} object declines at the pragma axis":
    pinDecline(packedLow, cellKey(axPragma, "type/packed"), feUnsupportedOp,
               needle = "pragma:type/packed")

  test "a wider view than its owner: the tail is the view's":
    template trustedSat(f: untyped) =
      let s = pinFind(f, tLabel("hit"))
      checkpoint astToStr(f) & ": " & show(s.errors)
      check s.status == sxSat
      check s.trusted
    trustedSat(wideTail)
    trustedSat(widePad)
    # the owner's padding is bytes the witness cannot fill from the owner
    let g = pinFind(widePadGap, tLabel("hit"))
    checkpoint show(g.errors)
    check g.status == sxSat

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

  test "a write before the casts forces no entry bytes":
    var x = 0
    let a = addr x
    let b = cast[ptr float](addr x)
    b[] = 2.0
    check cast[pointer](a) == cast[pointer](b) and b[] == 2.0
    let r = pinFind(lateCast, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "natively: a store through a pointer into a view's field":
    check sizeof(Two) == 16 and offsetOf(Two, y) == 8
    var buf: Two
    let a = addr buf
    let b = cast[ptr float](addr buf)
    let c = addr buf.x
    b[] = 2.0
    let f0 = b[]
    check a.x != 7
    c[] = 5
    check f0 == 2.0 and a.x == 5
    check cast[pointer](a) == cast[pointer](b)

  test "a store through a pointer into a view's field desyncs the path":
    let r = pinFind(famStore, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxSat

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 456
