## RFC-0016 INT-85 (soundness): a zero-initialised element or field of an
## enum or range type whose declared values exclude 0 was a false sxUnsat
## for "it holds ordinal 0". Every read site bounded the value to
## `[low, high]`, but natively a slot the program creates (`newSeq`,
## `setLen` growth, `new`, an object constructor leaving the field out,
## `default(T)`, an untouched `result`, a local array) starts zeroed, and
## for such a type that is ordinal 0: no declared value. Left by INT-84,
## and older than it.
##
## Native evidence (pinned toolchain, probed): every shape below holds 0 for
## `Wide = enum wA = 2, wB = 5` and for `range[3..9]`, `default(R)`
## included. An object constructor that leaves a `range[3..9]` field out and
## a `result` of such a range left untouched do not compile (Nim requires
## their explicit initialization), so those shapes are pinned for the enum
## only; a range field reaches 0 through `default(Obj)` and `new`.
##
## The bar: each target a zeroed slot reaches is sxSat, its witness replayed
## natively; a twin over a caller's value (a parameter, its element or
## field) stays sxUnsat, since no caller can pass a value outside the
## declared domain.
import std/[unittest, strutils]
import nelli/symex
import ./s8cu_helpers

type
  Wide = enum
    wA = 2
    wB = 5
  R = range[3..9]
  WRef = ref object
    w: Wide
    r: R
  ObjW = object
    w: Wide
    n: int
  ObjR = object
    r: R
    n: int
  F = range[1.0..2.0]
  F32 = range[1.0'f32..2.0'f32]
  FRef = ref object
    f: F
    g: F32
  ObjF = object
    f: F
    n: int

# Enum without ordinal 0.
proc seqElemW(k: int) =
  let xs = newSeq[Wide](1)
  if k == 1 and ord(xs[0]) == 0: symexTarget("hit")

proc setLenW(k: int) =
  var xs = @[wB]
  xs.setLen(2)
  if k == 1 and ord(xs[1]) == 0: symexTarget("hit")

proc newFieldW(k: int) =
  let r = new(WRef)
  if k == 1 and ord(r.w) == 0: symexTarget("hit")

proc ctorFieldW(k: int) =
  let o = ObjW(n: k)
  if k == 1 and ord(o.w) == 0: symexTarget("hit")

proc defaultW(k: int) =
  let w = default(Wide)
  if k == 1 and ord(w) == 0: symexTarget("hit")

proc defaultObjW(k: int) =
  let o = default(ObjW)
  if k == 1 and ord(o.w) == 0: symexTarget("hit")

proc untouchedW(): Wide = discard

proc resultW(k: int) =
  if k == 1 and ord(untouchedW()) == 0: symexTarget("hit")

proc arrayW(k: int) =
  var a: array[2, Wide]
  if k == 1 and ord(a[1]) == 0: symexTarget("hit")

# Range without 0.
proc seqElemR(k: int) =
  let xs = newSeq[R](1)
  if k == 1 and int(xs[0]) == 0: symexTarget("hit")

proc setLenR(k: int) =
  var xs: seq[R] = @[R(4)]
  xs.setLen(2)
  if k == 1 and int(xs[1]) == 0: symexTarget("hit")

proc newFieldR(k: int) =
  let r = new(WRef)
  if k == 1 and int(r.r) == 0: symexTarget("hit")

proc defaultR(k: int) =
  let v = default(R)
  if k == 1 and int(v) == 0: symexTarget("hit")

proc defaultObjR(k: int) =
  let o = default(ObjR)
  if k == 1 and int(o.r) == 0: symexTarget("hit")

proc arrayR(k: int) =
  var a: array[2, R]
  if k == 1 and int(a[0]) == 0: symexTarget("hit")

# Float range without 0.0.
proc seqElemF(k: int) =
  let xs = newSeq[F](1)
  if k == 1 and float(xs[0]) == 0.0: symexTarget("hit")

proc seqElemF32(k: int) =
  let xs = newSeq[F32](1)
  if k == 1 and float32(xs[0]) == 0.0'f32: symexTarget("hit")

proc setLenF(k: int) =
  var xs: seq[F] = @[F(1.5)]
  xs.setLen(2)
  if k == 1 and float(xs[1]) == 0.0: symexTarget("hit")

proc newFieldF(k: int) =
  let r = new(FRef)
  if k == 1 and float(r.f) == 0.0: symexTarget("hit")

proc newFieldF32(k: int) =
  let r = new(FRef)
  if k == 1 and float32(r.g) == 0.0'f32: symexTarget("hit")

proc defaultF(k: int) =
  let v = default(F)
  if k == 1 and float(v) == 0.0: symexTarget("hit")

proc defaultObjF(k: int) =
  let o = default(ObjF)
  if k == 1 and float(o.f) == 0.0: symexTarget("hit")

proc arrayF(k: int) =
  var a: array[2, F]
  if k == 1 and float(a[0]) == 0.0: symexTarget("hit")

proc localF(k: int) =
  var v: F
  if k == 1 and float(v) == 0.0: symexTarget("hit")

# Never-twins: a caller's value lies in the declared domain.
proc inW(w: Wide) =
  if ord(w) == 0: symexTarget("hit")

proc inSeqW(xs: seq[Wide]) =
  if xs.len > 0 and ord(xs[0]) == 0: symexTarget("hit")

proc inRefW(r: WRef) =
  if r != nil and ord(r.w) == 0: symexTarget("hit")

proc inObjW(o: ObjW) =
  if ord(o.w) == 0: symexTarget("hit")

proc inR(v: R) =
  if int(v) == 0: symexTarget("hit")

proc inSeqR(xs: seq[R]) =
  if xs.len > 0 and int(xs[0]) == 0: symexTarget("hit")

proc inRefR(r: WRef) =
  if r != nil and int(r.r) == 0: symexTarget("hit")

proc inObjR(o: ObjR) =
  if int(o.r) == 0: symexTarget("hit")

proc inF(v: F) =
  if float(v) == 0.0: symexTarget("hit")

proc inSeqF(xs: seq[F]) =
  if xs.len > 0 and float(xs[0]) == 0.0: symexTarget("hit")

proc inRefF(r: FRef) =
  if r != nil and float(r.f) == 0.0: symexTarget("hit")

proc inRefF32(r: FRef) =
  if r != nil and float32(r.g) == 0.0'f32: symexTarget("hit")

proc inObjF(o: ObjF) =
  if float(o.f) == 0.0: symexTarget("hit")

# A caller's seq grown by the program: the old slot is the caller's, the new
# one is zeroed.
proc grownInputW(xs: seq[Wide]) =
  var ys = xs
  ys.setLen(xs.len + 1)
  if ord(ys[xs.len]) == 0: symexTarget("hit")

proc grownInputOldW(xs: seq[Wide]) =
  var ys = xs
  ys.setLen(xs.len + 1)
  if xs.len > 0 and ord(ys[0]) == 0: symexTarget("hit")

suite "INT-85: a zeroed slot of an enum without ordinal 0 holds 0":
  test "a newSeq element":
    check pinFind(seqElemW, tLabel("hit")).status == sxSat
  test "a setLen growth slot":
    check pinFind(setLenW, tLabel("hit")).status == sxSat
  test "a new ref cell's field":
    check pinFind(newFieldW, tLabel("hit")).status == sxSat
  test "an object constructor's omitted field":
    check pinFind(ctorFieldW, tLabel("hit")).status == sxSat
  test "default(T)":
    check pinFind(defaultW, tLabel("hit")).status == sxSat
  test "default of an object":
    check pinFind(defaultObjW, tLabel("hit")).status == sxSat
  test "an untouched result":
    check pinFind(resultW, tLabel("hit")).status == sxSat
  test "a local array":
    check pinFind(arrayW, tLabel("hit")).status == sxSat

suite "INT-85: a zeroed slot of a range without 0 holds 0":
  test "a newSeq element":
    check pinFind(seqElemR, tLabel("hit")).status == sxSat
  test "a setLen growth slot":
    check pinFind(setLenR, tLabel("hit")).status == sxSat
  test "a new ref cell's field":
    check pinFind(newFieldR, tLabel("hit")).status == sxSat
  test "default(T)":
    check pinFind(defaultR, tLabel("hit")).status == sxSat
  test "default of an object":
    check pinFind(defaultObjR, tLabel("hit")).status == sxSat
  test "a local array":
    check pinFind(arrayR, tLabel("hit")).status == sxSat

suite "INT-85: a zeroed slot of a float range without 0.0 holds 0.0":
  test "a newSeq element":
    check pinFind(seqElemF, tLabel("hit")).status == sxSat
  test "a float32 newSeq element":
    check pinFind(seqElemF32, tLabel("hit")).status == sxSat
  test "a setLen growth slot":
    check pinFind(setLenF, tLabel("hit")).status == sxSat
  test "a new ref cell's field":
    check pinFind(newFieldF, tLabel("hit")).status == sxSat
  test "a new ref cell's float32 field":
    check pinFind(newFieldF32, tLabel("hit")).status == sxSat
  test "default(T)":
    check pinFind(defaultF, tLabel("hit")).status == sxSat
  test "default of an object":
    check pinFind(defaultObjF, tLabel("hit")).status == sxSat
  test "a local array":
    check pinFind(arrayF, tLabel("hit")).status == sxSat
  test "a local left uninitialised":
    check pinFind(localF, tLabel("hit")).status == sxSat

suite "INT-85: a caller's value is never 0":
  test "an enum parameter":
    check pinFind(inW, tLabel("hit")).status == sxUnsat
  test "an enum seq element":
    check pinFind(inSeqW, tLabel("hit")).status == sxUnsat
  test "an enum ref cell's field":
    check pinFind(inRefW, tLabel("hit")).status == sxUnsat
  test "an enum object field":
    check pinFind(inObjW, tLabel("hit")).status == sxUnsat
  test "a range parameter":
    check pinFind(inR, tLabel("hit")).status == sxUnsat
  test "a range seq element":
    check pinFind(inSeqR, tLabel("hit")).status == sxUnsat
  test "a range ref cell's field":
    check pinFind(inRefR, tLabel("hit")).status == sxUnsat
  test "a range object field":
    check pinFind(inObjR, tLabel("hit")).status == sxUnsat
  test "a float range parameter":
    check pinFind(inF, tLabel("hit")).status == sxUnsat
  test "a float range seq element":
    check pinFind(inSeqF, tLabel("hit")).status == sxUnsat
  test "a float range ref cell's field":
    check pinFind(inRefF, tLabel("hit")).status == sxUnsat
  test "a float32 range ref cell's field":
    check pinFind(inRefF32, tLabel("hit")).status == sxUnsat
  test "a float range object field":
    check pinFind(inObjF, tLabel("hit")).status == sxUnsat

proc grownInputF(xs: seq[F]) =
  var ys = xs
  ys.setLen(xs.len + 1)
  if float(ys[xs.len]) == 0.0: symexTarget("hit")

proc grownInputOldF(xs: seq[F]) =
  var ys = xs
  ys.setLen(xs.len + 1)
  if xs.len > 0 and float(ys[0]) == 0.0: symexTarget("hit")

suite "INT-85: a caller's seq grown by the program":
  test "the grown slot holds 0":
    check pinFind(grownInputW, tLabel("hit")).status == sxSat
  test "the caller's slot does not":
    check pinFind(grownInputOldW, tLabel("hit")).status == sxUnsat
  test "a float range's grown slot holds 0.0":
    check pinFind(grownInputF, tLabel("hit")).status == sxSat
  test "a float range's caller slot does not":
    check pinFind(grownInputOldF, tLabel("hit")).status == sxUnsat

suite "INT-85: version floor":
  test "the walker version is at least INT-85's":
    check parseInt(symexWalkerVersion) >= 445
