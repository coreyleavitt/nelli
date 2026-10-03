## RFC-0005 (soundness channels) slice S8bs -- an address cell aliased
## through a global ptr across a frame boundary.
##
## S8bg found it: `gpb = addr b; setXG(pb[].x, k)` where `setXG` writes its
## `var` formal and then `gpb[].x = 5`. Nim passes `pb[].x` by address, so
## the callee's two writes land on one location in its order (`b.x == 5`).
## The walker copied the actual in and out, and the write-back of the stale
## `v = k` landed over the write through the global: "ac" was `sxUnsat` and
## "ac_dead" `sxSat`, with no decline.
##
## Every expectation below is Nim's (the "nim" test runs each SUT natively
## under a capture frame and checks which labels it hits).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint

template declines(fn: typed, lbl, why: string): untyped =
  ## A shape the walk does not model: `sxUnknown`, with the decline named.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 1, 2, 5, 7]

# ---- the S8bg exhibit --------------------------------------------------------

type Box = object
  x: int

var gpb: ptr Box

proc setXG(v: var int, k: int) =
  v = k
  gpb[].x = 5

proc sutAddrCellByRef(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  gpb = pb
  setXG(pb[].x, k)
  if b.x == 5 and gpb[].x == 5 and k == 1: symexTarget("ac")
  if b.x == k and k != 5: symexTarget("ac_dead")


proc setXG2(v: var int, k: int) =
  ## The write through the alias first: `v = k` is the last write.
  gpb[].x = 5
  v = k

proc sutAliasBefore(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  gpb = pb
  setXG2(pb[].x, k)
  if b.x == k and k == 3: symexTarget("bf")
  if b.x != k: symexTarget("bf_dead")

proc sutByName(k: int) =
  ## The actual names the variable itself (`b.x`), not the pointer.
  var b: Box = Box(x: 0)
  gpb = addr b
  setXG(b.x, k)
  if b.x == 5 and k == 2: symexTarget("bn")
  if b.x != 5: symexTarget("bn_dead")

proc sutByNameBefore(k: int) =
  var b: Box = Box(x: 0)
  gpb = addr b
  setXG2(b.x, k)
  if b.x == k and k == 2: symexTarget("bnb")
  if b.x != k: symexTarget("bnb_dead")

var gpi: ptr int

proc setIG(v: var int, k: int) =
  v = k
  gpi[] = 5

proc sutScalar(k: int) =
  ## A scalar variable's own address cell (S8ax), by name.
  var x = 0
  gpi = addr x
  setIG(x, k)
  if x == 5 and k == 4: symexTarget("sc")
  if x != 5: symexTarget("sc_dead")

proc rdXG(v: var int, k: int): int =
  ## Only reads through the alias: it sees the write to `v`.
  v = k
  result = gpb[].x

proc sutReadOnly(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  gpb = pb
  let r = rdXG(pb[].x, k)
  if r == k and k == 6: symexTarget("ro")
  if r != k: symexTarget("ro_dead")

proc sutReadOnlyByName(k: int) =
  var b: Box = Box(x: 0)
  gpb = addr b
  let r = rdXG(b.x, k)
  if r == k and k == 6: symexTarget("rn")
  if r != k: symexTarget("rn_dead")

proc helperG() =
  gpb[].x = 5

proc setXG2Deep(v: var int, k: int) =
  v = k
  helperG()

proc sutTwoDeep(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  gpb = pb
  setXG2Deep(pb[].x, k)
  if b.x == 5 and k == 7: symexTarget("td")
  if b.x != 5: symexTarget("td_dead")

proc setXP(v: var int, p: ptr Box, k: int) =
  v = k
  p[].x = 5

proc sutPtrParam(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  setXP(pb[].x, pb, k)
  if b.x == 5 and k == 8: symexTarget("pp")
  if b.x != 5: symexTarget("pp_dead")

proc sutPtrParamByName(k: int) =
  var b: Box = Box(x: 0)
  setXP(b.x, addr b, k)
  if b.x == 5 and k == 8: symexTarget("ppn")
  if b.x != 5: symexTarget("ppn_dead")

type Holder = ref object
  p: ptr Box

var gh: Holder

proc setXH(v: var int, k: int) =
  v = k
  gh.p[].x = 5

proc sutHeapField(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  gh = Holder(p: pb)
  setXH(pb[].x, k)
  if b.x == 5 and k == 9: symexTarget("hf")
  if b.x != 5: symexTarget("hf_dead")

proc sutCapture(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  proc setXC(v: var int) =
    v = k
    pb[].x = 5
  setXC(pb[].x)
  if b.x == 5 and k == 10: symexTarget("cp")
  if b.x != 5: symexTarget("cp_dead")

proc sutProcValue(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  gpb = pb
  let f = setXG
  f(pb[].x, k)
  if b.x == 5 and k == 11: symexTarget("pv")
  if b.x != 5: symexTarget("pv_dead")

type RBox = ref object
  x: int

var grb: RBox

proc setXR(v: var int, k: int) =
  v = k
  grb.x = 5

proc sutGlobalRef(k: int) =
  let b = RBox(x: 0)
  grb = b
  setXR(b.x, k)
  if b.x == 5 and k == 12: symexTarget("gr")
  if b.x != 5: symexTarget("gr_dead")

proc sutElem(k: int) =
  ## An element cell (S8be) aliased through a global.
  var s = @[0, 0]
  gpi = addr s[1]
  setIG(s[1], k)
  if s[1] == 5 and k == 13: symexTarget("el")
  if s[1] != 5: symexTarget("el_dead")

type VBox = object
  case on: bool
  of true: a: int
  of false: c: int

var gpv: ptr VBox

proc setAV(v: var int, k: int) =
  v = k
  gpv[].a = 5

proc sutVariant(k: int) =
  var o = VBox(on: true, a: 0)
  let po = addr o
  gpv = po
  setAV(po[].a, k)
  if o.a == 5 and k == 14: symexTarget("va")
  if o.a != 5: symexTarget("va_dead")

proc sutVariantByName(k: int) =
  var o = VBox(on: true, a: 0)
  gpv = addr o
  setAV(o.a, k)
  if o.a == 5 and k == 14: symexTarget("van")
  if o.a != 5: symexTarget("van_dead")

proc sutTwoDeepByName(k: int) =
  var b: Box = Box(x: 0)
  gpb = addr b
  setXG2Deep(b.x, k)
  if b.x == 5 and k == 7: symexTarget("tdn")
  if b.x != 5: symexTarget("tdn_dead")

proc sutHeapFieldByName(k: int) =
  var b: Box = Box(x: 0)
  gh = Holder(p: addr b)
  setXH(b.x, k)
  if b.x == 5 and k == 9: symexTarget("hfn")
  if b.x != 5: symexTarget("hfn_dead")

proc sutCaptureByName(k: int) =
  var b: Box = Box(x: 0)
  let pb = addr b
  proc setXC(v: var int) =
    v = k
    pb[].x = 5
  setXC(b.x)
  if b.x == 5 and k == 10: symexTarget("cpn")
  if b.x != 5: symexTarget("cpn_dead")

proc sutProcValueByName(k: int) =
  var b: Box = Box(x: 0)
  gpb = addr b
  let f = setXG
  f(b.x, k)
  if b.x == 5 and k == 11: symexTarget("pvn")
  if b.x != 5: symexTarget("pvn_dead")

proc setPG(p: ptr int, k: int) =
  p[] = k
  gpb[].x = 5

proc sutAddrActualByName(k: int) =
  var b: Box = Box(x: 0)
  gpb = addr b
  setPG(addr b.x, k)
  if b.x == 5 and k == 15: symexTarget("aa")
  if b.x != 5: symexTarget("aa_dead")

proc setXGNest(v: var int, k: int) =
  ## Passes its formal on: the location is still `b.x`.
  setXG(v, k)

proc sutNested(k: int) =
  var b: Box = Box(x: 0)
  gpb = addr b
  setXGNest(b.x, k)
  if b.x == 5 and k == 16: symexTarget("ne")
  if b.x != 5: symexTarget("ne_dead")

# ---- a heap lvalue goes by reference whatever else reaches it ---------------

proc setPlain(v: var int, k: int) =
  v = k

proc sutDerefPlain(k: int) =
  ## No alias at all: `pb[].x` is still passed by address.
  var b: Box = Box(x: 0)
  let pb = addr b
  setPlain(pb[].x, k)
  if b.x == k and k == 17: symexTarget("dp")
  if b.x != k: symexTarget("dp_dead")

type Outer = object
  inner: Box
  y: int

var gpo: ptr Outer

proc setIO(v: var int, k: int) =
  v = k
  gpo[].inner.x = 5

proc sutDerefInner(k: int) =
  var o: Outer = Outer(inner: Box(x: 0), y: 0)
  gpo = addr o
  let po = addr o
  setIO(po[].inner.x, k)
  if o.inner.x == 5 and k == 18: symexTarget("di")
  if o.inner.x != 5: symexTarget("di_dead")

proc sutRefDeref(k: int) =
  let r = RBox(x: 0)
  grb = r
  setXR(r[].x, k)
  if r.x == 5 and k == 19: symexTarget("rd")
  if r.x != 5: symexTarget("rd_dead")

proc sutPtrValueByName(k: int) =
  ## The pointer passed by value beside a path into its pointee.
  var b: Box = Box(x: 0)
  let pb = addr b
  setXP(b.x, pb, k)
  if b.x == 5 and k == 20: symexTarget("pq")
  if b.x != 5: symexTarget("pq_dead")

# ---- inheritance conversions on a by-reference actual ------------------------

type
  BaseR = ref object of RootObj
    x: int
  DerR = ref object of BaseR
    y: int

var gbr: BaseR
var gdr: DerR

proc setXB(v: var int, k: int) =
  v = k
  gbr.x = 5

proc sutUpcast(k: int) =
  let d = DerR(x: 0, y: 0)
  gbr = d
  setXB(BaseR(d).x, k)
  if d.x == 5 and k == 21: symexTarget("uc")
  if d.x != 5: symexTarget("uc_dead")

proc setYD(v: var int, k: int) =
  v = k
  gdr.y = 5

proc sutDowncast(k: int) =
  let d = DerR(x: 0, y: 0)
  gdr = d
  let b: BaseR = d
  setYD(DerR(b).y, k)
  if d.y == 5 and k == 22: symexTarget("dc")
  if d.y != 5: symexTarget("dc_dead")

proc sutDowncastBad(k: int) =
  ## Not a `DerR`: the conversion raises before the call.
  let b = BaseR(x: 0)
  gdr = DerR(x: 0, y: 0)
  var hit = false
  try:
    setYD(DerR(b).y, k)
  except ObjectConversionDefect:
    hit = true
  if hit and k == 23: symexTarget("dx")
  if not hit: symexTarget("dx_dead")

# ---- other parameters Nim passes by address ---------------------------------

proc setOA(a: var openArray[int], k: int) =
  a[0] = k
  gpi[] = 5

proc sutVarOpenArray(k: int) =
  var s = @[0, 0]
  gpi = addr s[0]
  setOA(s, k)
  if s[0] == 5 and k == 24: symexTarget("oa")
  if s[0] != 5: symexTarget("oa_dead")

proc rdOA(a: openArray[int], k: int): int =
  gpi[] = k
  a[0]

proc sutOpenArrayRead(k: int) =
  ## Nim passes an `openArray` by address: the read after the write
  ## through the alias sees it.
  var s = @[0, 0]
  gpi = addr s[0]
  let r = rdOA(s, k)
  if r == k and k == 25: symexTarget("or")
  if r != k: symexTarget("or_dead")

proc takeS(t: sink seq[int], k: int): int =
  gpi[] = k
  t[0]

proc sutSink(k: int) =
  var s = @[0, 0]
  gpi = addr s[0]
  let r = takeS(s, k)
  if r == k and k == 26: symexTarget("sk")
  if r != k: symexTarget("sk_dead")

iterator itv(a: var seq[int]; k: int): int =
  a[0] = k
  gpi[] = 5
  yield a[0]

proc sutIterVar(k: int) =
  var s = @[0, 0]
  gpi = addr s[0]
  var got = 0
  for x in itv(s, k): got = x
  if got == 5 and s[0] == 5 and k == 27: symexTarget("iv")
  if got != 5 or s[0] != 5: symexTarget("iv_dead")

proc sutMitems(k: int) =
  var s = @[0, 0]
  gpi = addr s[0]
  for x in mitems(s):
    x = k
    gpi[] = 5
  if s[0] == 5 and s[1] == k and k == 28: symexTarget("mi")
  if s[0] != 5 or s[1] != k: symexTarget("mi_dead")

suite "S8bs: an address cell reached through a global ptr":

  test "nim":
    let h = nativeHits(sutAddrCellByRef, ks)
    check "ac" in h
    check "ac_dead" notin h

  test "the S8bg exhibit":
    clean(sutAddrCellByRef, "ac", sxSat)
    clean(sutAddrCellByRef, "ac_dead", sxUnsat)

  test "nim: the family":
    let ks2 = [-1, 0, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    let h = nativeHits(sutAliasBefore, ks2) + nativeHits(sutByName, ks2) +
            nativeHits(sutByNameBefore, ks2) + nativeHits(sutScalar, ks2) +
            nativeHits(sutReadOnly, ks2) + nativeHits(sutReadOnlyByName, ks2) +
            nativeHits(sutTwoDeep, ks2) + nativeHits(sutPtrParam, ks2) +
            nativeHits(sutPtrParamByName, ks2) + nativeHits(sutHeapField, ks2) +
            nativeHits(sutCapture, ks2) + nativeHits(sutProcValue, ks2) +
            nativeHits(sutGlobalRef, ks2) + nativeHits(sutElem, ks2) +
            nativeHits(sutVariant, ks2) + nativeHits(sutVariantByName, ks2) +
            nativeHits(sutTwoDeepByName, ks2) +
            nativeHits(sutHeapFieldByName, ks2) +
            nativeHits(sutCaptureByName, ks2) +
            nativeHits(sutProcValueByName, ks2) +
            nativeHits(sutAddrActualByName, ks2) + nativeHits(sutNested, ks2)
    for l in ["bf", "bn", "bnb", "sc", "ro", "rn", "td", "pp", "ppn", "hf",
              "cp", "pv", "gr", "el", "va", "van", "tdn", "hfn", "cpn", "pvn",
              "aa", "ne"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "the write through the alias before `v = k`":
    clean(sutAliasBefore, "bf", sxSat)
    clean(sutAliasBefore, "bf_dead", sxUnsat)
  test "the actual by name":
    clean(sutByName, "bn", sxSat)
    clean(sutByName, "bn_dead", sxUnsat)
    clean(sutByNameBefore, "bnb", sxSat)
    clean(sutByNameBefore, "bnb_dead", sxUnsat)
  test "a scalar address cell":
    clean(sutScalar, "sc", sxSat)
    clean(sutScalar, "sc_dead", sxUnsat)
  test "a callee that only reads through the alias":
    clean(sutReadOnly, "ro", sxSat)
    clean(sutReadOnly, "ro_dead", sxUnsat)
    clean(sutReadOnlyByName, "rn", sxSat)
    clean(sutReadOnlyByName, "rn_dead", sxUnsat)
  test "two levels deep":
    clean(sutTwoDeep, "td", sxSat)
    clean(sutTwoDeep, "td_dead", sxUnsat)
  test "a separate ptr parameter":
    clean(sutPtrParam, "pp", sxSat)
    clean(sutPtrParam, "pp_dead", sxUnsat)
    clean(sutPtrParamByName, "ppn", sxSat)
    clean(sutPtrParamByName, "ppn_dead", sxUnsat)
  test "a heap object's field":
    clean(sutHeapField, "hf", sxSat)
    clean(sutHeapField, "hf_dead", sxUnsat)
  test "a closure capture":
    clean(sutCapture, "cp", sxSat)
    clean(sutCapture, "cp_dead", sxUnsat)
  test "a proc-value call":
    # RFC-0005 S8bh's decline: the body reaches a heap cell of the type.
    declines(sutProcValue, "pv", "can also be reached by the body")
    declines(sutProcValue, "pv_dead", "can also be reached by the body")
  test "a global ref":
    clean(sutGlobalRef, "gr", sxSat)
    clean(sutGlobalRef, "gr_dead", sxUnsat)
  test "an element address":
    clean(sutElem, "el", sxSat)
    clean(sutElem, "el_dead", sxUnsat)
  test "a variant-arm field":
    clean(sutVariant, "va", sxSat)
    clean(sutVariant, "va_dead", sxUnsat)
    clean(sutVariantByName, "van", sxSat)
    clean(sutVariantByName, "van_dead", sxUnsat)
  test "by name, through every route":
    clean(sutTwoDeepByName, "tdn", sxSat)
    clean(sutTwoDeepByName, "tdn_dead", sxUnsat)
    clean(sutHeapFieldByName, "hfn", sxSat)
    clean(sutHeapFieldByName, "hfn_dead", sxUnsat)
    clean(sutCaptureByName, "cpn", sxSat)
    clean(sutCaptureByName, "cpn_dead", sxUnsat)
    # A closure descent binds no formal to a cell (`bindVarLocs` is the
    # direct call's): declined, where it was a swapped verdict.
    declines(sutProcValueByName, "pvn", "whose address is taken")
    declines(sutProcValueByName, "pvn_dead", "whose address is taken")
    clean(sutNested, "ne", sxSat)
    clean(sutNested, "ne_dead", sxUnsat)
  test "an addr actual by name":
    # `addr b.x` of an address-taken `b` is a cell for the call: declined,
    # where it was a swapped verdict.
    declines(sutAddrActualByName, "aa", "is a cell for the call")
    declines(sutAddrActualByName, "aa_dead", "is a cell for the call")

  test "nim: by reference, and through conversions":
    let ks3 = [-1, 0, 5, 17, 18, 19, 20, 21, 22, 23]
    let h = nativeHits(sutDerefPlain, ks3) + nativeHits(sutDerefInner, ks3) +
            nativeHits(sutRefDeref, ks3) + nativeHits(sutPtrValueByName, ks3) +
            nativeHits(sutUpcast, ks3) + nativeHits(sutDowncast, ks3) +
            nativeHits(sutDowncastBad, ks3)
    for l in ["dp", "di", "rd", "pq", "uc", "dc", "dx"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h
  test "a heap lvalue goes by reference":
    clean(sutDerefPlain, "dp", sxSat)
    clean(sutDerefPlain, "dp_dead", sxUnsat)
    clean(sutDerefInner, "di", sxSat)
    clean(sutDerefInner, "di_dead", sxUnsat)
    clean(sutRefDeref, "rd", sxSat)
    clean(sutRefDeref, "rd_dead", sxUnsat)
    clean(sutPtrValueByName, "pq", sxSat)
    clean(sutPtrValueByName, "pq_dead", sxUnsat)
  test "an inheritance conversion on a by-reference actual":
    clean(sutUpcast, "uc", sxSat)
    clean(sutUpcast, "uc_dead", sxUnsat)
    clean(sutDowncast, "dc", sxSat)
    clean(sutDowncast, "dc_dead", sxUnsat)
    clean(sutDowncastBad, "dx", sxSat)
    clean(sutDowncastBad, "dx_dead", sxUnsat)
  test "nim: other by-address parameters":
    let ks4 = [-1, 0, 5, 24, 25, 26, 27, 28]
    let h = nativeHits(sutVarOpenArray, ks4) +
            nativeHits(sutOpenArrayRead, ks4) + nativeHits(sutSink, ks4) +
            nativeHits(sutIterVar, ks4) + nativeHits(sutMitems, ks4)
    for l in ["oa", "or", "sk", "iv", "mi"]:
      checkpoint l & " " & $(l in h) & " " & $((l & "_dead") in h)
      check l in h
      check (l & "_dead") notin h
  test "other by-address parameters":
    clean(sutVarOpenArray, "oa", sxSat)
    clean(sutVarOpenArray, "oa_dead", sxUnsat)
    clean(sutOpenArrayRead, "or", sxSat)
    clean(sutOpenArrayRead, "or_dead", sxUnsat)
    clean(sutSink, "sk", sxSat)
    clean(sutSink, "sk_dead", sxUnsat)
    clean(sutIterVar, "iv", sxSat)
    clean(sutIterVar, "iv_dead", sxUnsat)
    clean(sutMitems, "mi", sxSat)
    clean(sutMitems, "mi_dead", sxUnsat)
