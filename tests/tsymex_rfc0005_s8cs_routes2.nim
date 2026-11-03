## RFC-0005 S8cs -- the stores to a global that an opaque call's summary missed, and
## the verdicts that must stay exact. See `tsymex_rfc0005_s8cs_routes`.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/engine/markers
import s8cs_hooks_fixture

var nh: HashSet[string]
template nat(call: untyped) =
  symexCaptureBegin()
  call
  nh = nh + symexCaptureEnd()

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template notUnsat(fn: typed, lbl: string, kind: SymexErrorKind) =
  ## The opaque call's havoc reaches the global, so the hit is a candidate. A
  ## store the summary missed left the global as it was: `sxUnsat`, false.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    check r.errors.hasKind(kind)

template declined(fn: typed, lbl: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feGlobalRouteUnproved)

template exactSat(fn: typed, lbl: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feGlobalRouteUnproved)

template exactUnsat(fn: typed, lbl: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnsat
    check not r.errors.hasKind(feGlobalRouteUnproved)

# --- B24: a store behind a read position ------------------------------------------

type PH = object
  p: ptr int
var gI: int
var gPtr: ptr int
var gPtrs: seq[ptr int]
var gPH: PH

proc o1() {.symexOpaque.} =
  let p = gPtr
  p[] = 9
proc n1(k: int) =
  let a = gI
  o1()
  if gI != 9 and a == 9: symexTarget("n1_dead")
  if gI == 9 and a != 9: symexTarget("n1_live")
proc o2() {.symexOpaque.} =
  let o = gPH
  o.p[] = 9
proc n2(k: int) =
  let a = gI
  o2()
  if gI == 9 and a != 9: symexTarget("n2_live")
proc o3() {.symexOpaque.} =
  for p in gPtrs: p[] = 9
proc n3(k: int) =
  let a = gI
  o3()
  if gI == 9 and a != 9: symexTarget("n3_live")
proc o4() {.symexOpaque.} =
  let p = addr gI
  p[] = 9
proc n4(k: int) =
  let a = gI
  o4()
  if gI == 9 and a != 9: symexTarget("n4_live")
proc o5a(p: ptr int) = p[] = 9
proc o5() {.symexOpaque.} =
  o5a(gPtr)
proc n5(k: int) =
  let a = gI
  o5()
  if gI == 9 and a != 9: symexTarget("n5_live")
proc o13(x: int) {.symexOpaque.} =
  var c = gPtr
  c[] = x
proc n13(k: int) =
  let a = gI
  o13(9)
  if gI == 9 and a != 9: symexTarget("n13_live")

# --- stdlib stores through a pointer --------------------------------------------------

var gI1, gI2: int
var gIp, gIq: ptr int
var gCs: array[8, char]
var gCsp: cstring
proc o31() {.symexOpaque.} =
  var v = 9
  copyMem(gIp, addr v, sizeof(int))
proc mem1(k: int) =
  let a = gI1
  o31()
  if gI1 == 9 and a != 9: symexTarget("mem1")
proc o32() {.symexOpaque.} =
  zeroMem(gIq, sizeof(int))
proc mem2(k: int) =
  let a = gI2
  o32()
  if gI2 == 0 and a != 0: symexTarget("mem2")
proc o33() {.symexOpaque.} =
  gCsp[0] = 'z'
proc mem3(k: int) =
  let a = gCs[0]
  o33()
  if gCs[0] == 'z' and a != 'z': symexTarget("mem3")

# --- B25: the opaque's own local has the hook -----------------------------------------

var gW: int
type D = object
  v: int
proc `=destroy`(d: D) = gW = gW + 1
proc mkD(k: int): D = D(v: k)
proc mkLocal(k: int) =
  var d = mkD(k)
  d.v = 1
proc o6() {.symexOpaque.} =
  var d = mkD(1)
  d.v = 2
proc n6(k: int) =
  let a = gW
  o6()
  if gW != a: symexTarget("n6_live")
proc o7() {.symexOpaque.} =
  mkLocal(1)
proc n7(k: int) =
  let a = gW
  o7()
  if gW != a: symexTarget("n7_live")

# --- B26: foreign code inline --------------------------------------------------------

# `NI`, not `long`: `long` is 32 bits on Windows, and the declarations must agree.
{.emit: "extern NI gCw;".}
var gCw {.exportc: "gCw".}: int
proc o11() {.symexOpaque.} = {.emit: "gCw = gCw + 1;".}
proc n11(k: int) =
  let a = gCw
  o11()
  if gCw != a: symexTarget("n11_live")
proc o30() {.symexOpaque.} =
  asm """
    nop
  """
var gH5: int
proc asm1(k: int) =
  let a = gH5
  o30()
  if gH5 == a: symexTarget("asm1_same")

# --- what must stay exact ---------------------------------------------------------------

var gX1, gX2, gOther: int
type
  NopH = object
    v: int
  OthH = object
    v: int
  GenOnly = object
    s: seq[int]
  ErrC = object
    v: int
  PlainC = object
    a, b: int
  PlainD = object
    a: int
proc `=destroy`(d: NopH) = discard
proc `=destroy`(d: OthH) = gOther = 1
proc `=copy`(a: var ErrC; b: ErrC) {.error.}
proc `=copy`(a: var PlainC; b: PlainC) =
  a.a = b.a
  a.b = b.b
proc `=dup`(x: PlainD): PlainD =
  result.a = x.a
proc x1(k: int) = # a hook that writes nothing
  let a = gX1
  block:
    var o = NopH(v: k)
    o.v = 1
  if gX1 != a: symexTarget("x1_dead")
proc x2(k: int) = # no hook
  let a = gX1
  if gX1 != a: symexTarget("x2_dead")
proc x3(k: int) = # a hook that writes another global
  let a = gX2
  block:
    var o = OthH(v: k)
    o.v = 1
  if gX2 != a: symexTarget("x3_dead")
proc x4(k: int) = # generated hooks only
  let a = gX1
  block:
    var o = GenOnly(s: @[k])
    o.s.setLen(1)
  if gX1 != a: symexTarget("x4_dead")
proc x5(k: int) = # a hook the compiler refuses never runs
  let a = gX1
  block:
    var o = ErrC(v: k)
    o.v = 1
  if gX1 != a: symexTarget("x5_dead")
proc x6(k: int) = # no read of the hook's global at all
  gX2 = k
  block:
    var o = OthH(v: k)
    o.v = 1
  if gX2 != k: symexTarget("x6_dead")
  if gX2 == k: symexTarget("x6_live")
proc x7(k: int) = # copy hooks that make the plain copy
  var x = PlainC(a: k, b: k)
  var y = x
  x.a = 0
  y.b = y.b
  let d = PlainD(a: k)
  let e = d
  if y.a != k or e.a != k: symexTarget("x7_dead")
  symexTarget("x7_live")
iterator itW(k: int): int =
  gX2 = k
  yield k
proc x8(k: int) = # an iterator's body is read, and it holds no hook
  for v in itW(k):
    if gX2 == v: symexTarget("x8_live")
    if gX2 != v: symexTarget("x8_dead")

# --- hooks another module does not export ---------------------------------------------

proc hid1(k: int) =
  let a = gM
  block:
    var o = mkPrivD(k)
    o.v = 1
  if gM != a: symexTarget("hid1")
proc hid2(k: int) =
  let a = gM
  var x = PrivC(v: k)
  var y: PrivC
  y = x
  x.v = 0
  y.v = y.v
  if gM != a: symexTarget("hid2")
proc hid3(k: int) =
  let a = gM
  block:
    var o = mkShown(k)
    discard addr o
  if gM != a: symexTarget("hid3")
proc hid4(k: int) =
  let a = gM
  var x = mkPrivS(1)
  if useS(x) == 1:
    x = mkPrivS(k)
  x.v = 1
  if gM != a: symexTarget("hid4")
proc hid5(k: int) =
  let a = gM
  let x = PrivU(v: k)
  eatU(x)
  if x.v == k and gM != a: symexTarget("hid5")
proc hid6(k: int) = # `=wasMoved` and `=trace`: their declarations alone
  let a = gM
  var x = PrivW(v: k)
  x.v = 1
  var y = PrivT(v: k)
  y.v = 1
  if gM != a: symexTarget("hid6")
proc hid7(k: int) = # plain bits from another module: nothing to hide
  let a = gX1
  var o = PlainB(v: k)
  o.v = 1
  if gX1 != a: symexTarget("hid7_dead")
proc hid8(k: int) = # not plain bits, another module: no proof that nothing hides
  let a = gX1
  var o = WithSeq(s: @[k])
  o.s.setLen(1)
  if gX1 != a: symexTarget("hid8_dead")

suite "RFC-0005 S8cs: Nim runs each route":
  setup:
    if nh.len == 0:
      gPtr = addr gI
      gPtrs = @[addr gI]
      gPH = PH(p: addr gI)
      gIp = addr gI1
      gIq = addr gI2
      gCsp = cast[cstring](addr gCs[0])
      for k in [0, 1, 3]:
        gW = k; gCw = k; gX1 = k; gX2 = k; gH5 = k
        gI = k; nat(n1(k))
        gI = k; nat(n2(k))
        gI = k; nat(n3(k))
        gI = k; nat(n4(k))
        gI = k; nat(n5(k))
        gI = k; nat(n13(k))
        gI1 = k; nat(mem1(k))
        gI2 = k + 1; nat(mem2(k))
        gCs[0] = 'a'; nat(mem3(k))
        nat(n6(k)); nat(n7(k)); nat(n11(k)); nat(asm1(k))
        nat(x1(k)); nat(x2(k)); nat(x3(k)); nat(x4(k)); nat(x5(k)); nat(x6(k))
        nat(x7(k)); nat(x8(k))
        nat(hid1(k)); nat(hid2(k)); nat(hid3(k)); nat(hid4(k)); nat(hid5(k))
        nat(hid7(k)); nat(hid8(k))

  test "the labels the old verdicts denied are reached":
    for l in ["n1_live", "n2_live", "n3_live", "n4_live", "n5_live", "n13_live",
              "mem1", "mem2", "mem3", "n6_live", "n7_live", "n11_live", "asm1_same",
              "x6_live", "x7_live", "x8_live",
              "hid1", "hid2", "hid3", "hid4", "hid5"]:
      checkpoint l
      check l in nh

  test "the exact sxUnsat pins agree":
    for l in ["n1_dead", "x1_dead", "x2_dead", "x3_dead", "x4_dead", "x5_dead",
              "x6_dead", "x7_dead", "x8_dead", "hid7_dead", "hid8_dead"]:
      checkpoint l
      check l notin nh

suite "RFC-0005 S8cs: B24, an opaque's store behind a read position":
  test "a local alias, a field of a local copy, a loop, an address, a by-value callee":
    notUnsat(n1, "n1_live", feOpaqueEffectHavoc)
    notUnsat(n1, "n1_dead", feOpaqueEffectHavoc)
    notUnsat(n2, "n2_live", feOpaqueEffectHavoc)
    notUnsat(n3, "n3_live", feOpaqueEffectHavoc)
    notUnsat(n4, "n4_live", feOpaqueEffectHavoc)
    notUnsat(n5, "n5_live", feOpaqueEffectHavoc)
    notUnsat(n13, "n13_live", feOpaqueEffectHavoc)
  test "copyMem, zeroMem, a cstring store":
    notUnsat(mem1, "mem1", feOpaqueEffectHavoc)
    notUnsat(mem2, "mem2", feOpaqueEffectHavoc)
    notUnsat(mem3, "mem3", feOpaqueEffectHavoc)

suite "RFC-0005 S8cs: B25, an opaque's local holds the hook":
  test "directly, through a callee":
    declined(n6, "n6_live")
    declined(n7, "n7_live")

suite "RFC-0005 S8cs: B26, foreign code inline":
  test "emit":
    exactSat(n11, "n11_live")
    let r = symexFind(n11, tLabel("n11_live"))
    check r.errors.hasKind(feOpaqueEffectHavoc)
  test "asm":
    exactSat(asm1, "asm1_same")

suite "RFC-0005 S8cs: hooks another module does not export":
  test "each kind declines":
    declined(hid1, "hid1")
    declined(hid2, "hid2")
    declined(hid3, "hid3")
    declined(hid4, "hid4")
    declined(hid5, "hid5")
    declined(hid6, "hid6")
  test "plain bits stay exact; a type with no proof declines":
    exactUnsat(hid7, "hid7_dead")
    declined(hid8, "hid8_dead")

suite "RFC-0005 S8cs: what stays exact":
  test "a hook that writes nothing":
    exactUnsat(x1, "x1_dead")
  test "no hook":
    exactUnsat(x2, "x2_dead")
  test "a hook that writes another global":
    exactUnsat(x3, "x3_dead")
  test "generated hooks only":
    exactUnsat(x4, "x4_dead")
  test "a hook the compiler refuses":
    exactUnsat(x5, "x5_dead")
  test "the walked write of a global the hook does not touch":
    exactUnsat(x6, "x6_dead")
    exactSat(x6, "x6_live")
  test "copy hooks that make the plain copy":
    exactUnsat(x7, "x7_dead")
    exactSat(x7, "x7_live")
  test "an iterator's body is read":
    exactSat(x8, "x8_live")
    exactUnsat(x8, "x8_dead")
