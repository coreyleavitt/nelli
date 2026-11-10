## RFC-0005 S8cs -- the stores to a variable that the walk does not see: the
## lifetime hooks the compiler inserts.
##
## Every expectation is Nim's: the "nim" tests run the SUT natively, and a route
## pinned here as a decline is one that native run proved live: the verdict the
## walk used to give from its stale value was false, not lucky.
## `tsymex_rfc0005_s8cs_routes2` holds the opaque routes and the exact verdicts.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8cs_routes_b`, `tsymex_rfc0005_s8cs_routes_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 64 s).
import std/[unittest, strutils, sets, tables]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers
import ./s8cu_helpers except show

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

template declined(fn: typed, lbl: string) =
  ## The route's store is unseen: no definite verdict, with the reason in band.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feGlobalRouteUnproved)

# --- B22: a hook writes a global the path read first ---------------------------

type D = object
  v: int
var gW: int
proc `=destroy`(d: D) = gW = gW + 1
proc mkD(k: int): D = D(v: k)
proc mkLocal(k: int) =
  var d = mkD(k)
  d.v = 1

proc k1(k: int) =
  let a = gW
  block:
    var d = mkD(k)
    d.v = 1
  if gW != a: symexTarget("k1")
proc k2(k: int) =
  let a = gW
  proc inner() =
    var d = mkD(k)
    d.v = 1
  inner()
  if gW != a: symexTarget("k2")
proc k3(k: int) =
  let a = gW
  mkLocal(k)
  if gW != a: symexTarget("k3")
proc k4(k: int) =
  let a = gW
  var d = mkD(k)
  d = mkD(k)
  if gW != a: symexTarget("k4")
proc k5(k: int) =
  let a = gW
  for i in 0 .. 1:
    var d = mkD(i)
    d.v = 1
  if gW != a: symexTarget("k5")
proc k6(k: int) =
  let a = gW
  block:
    var o: tuple[d: D, n: int]
    o.n = k
  if gW != a: symexTarget("k6")
proc k7(k: int) =
  let a = gW
  block:
    var xs = @[mkD(k)]
    xs.setLen(1)
  if gW != a: symexTarget("k7")
proc k8(k: int) =
  let a = gW
  var d = mkD(k)
  reset(d)
  if gW != a: symexTarget("k8")

# --- B23: a hook writes a global the path wrote first ----------------------------

proc w1(k: int) =
  gW = 0
  block:
    var d = mkD(k)
    d.v = 1
  if gW == 1: symexTarget("w1_live")
  if gW == 0: symexTarget("w1_dead")
proc w2(k: int) =
  gW = 0
  var d = mkD(k)
  d = mkD(k)
  if gW == 1: symexTarget("w2_live")
  if gW == 0: symexTarget("w2_dead")

# --- sxRaised rests on the same read --------------------------------------------

var gN1: int
type RH = object
  v: int
proc `=destroy`(d: RH) = gN1 = 1
proc raises1(k: int) =
  gN1 = 0
  block:
    var o = RH(v: k)
    o.v = 1
  if gN1 == 0:
    raise newException(ValueError, "stale")
  symexTarget("raises1_after")

# --- each hook, through the route it has --------------------------------------

var gA1, gA2, gA3, gA4, gA5: int
type
  HC = object
    v: int
  HS = object
    v: int
  HU = object
    v: int
  HW = object
    v: int
  HT = object
    v: int
  TCell = ref object
    h: HT
    next: TCell
proc `=copy`(a: var HC; b: HC) =
  a.v = b.v
  gA1 = gA1 + 1
proc `=sink`(a: var HS; b: HS) =
  a.v = b.v
  gA2 = gA2 + 1
proc `=dup`(a: HU): HU =
  result.v = a.v
  gA3 = gA3 + 1
proc `=wasMoved`(a: var HW) =
  a.v = 0
  gA4 = gA4 + 1
proc `=destroy`(a: HW) = discard a.v
proc `=trace`(a: var HT; env: pointer) = gA5 = gA5 + 1
proc mkHS(k: int): HS = HS(v: k)
proc useS(x: HS): int = x.v
proc eatU(x: sink HU) = discard x.v
proc eatW(x: sink HW) = discard x.v

proc copy1(k: int) =
  let a = gA1
  var x = HC(v: k)
  var y: HC
  y = x
  x.v = 0
  y.v = y.v
  if gA1 != a: symexTarget("copy1")
proc sink1(k: int) =
  let a = gA2
  var x = mkHS(1)
  if useS(x) == 1:
    x = mkHS(k)
  x.v = 1
  if gA2 != a: symexTarget("sink1")
proc dup1(k: int) =
  let a = gA3
  let x = HU(v: k)
  eatU(x)
  if x.v == k and gA3 != a: symexTarget("dup1")
proc moved1(k: int) =
  let a = gA4
  block:
    var x = HW(v: k)
    if k >= 0: eatW(x)
  if gA4 != a: symexTarget("moved1")
proc cycle(k: int) =
  var c = TCell(h: HT(v: k))
  c.next = c
proc trace1(k: int) = # only Nim runs this one: the cycle collector calls the hook
  let a = gA5
  cycle(k)
  GC_fullCollect()
  if gA5 != a: symexTarget("trace1")
proc trace2(k: int) =
  let a = gA5
  var x = HT(v: k)
  x.v = 1
  if gA5 != a: symexTarget("trace2")

# --- the hook runs other code ------------------------------------------------------

var gB1, gB2, gB3: int
type
  In1 = object
    v: int
  Out1 = object
    v: int
  Rc = object
    v: int
  Lp = object
    v: int
proc `=destroy`(d: In1) = gB1 = gB1 + 1
proc `=destroy`(d: Out1) =
  var i = In1(v: 1)
  i.v = 2
proc recW(n: int) =
  if n > 0:
    gB2 = gB2 + 1
    recW(n - 1)
proc `=destroy`(d: Rc) = recW(3)
proc `=destroy`(d: Lp) =
  var i = 0
  while i < 2:
    gB3 = gB3 + 1
    inc i
proc hookInHook(k: int) =
  let a = gB1
  block:
    var o = Out1(v: k)
    o.v = 1
  if gB1 != a: symexTarget("hookInHook")
proc hookRec(k: int) =
  let a = gB2
  block:
    var o = Rc(v: k)
    o.v = 1
  if gB2 != a: symexTarget("hookRec")
proc hookLoop(k: int) =
  let a = gB3
  block:
    var o = Lp(v: k)
    o.v = 1
  if gB3 != a: symexTarget("hookLoop")

# --- the hook stores through a pointer, or in foreign code --------------------------

var gC1: int
var gCp: ptr int
# `NI`, not `long`: `long` is 32 bits on Windows, and the declarations must agree.
{.emit: "extern NI gCw2;".}
var gCw2 {.exportc: "gCw2".}: int
type
  PtrH = object
    v: int
  EmH = object
    v: int
proc `=destroy`(d: PtrH) = gCp[] = gCp[] + 1
proc `=destroy`(d: EmH) = {.emit: "gCw2 = gCw2 + 1;".}
proc hookPtr(k: int) =
  let a = gC1
  block:
    var o = PtrH(v: k)
    o.v = 1
  if gC1 != a: symexTarget("hookPtr")
proc hookEmit(k: int) =
  let a = gCw2
  block:
    var o = EmH(v: k)
    o.v = 1
  if gCw2 != a: symexTarget("hookEmit")

# --- a part of a global ---------------------------------------------------------------

var gO: tuple[a, b: int]
var gAr: array[2, int]
var gSq: seq[int]
var gTb: Table[string, int]
type
  FldH = object
    v: int
  ArrH = object
    v: int
  SqH = object
    v: int
  TbH = object
    v: int
proc `=destroy`(d: FldH) = gO.a = gO.a + 1
proc `=destroy`(d: ArrH) = gAr[0] = gAr[0] + 1
proc `=destroy`(d: SqH) =
  if gSq.len > 0: gSq[0] = gSq[0] + 1
proc `=destroy`(d: TbH) = gTb["a"] = gTb.getOrDefault("a") + 1
proc part1(k: int) =
  let a = gO.a
  block:
    var o = FldH(v: k)
    o.v = 1
  if gO.a != a: symexTarget("part1")
proc part2(k: int) =
  let a = gAr[0]
  block:
    var o = ArrH(v: k)
    o.v = 1
  if gAr[0] != a: symexTarget("part2")
proc part3(k: int) =
  if gSq.len == 0: return
  let a = gSq[0]
  block:
    var o = SqH(v: k)
    o.v = 1
  if gSq[0] != a: symexTarget("part3")
proc part4(k: int) =
  if "a" notin gTb: return
  let a = gTb["a"]
  block:
    var o = TbH(v: k)
    o.v = 1
  if gTb["a"] != a: symexTarget("part4")

# --- the read goes by another name ------------------------------------------------------

var gE1, gE2, gE3, gE4: int
type
  VarH = object
    v: int
  AddrH = object
    v: int
  PtrPH = object
    v: int
  PtrO = object
    a: int
  PoH = object
    v: int
var gPo: PtrO
proc `=destroy`(d: VarH) = gE1 = gE1 + 1
proc `=destroy`(d: AddrH) = gE2 = gE2 + 1
proc `=destroy`(d: PtrPH) = gE3 = gE3 + 1
proc `=destroy`(d: PoH) = gPo.a = gPo.a + 1
proc viaVar(x: var int; k: int) =
  let a = x
  block:
    var o = VarH(v: k)
    o.v = 1
  if x != a: symexTarget("alias_var")
proc aliasVar(k: int) = viaVar(gE1, k)
proc aliasAddr(k: int) =
  let p = addr gE2
  let a = p[]
  block:
    var o = AddrH(v: k)
    o.v = 1
  if p[] != a: symexTarget("alias_addr")
proc aliasPtr(p: ptr int; k: int) =
  # The program names no global: the hook does, and `p` may address it.
  if p == nil: return
  let a = p[]
  block:
    var o = PtrPH(v: k)
    o.v = 1
  if p[] != a: symexTarget("alias_ptr")
proc aliasPtrObj(p: ptr PtrO; k: int) =
  if p == nil: return
  let a = p.a
  block:
    var o = PoH(v: k)
    o.v = 1
  if p.a != a: symexTarget("alias_ptrobj")

# --- the value that holds the hook --------------------------------------------------------

var gF1, gF2, gF3, gF4, gF5, gF6: int
type
  GenH[T] = object
    v: T
  RefH = ref object
    v: int
  FieldHolder = object
    h: HoldH
    n: int
  HoldH = object
    v: int
  SeqH = object
    v: int
  RefValH = object
    v: int
  TabH = object
    v: int
proc `=destroy`[T](d: GenH[T]) = gF1 = gF1 + 1
proc `=destroy`(d: typeof(RefH()[])) = gF2 = gF2 + 1
proc `=destroy`(d: HoldH) = gF3 = gF3 + 1
proc `=destroy`(d: SeqH) = gF4 = gF4 + 1
proc `=destroy`(d: RefValH) = gF5 = gF5 + 1
proc `=destroy`(d: TabH) = gF6 = gF6 + 1
proc hold1(k: int) =
  let a = gF1
  block:
    var o = GenH[int](v: k)
    o.v = 1
  if gF1 != a: symexTarget("hold1")
proc hold2(k: int) =
  let a = gF2
  block:
    var o = RefH(v: k)
    o.v = 1
  if gF2 != a: symexTarget("hold2")
proc hold3(k: int) =
  let a = gF3
  block:
    var o: FieldHolder
    o.n = k
  if gF3 != a: symexTarget("hold3")
proc hold4(k: int) =
  let a = gF4
  block:
    var o = @[SeqH(v: k)]
    o.setLen(1)
  if gF4 != a: symexTarget("hold4")
proc hold5(k: int) =
  let a = gF5
  block:
    var o: ref RefValH
    new o
    o.v = k
  if gF5 != a: symexTarget("hold5")
proc hold6(k: int) =
  let a = gF6
  block:
    var o: Table[string, TabH]
    o["a"] = TabH(v: k)
  if gF6 != a: symexTarget("hold6")

# --- a generic routine, each instance ------------------------------------------------------

var gG1, gG2: int
type
  GD = object
    v: int
  GD2 = object
    v: int
  IntHold = object
    v: int
proc `=destroy`(d: GD) = gG1 = gG1 + 1
proc `=destroy`(d: GD2) = gG2 = gG2 + 1
proc mkGD(k: int): GD = GD(v: k)
proc genDrop[T](x: sink T) = discard x
proc genLocal[T](k: int) =
  var x: T
  x.v = k
proc gen1(k: int) =
  let a = gG1
  genDrop(mkGD(k))
  if gG1 != a: symexTarget("gen1")
proc gen2first(k: int) =
  let a = gG2
  genLocal[IntHold](k)
  if gG2 != a: symexTarget("gen2first")
proc gen2(k: int) = # a later instance of a routine another entry already read
  let a = gG2
  genLocal[GD2](k)
  if gG2 != a: symexTarget("gen2")

# --- open code: a stored closure, a dynamic subtype, a method, a thread ----------------------

var gH1, gH2, gH3, gH4: int
var gClo: proc ()
type
  ClH = object
    v: int
  BaseT = ref object of RootObj
  SubT = ref object of BaseT
    d: SubH
  SubH = object
    v: int
  MBase = ref object of RootObj
  MSub = ref object of MBase
proc `=destroy`(d: ClH) = gH1 = gH1 + 1
proc `=destroy`(d: SubH) = gH2 = gH2 + 1
method mw(o: MBase) {.base.} = discard
method mw(o: MSub) = gH3 = gH3 + 1
proc setClo(k: int) =
  var h = ClH(v: k)
  gClo = proc () =
    h.v = h.v + 1
proc mkSub(k: int): BaseT = SubT(d: SubH(v: k))
proc open1(k: int) =
  setClo(k)
  let a = gH1
  gClo = nil
  if gH1 != a: symexTarget("open1")
proc open2(k: int) =
  var b = mkSub(k)
  let a = gH2
  b = nil
  if gH2 != a: symexTarget("open2")
proc open3(k: int) =
  let a = gH3
  let o: MBase = MSub()
  mw(o)
  if gH3 != a: symexTarget("open3")

# --- no global: a heap cell, a local, the value itself ---------------------------------------

var gKp: ptr int
var gMr: ref int
type
  LocH = object
    v: int
  HeapH = object
    r: ref int
  HeapG = object
    v: int
  ValC = object
    v: int
  ValS = object
    v: int
  MissC = object
    a, b: int
proc `=destroy`(d: LocH) =
  if gKp != nil: gKp[] = 7
proc `=destroy`(d: HeapH) =
  if d.r != nil: d.r[] = d.r[] + 1
proc `=destroy`(d: HeapG) =
  if gMr != nil: gMr[] = gMr[] + 1
proc `=copy`(a: var ValC; b: ValC) = a.v = b.v + 1
proc `=sink`(a: var ValS; b: ValS) = a.v = b.v + 1
proc `=copy`(a: var MissC; b: MissC) = a.a = b.a
proc mkValS(k: int): ValS = ValS(v: k)
proc local1(k: int) =
  var x = 0
  gKp = addr x
  block:
    var o = LocH(v: k)
    o.v = 1
  gKp = nil
  if x == 7: symexTarget("local1_live")
  if x == 0: symexTarget("local1_dead")
proc heap1(k: int) =
  let r = new int
  r[] = k
  block:
    var o = HeapH(r: r)
    o.r[] = o.r[]
  if r[] != k: symexTarget("heap1_live")
  if r[] == k: symexTarget("heap1_dead")
proc heap2(k: int) =
  if gMr == nil: return
  let a = gMr[]
  block:
    var o = HeapG(v: k)
    o.v = 1
  if gMr[] != a: symexTarget("heap2_live")
  if gMr[] == a: symexTarget("heap2_dead")
proc value1(k: int) =
  var x = ValC(v: k)
  var y = x
  x.v = 0
  y.v = y.v
  if y.v != k: symexTarget("value1_live")
  if y.v == k: symexTarget("value1_dead")
proc value2(k: int) =
  var x = mkValS(0)
  if x.v == 0: x = mkValS(k)
  if x.v != k: symexTarget("value2_live")
  if x.v == k: symexTarget("value2_dead")
proc value3(k: int) =
  var x = MissC(a: k, b: k)
  var y: MissC
  y = x
  x.a = 0
  y.b = y.b
  if y.b != k: symexTarget("value3_live")
  if y.b == k: symexTarget("value3_dead")

suite "RFC-0005 S8cs: Nim runs each route":
  setup:
    if nh.len == 0:
      gCp = addr gC1
      gMr = new int
      gMr[] = 1
      for k in [0, 1, 3]:
        gSq = @[k]
        gTb = {"a": k}.toTable
        nat(k1(k)); nat(k2(k)); nat(k3(k)); nat(k4(k))
        nat(k5(k)); nat(k6(k)); nat(k7(k)); nat(k8(k))
        nat(w1(k)); nat(w2(k))
        try: nat(raises1(k))
        except ValueError: discard
        nat(copy1(k)); nat(sink1(k)); nat(dup1(k)); nat(moved1(k)); nat(trace1(k))
        nat(hookInHook(k)); nat(hookRec(k)); nat(hookLoop(k))
        nat(hookPtr(k)); nat(hookEmit(k))
        nat(part1(k)); nat(part2(k)); nat(part3(k)); nat(part4(k))
        nat(aliasVar(k)); nat(aliasAddr(k)); nat(aliasPtr(addr gE3, k))
        nat(aliasPtrObj(addr gPo, k))
        nat(hold1(k)); nat(hold2(k)); nat(hold3(k))
        nat(hold4(k)); nat(hold5(k)); nat(hold6(k))
        nat(gen1(k)); nat(gen2first(k)); nat(gen2(k))
        nat(open1(k)); nat(open2(k)); nat(open3(k))
        nat(local1(k)); nat(heap1(k)); nat(heap2(k))
        nat(value1(k)); nat(value2(k)); nat(value3(k))

  test "the label each decline would have denied is reached":
    for l in ["k1", "k2", "k3", "k4", "k5", "k6", "k7", "k8",
              "w1_live", "w2_live", "raises1_after",
              "copy1", "sink1", "dup1", "moved1", "trace1",
              "hookInHook", "hookRec", "hookLoop", "hookPtr", "hookEmit",
              "part1", "part2", "part3", "part4",
              "alias_var", "alias_addr", "alias_ptr", "alias_ptrobj",
              "hold1", "hold2", "hold3", "hold4", "hold5", "hold6",
              "gen1", "gen2",
              "open1", "open2", "open3",
              "local1_live", "heap1_live", "heap2_live",
              "value1_live", "value2_live", "value3_live"]:
      checkpoint l
      check l in nh

  test "the label each decline would have reported is not reached":
    for l in ["w1_dead", "w2_dead", "local1_dead", "heap1_dead", "value1_dead",
              "value2_dead", "gen2first"]:
      checkpoint l
      check l notin nh

suite "RFC-0005 S8cs: B22, a hook writes a global the path read":
  test "scope exit, callee, named callee, overwrite, loop, tuple, seq, reset":
    declined(k1, "k1")
    declined(k2, "k2")
    declined(k3, "k3")
    declined(k4, "k4")
    declined(k5, "k5")
    declined(k6, "k6")
    declined(k7, "k7")
    declined(k8, "k8")

suite "RFC-0005 S8cs: B23, a hook writes a global the path wrote":
  test "neither half of the false pair stands":
    declined(w1, "w1_live")
    declined(w1, "w1_dead")
    declined(w2, "w2_live")
    declined(w2, "w2_dead")
    # RFC-0016 SND-09: the decline as K9 pins.
    pinDecline(w2, cellKey(faCallShape, "hook/overwriteGlobalWrittenFirst"),
               feGlobalRouteUnproved, tLabel("w2_live"))
    pinDecline(w2, cellKey(faCallShape, "hook/overwriteGlobalWrittenFirst"),
               feGlobalRouteUnproved, tLabel("w2_dead"))
  test "sxRaised needs the read too":
    # Nim never raises here (the hook has written 1): the raise is the stale
    # value's.
    block:
      let r = symexFind(raises1, tLabel("raises1_after"))
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check r.errors.hasKind(feGlobalRouteUnproved)

suite "RFC-0005 S8cs: every hook kind":
  test "=copy, =sink, =dup, =wasMoved, =trace":
    declined(copy1, "copy1")
    declined(sink1, "sink1")
    declined(dup1, "dup1")
    declined(moved1, "moved1")
    declined(trace2, "trace2")
  test "a hook's own hook, a recursion, a loop":
    declined(hookInHook, "hookInHook")
    declined(hookRec, "hookRec")
    declined(hookLoop, "hookLoop")
  test "a store through a pointer, foreign code":
    declined(hookPtr, "hookPtr")
    declined(hookEmit, "hookEmit")
