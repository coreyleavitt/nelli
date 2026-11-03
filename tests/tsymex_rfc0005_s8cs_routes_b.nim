## RFC-0005 S8cs -- the stores to a variable that the walk does not see: the
## lifetime hooks the compiler inserts.
##
## Every expectation is Nim's: the "nim" tests run the SUT natively, and a route
## pinned here as a decline is one that native run proved live: the verdict the
## walk used to give from its stale value was false, not lucky.
## `tsymex_rfc0005_s8cs_routes2` holds the opaque routes and the exact verdicts.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with `tsymex_rfc0005_s8cs_routes`,
## `tsymex_rfc0005_s8cs_routes_c`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 64 s).
import std/[unittest, strutils, sets, tables]
import nelli/symex
import nelli/smt/canonicalize
import nelli/engine/markers

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

# --- sxRaised rests on the same read --------------------------------------------

var gN1: int
type RH = object
  v: int
proc `=destroy`(d: RH) = gN1 = 1

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
var gCp: ptr int
# `NI`, not `long`: `long` is 32 bits on Windows, and the declarations must agree.
{.emit: "extern NI gCw2;".}
type
  PtrH = object
    v: int
  EmH = object
    v: int
proc `=destroy`(d: PtrH) = gCp[] = gCp[] + 1
proc `=destroy`(d: EmH) = {.emit: "gCw2 = gCw2 + 1;".}

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

suite "RFC-0005 S8cs: where the store lands, where the read goes":
  test "a field, an array element, a seq element, a table value":
    declined(part1, "part1")
    declined(part2, "part2")
    declined(part3, "part3")
    declined(part4, "part4")
  test "a var formal, an address, a pointer of unknown origin":
    declined(aliasVar, "alias_var")
    declined(aliasAddr, "alias_addr")
    declined(aliasPtr, "alias_ptr")
    declined(aliasPtrObj, "alias_ptrobj")

suite "RFC-0005 S8cs: the value that holds the hook":
  test "generic, ref, field, seq, ref value, table value":
    declined(hold1, "hold1")
    declined(hold2, "hold2")
    declined(hold3, "hold3")
    declined(hold4, "hold4")
    declined(hold5, "hold5")
    declined(hold6, "hold6")
  test "a generic routine, per instance":
    declined(gen1, "gen1")
    # Read first, so a later instance sharing its cache entry would miss the hook.
    check symexFind(gen2first, tLabel("gen2first")).status == sxUnsat
    declined(gen2, "gen2")

suite "RFC-0005 S8cs: code the analysis cannot list":
  test "a stored closure, a dynamic subtype, a method":
    declined(open1, "open1")
    declined(open2, "open2")
    declined(open3, "open3")
