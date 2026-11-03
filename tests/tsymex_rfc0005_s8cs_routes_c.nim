## RFC-0005 S8cs -- the stores to a variable that the walk does not see: the
## lifetime hooks the compiler inserts.
##
## Every expectation is Nim's: the "nim" tests run the SUT natively, and a route
## pinned here as a decline is one that native run proved live: the verdict the
## walk used to give from its stale value was false, not lucky.
## `tsymex_rfc0005_s8cs_routes2` holds the opaque routes and the exact verdicts.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with `tsymex_rfc0005_s8cs_routes`,
## `tsymex_rfc0005_s8cs_routes_b`. Split so that each part compiles and runs in
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

# --- open code: a stored closure, a dynamic subtype, a method, a thread ----------------------

var gH1, gH2, gH3, gH4: int
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

suite "RFC-0005 S8cs: no global at all":
  test "a local a pointer addresses":
    declined(local1, "local1_live")
    declined(local1, "local1_dead")
  test "a heap cell":
    declined(heap1, "heap1_live")
    declined(heap1, "heap1_dead")
    declined(heap2, "heap2_live")
    declined(heap2, "heap2_dead")
  test "the copy a value hook makes":
    declined(value1, "value1_live")
    declined(value1, "value1_dead")
    declined(value2, "value2_live")
    declined(value2, "value2_dead")
    declined(value3, "value3_live")
    declined(value3, "value3_dead")

suite "RFC-0005 S8cs: version floor":
  test "the walker's semantics moved":
    check parseInt(symexWalkerVersion) >= 260
