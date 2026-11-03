## RFC-0005 slice S8cq, item 1 -- a by-value formal and the memory Nim shares.
##
## Nim passes a formal by address when its type is over three words, a seq, a
## string, a set or an inheritable or `{.byref.}` object, and the walk binds it to
## a copy, so a write the callee makes through another name is read back through
## the formal natively and not in the walk: a false `sxUnsat` on the value it
## wrote and a false `sxSat` on the old one. The rule is inverted: a call is
## decided only when the type is on the allowlist (`typeCopiedByValue`, pinned on
## nine settings in `tsymex_rfc0005_s8cq_native`), or the callee with everything
## it reaches is proved to write nothing the actual could be (`byValueWritten`).
## Everything else declines; the exact model belongs to RFC-0016.
import std/[unittest, strutils, sets]
import nelli
import nelli/symex
import nelli/smt/canonicalize

var natHits: HashSet[string]

template nat(call: untyped) =
  block:
    symexCaptureBegin()
    try:
      call
    except CatchableError:
      discard
    for h in symexCaptureEnd(): natHits.incl h

template pin(fn: typed; lbl: static string; nativeHit: bool;
             want: SymexStatusKind) =
  ## Nim's own answer on the input loop above, then the walker's. Neither may
  ## contradict the other: `sxUnknown` is the decline RFC-0016 inherits.
  block:
    let r = symexFind(fn, tLabel(lbl))
    var parts: seq[string]
    for e in r.errors: parts.add $e.kind & ": " & e.msg
    checkpoint lbl & " " & $r.status & " [" & parts.join(", ") & "]"
    check (lbl in natHits) == nativeHit
    check r.status == want
    check not (nativeHit and r.status == sxUnsat)
    check not (not nativeHit and r.status == sxSat)

template pinFree(fn: typed; lbl: static string; want: SymexStatusKind) =
  ## As `pin`, for a shape Nim gives no one answer on: only the decline holds.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status
    check r.status == want
import std/[tables, strutils]
type
  O1 = object
    x: int
  O3 = object
    x, b, c: int
  O4 = object
    x, b, c, d: int
  O16 = object
    x, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15: int
  OS = object
    s: seq[int]
  OStr = object
    st: string
  OT = object
    t: Table[string, int]
  ONest = object
    o: OS
  Inh = object of RootObj
    x: int
  ByR {.byref.} = object
    x: int
  ByC {.bycopy.} = object
    x, b, c, d, e: int
  T1 = tuple[x: int]
  T4 = tuple[x, b, c, d: int]
  TS = tuple[x: int, s: seq[int]]
  A1 = array[1, int]
  ASm = array[2, int]
  ASeq = array[1, seq[int]]
  SC = set[char]
var
  gO1: O1
  gO3: O3
  gO4: O4
  gO16: O16
  gOS: OS
  gOStr: OStr
  gOT: OT
  gONest: ONest
  gInh: Inh
  gByR: ByR
  gByC: ByC
  gT1: T1
  gT4: T4
  gTS: TS
  gA1: A1
  gASm: ASm
  gASeq: ASeq
  gStr: string
  gSC: SC
  gs: seq[int]
  gss: seq[seq[int]]
  gHolder: tuple[s: seq[int]]
  gPs: ptr seq[int]
  gPO4: ptr O4
  gRO4: ref O4
  gRs: ref seq[int]
  gHook: proc () {.nimcall.}
proc wO1(a: O1): int =
  gO1.x = 50; a.x
proc wO3(a: O3): int =
  gO3.x = 50; a.x
proc wO4(a: O4): int =
  gO4.x = 50; a.x
proc wO16(a: O16): int =
  gO16.x = 50; a.x
proc wOS(a: OS): int =
  gOS.s[0] = 50; a.s[0]
proc wOStr(a: OStr): char =
  gOStr.st[0] = 'z'; a.st[0]
proc wOT(a: OT): int =
  gOT.t["a"] = 50; a.t["a"]
proc wONest(a: ONest): int =
  gONest.o.s[0] = 50; a.o.s[0]
proc wInh(a: Inh): int =
  gInh.x = 50; a.x
proc wByR(a: ByR): int =
  gByR.x = 50; a.x
proc wByC(a: ByC): int =
  gByC.x = 50; a.x
proc wT1(a: T1): int =
  gT1.x = 50; a.x
proc wT4(a: T4): int =
  gT4.x = 50; a.x
proc wTS(a: TS): int =
  gTS.s[0] = 50; a.s[0]
proc wA1(a: A1): int =
  gA1[0] = 50; a[0]
proc wASm(a: ASm): int =
  gASm[0] = 50; a[0]
proc wASeq(a: ASeq): int =
  gASeq[0][0] = 50; a[0][0]
proc wStr(a: string): char =
  gStr[0] = 'z'; a[0]
proc wSC(a: SC): bool =
  gSC.incl 'z'; 'z' in a
proc wFld(a: seq[int]): int =
  gOS.s[0] = 50; a[0]
proc wElem(a: seq[int]): int =
  gss[0][0] = 50; a[0]
proc wOA(a: openArray[int]): int =
  gs[0] = 50; a[0]
proc wPs(a: seq[int]): int =
  gPs[][0] = 50; a[0]
proc wPO4(a: O4): int =
  gPO4.x = 50; a.x
proc wRO4(a: O4): int =
  gRO4.x = 50; a.x
proc wRs(a: seq[int]): int =
  gRs[][0] = 50; a[0]
proc wVarS(v: var seq[int]; a: seq[int]): int =
  v[0] = 50; a[0]
proc wVarO4(v: var O4; a: O4): int =
  v.x = 50; a.x
proc wPtrS(p: ptr seq[int]; a: seq[int]): int =
  p[][0] = 50; a[0]
proc wPtrO4(p: ptr O4; a: O4): int =
  p.x = 50; a.x
proc wRefS(p: ref seq[int]; a: seq[int]): int =
  p[][0] = 50; a[0]
proc wRefO4(p: ref O4; a: O4): int =
  p.x = 50; a.x
proc wCb(cb: proc (); a: seq[int]): int =
  cb(); a[0]
proc wCbO(cb: proc (); a: O4): int =
  cb(); a.x
proc wHook(a: seq[int]): int =
  gHook(); a[0]
proc wrS() = gs[0] = 50
iterator itS(a: seq[int]): int =
  gs[0] = 50
  yield a[0]
iterator itO(a: O4): int =
  gO4.x = 50
  yield a.x
type B = ref object of RootObj
type D = ref object of B
method m(b: B; a: seq[int]): int {.base.} = a[0]
method m(b: D; a: seq[int]): int =
  gs[0] = 50; a[0]
method mo(b: B; a: O4): int {.base.} = a.x
method mo(b: D; a: O4): int =
  gO4.x = 50; a.x
proc wGen[T](a: seq[T]): T =
  gs[0] = 50; a[0]
proc wLent(a: O1): lent int =
  gO1.x = 50
  a.x
proc wSink(a: sink seq[int]): int =
  gs[0] = 50; a[0]
proc wRet(a: seq[int]): seq[int] =
  gs[0] = 50; a
proc wRetO(a: O4): O4 =
  gO4.x = 50; a
proc p_o1(x: int) =
  if x == 50: return
  gO1 = O1(x: x)
  let r = wO1(gO1)
  if r == 50: symexTarget("o1_r50")
  if r == x: symexTarget("o1_rx")
proc p_o3(x: int) =
  if x == 50: return
  gO3 = O3(x: x)
  let r = wO3(gO3)
  if r == 50: symexTarget("o3_r50")
  if r == x: symexTarget("o3_rx")
proc p_o4(x: int) =
  if x == 50: return
  gO4 = O4(x: x)
  let r = wO4(gO4)
  if r == 50: symexTarget("o4_r50")
  if r == x: symexTarget("o4_rx")
proc p_o16(x: int) =
  if x == 50: return
  gO16 = O16(x: x)
  let r = wO16(gO16)
  if r == 50: symexTarget("o16_r50")
  if r == x: symexTarget("o16_rx")
proc p_os(x: int) =
  if x == 50: return
  gOS = OS(s: @[x])
  let r = wOS(gOS)
  if r == 50: symexTarget("os_r50")
  if r == x: symexTarget("os_rx")
proc p_ot(x: int) =
  if x == 50: return
  gOT = OT(t: {"a": x}.toTable)
  let r = wOT(gOT)
  if r == 50: symexTarget("ot_r50")
  if r == x: symexTarget("ot_rx")
proc p_onest(x: int) =
  if x == 50: return
  gONest = ONest(o: OS(s: @[x]))
  let r = wONest(gONest)
  if r == 50: symexTarget("onest_r50")
  if r == x: symexTarget("onest_rx")
proc p_inh(x: int) =
  if x == 50: return
  gInh = Inh(x: x)
  let r = wInh(gInh)
  if r == 50: symexTarget("inh_r50")
  if r == x: symexTarget("inh_rx")
proc p_byr(x: int) =
  if x == 50: return
  gByR = ByR(x: x)
  let r = wByR(gByR)
  if r == 50: symexTarget("byr_r50")
  if r == x: symexTarget("byr_rx")
proc p_byc(x: int) =
  if x == 50: return
  gByC = ByC(x: x)
  let r = wByC(gByC)
  if r == 50: symexTarget("byc_r50")
  if r == x: symexTarget("byc_rx")
proc p_t1(x: int) =
  if x == 50: return
  gT1 = (x: x)
  let r = wT1(gT1)
  if r == 50: symexTarget("t1_r50")
  if r == x: symexTarget("t1_rx")
proc p_t4(x: int) =
  if x == 50: return
  gT4 = (x: x, b: 0, c: 0, d: 0)
  let r = wT4(gT4)
  if r == 50: symexTarget("t4_r50")
  if r == x: symexTarget("t4_rx")
proc p_ts(x: int) =
  if x == 50: return
  gTS = (x: x, s: @[x])
  let r = wTS(gTS)
  if r == 50: symexTarget("ts_r50")
  if r == x: symexTarget("ts_rx")
proc p_a1(x: int) =
  if x == 50: return
  gA1 = [x]
  let r = wA1(gA1)
  if r == 50: symexTarget("a1_r50")
  if r == x: symexTarget("a1_rx")
proc p_asm(x: int) =
  if x == 50: return
  gASm = [x, 0]
  let r = wASm(gASm)
  if r == 50: symexTarget("asm_r50")
  if r == x: symexTarget("asm_rx")
proc p_aseq(x: int) =
  if x == 50: return
  gASeq = [@[x]]
  let r = wASeq(gASeq)
  if r == 50: symexTarget("aseq_r50")
  if r == x: symexTarget("aseq_rx")
proc p_fld(x: int) =
  if x == 50: return
  gOS = OS(s: @[x])
  let r = wFld(gOS.s)
  if r == 50: symexTarget("fld_r50")
  if r == x: symexTarget("fld_rx")
proc p_elem(x: int) =
  if x == 50: return
  gss = @[@[x]]
  let r = wElem(gss[0])
  if r == 50: symexTarget("elem_r50")
  if r == x: symexTarget("elem_rx")
proc p_oa(x: int) =
  if x == 50: return
  gs = @[x]
  let r = wOA(gs)
  if r == 50: symexTarget("oa_r50")
  if r == x: symexTarget("oa_rx")
proc p_ps(x: int) =
  if x == 50: return
  gs = @[x]; gPs = addr gs
  let r = wPs(gs)
  if r == 50: symexTarget("ps_r50")
  if r == x: symexTarget("ps_rx")
proc p_po4(x: int) =
  if x == 50: return
  gO4 = O4(x: x); gPO4 = addr gO4
  let r = wPO4(gO4)
  if r == 50: symexTarget("po4_r50")
  if r == x: symexTarget("po4_rx")
proc p_ro4(x: int) =
  if x == 50: return
  new(gRO4); gRO4.x = x
  let r = wRO4(gRO4[])
  if r == 50: symexTarget("ro4_r50")
  if r == x: symexTarget("ro4_rx")
proc p_rs(x: int) =
  if x == 50: return
  new(gRs); gRs[] = @[x]
  let r = wRs(gRs[])
  if r == 50: symexTarget("rs_r50")
  if r == x: symexTarget("rs_rx")

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(p_o1(x))
  nat(p_o3(x))
  nat(p_o4(x))
  nat(p_o16(x))
  nat(p_os(x))
  nat(p_ot(x))
  nat(p_onest(x))
  nat(p_inh(x))
  nat(p_byr(x))
  nat(p_byc(x))
  nat(p_t1(x))
  nat(p_t4(x))
  nat(p_ts(x))
  nat(p_a1(x))
  nat(p_asm(x))
  nat(p_aseq(x))
  nat(p_fld(x))
  nat(p_elem(x))
  nat(p_oa(x))
  nat(p_ps(x))
  nat(p_po4(x))
  nat(p_ro4(x))
  nat(p_rs(x))

suite "tsymex_rfc0005_s8cq_byvalue2":
  test "verdicts against Nim":
    pin(p_o1, "o1_r50", false, sxUnsat)
    pin(p_o1, "o1_rx", true, sxSat)
    pin(p_o3, "o3_r50", false, sxUnsat)
    pin(p_o3, "o3_rx", true, sxSat)
    pin(p_o4, "o4_r50", true, sxUnknown)
    pin(p_o4, "o4_rx", false, sxUnknown)
    pin(p_o16, "o16_r50", true, sxUnknown)
    pin(p_o16, "o16_rx", false, sxUnknown)
    pin(p_os, "os_r50", true, sxUnknown)
    pin(p_os, "os_rx", false, sxUnknown)
    pin(p_ot, "ot_r50", true, sxUnknown)
    pin(p_ot, "ot_rx", false, sxUnknown)
    pin(p_onest, "onest_r50", true, sxUnknown)
    pin(p_onest, "onest_rx", false, sxUnknown)
    pin(p_inh, "inh_r50", true, sxUnknown)
    pin(p_inh, "inh_rx", false, sxUnknown)
    pin(p_byr, "byr_r50", true, sxUnknown)
    pin(p_byr, "byr_rx", false, sxUnknown)
    pin(p_byc, "byc_r50", false, sxUnknown)
    pin(p_byc, "byc_rx", true, sxUnknown)
    pin(p_t1, "t1_r50", false, sxUnsat)
    pin(p_t1, "t1_rx", true, sxSat)
    pin(p_t4, "t4_r50", true, sxUnknown)
    pin(p_t4, "t4_rx", false, sxUnknown)
    pin(p_ts, "ts_r50", true, sxUnknown)
    pin(p_ts, "ts_rx", false, sxUnknown)
    pin(p_a1, "a1_r50", true, sxUnknown)
    pin(p_a1, "a1_rx", false, sxUnknown)
    pin(p_asm, "asm_r50", true, sxUnknown)
    pin(p_asm, "asm_rx", false, sxUnknown)
    pin(p_aseq, "aseq_r50", true, sxUnknown)
    pin(p_aseq, "aseq_rx", false, sxUnknown)
    pin(p_fld, "fld_r50", true, sxUnknown)
    pin(p_fld, "fld_rx", false, sxUnknown)
    pin(p_elem, "elem_r50", true, sxUnknown)
    pin(p_elem, "elem_rx", false, sxUnknown)
    pin(p_oa, "oa_r50", true, sxUnknown)
    pin(p_oa, "oa_rx", false, sxUnknown)
    pin(p_ps, "ps_r50", true, sxUnknown)
    pin(p_ps, "ps_rx", false, sxUnknown)
    pin(p_po4, "po4_r50", true, sxUnknown)
    pin(p_po4, "po4_rx", false, sxUnknown)
    pin(p_ro4, "ro4_r50", true, sxUnknown)
    pin(p_ro4, "ro4_rx", false, sxUnknown)
    pin(p_rs, "rs_r50", true, sxUnknown)
    pin(p_rs, "rs_rx", false, sxUnknown)
