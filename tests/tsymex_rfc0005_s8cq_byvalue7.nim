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
##
## A local's memory has no other name but a pointer to it, and S8bs keeps that cell
## and the formal one location, so a local actual stays decided; a formal whose
## address the callee takes, a routine actual, and a `var` of the same local decline.
import std/[unittest, strutils, sets]
import nelli
import nelli/symex

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
proc p_ostr(x: char) =
  if x == 'z': return
  gOStr = OStr(st: "ab"); gOStr.st[0] = x
  let r = wOStr(gOStr)
  if r == 'z': symexTarget("ostr_r50")
  if r == x: symexTarget("ostr_rx")

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(p_ostr(char(ord('a') + (x + 3) mod 5)))

suite "tsymex_rfc0005_s8cq_byvalue7":
  test "verdicts against Nim":
    pin(p_ostr, "ostr_r50", true, sxUnknown)
    pin(p_ostr, "ostr_rx", false, sxUnknown)
