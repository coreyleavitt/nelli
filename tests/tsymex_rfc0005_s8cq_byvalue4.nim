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
import std/[tables]
type
  Box[T] = object
    a: T
    b, c, d: int
  DS = distinct seq[int]
  BR {.byref.} = object
    x: int
  BC {.bycopy.} = object
    x: int
  AliasO = O1
  O1 = object
    x: int
  O4 = object
    x, b, c, d: int
  SetS = set[0..7]
  SetB = set[0..200]
  H = object
    s: seq[int]
  B0 = ref object of RootObj
  D0 = ref object of B0
  Hk = object
    x: int
    y: seq[int]
var gBox: Box[int]
var gDS: DS
var gBR: BR
var gBC: BC
var gAl: AliasO
var gSetS: SetS
var gSetB: SetB
var gs: seq[int]
var gO4: O4
var gInt: int
var gH: H
var gPtr: ptr int
var gCb: proc (): int {.nimcall.}
var gRf: ref int
proc oneC(): int = 1
proc twoC(): int = 50
proc wBox(a: Box[int]): int = (gBox.a = 50; a.a)
proc wDS(a: DS): int = (seq[int](gDS)[0] = 50; seq[int](a)[0])
proc wBR(a: BR): int = (gBR.x = 50; a.x)
proc wBC(a: BC): int = (gBC.x = 50; a.x)
proc wAl(a: AliasO): int = (gAl.x = 50; a.x)
proc wSetS(a: SetS): bool = (gSetS = {7}; 7 in a)
proc wSetB(a: SetB): bool = (gSetB = {7}; 7 in a)
proc wIntByref(a {.byref.}: int): int = (gInt = 50; a)
proc wCopyPrg(a {.bycopy.}: O4): int = (gO4.x = 50; a.x)
proc wPtr2(p: ptr seq[int]; a: seq[int]): int = (p[][0] = 50; a[0])
proc gw(a: seq[int]): int = (gs[0] = 50; a[0])
proc vchain(v: var seq[int]): int = gw(v)
method wr(b: B0) {.base.} = discard
method wr(b: D0) = gs[0] = 50
proc wMeth(b: B0; a: seq[int]): int = (b.wr(); a[0])
proc wrS() {.nimcall.} = gs[0] = 50
proc wCb2(cb: proc () {.nimcall.}; a: seq[int]): int = (cb(); a[0])
proc vgs(a: varargs[seq[int]]): int = (gs[0] = 50; a[0][0])
proc noW(a: seq[int]): int = a[0]
proc readG(a: seq[int]): int = a[0] + gs[0]
proc pa(a: O4): ptr int = unsafeAddr a.x
proc keepP(a: O4) = gPtr = unsafeAddr a.x
proc vw(h: H): lent seq[int] = h.s
proc idS(a: seq[int]): seq[int] = a
proc idO(a: O4): O4 = a
proc wCbV(a: proc (): int {.nimcall.}): int = (gCb = twoC; a())
proc wInt(a: int): int = (gInt = 50; a)
proc wRef(a: ref int): int = (new gRf; gRf[] = 50; a[])
proc wRefCell(a: ref int): int = (gRf[] = 50; a[])
proc wEmit(a: seq[int]): int =
  {.emit: "/*x*/".}
  a[0]
proc recW(a: seq[int]; d: int): int =
  if d > 0: return recW(a, d - 1)
  a[0]
proc pBox(x: int) =
  if x == 50: return
  gBox.a = x
  let r = wBox(gBox)
  if r == 50: symexTarget("box_r50")
  if r == x: symexTarget("box_rx")
proc pDS(x: int) =
  if x == 50: return
  gDS = DS(@[x])
  let r = wDS(gDS)
  if r == 50: symexTarget("ds_r50")
  if r == x: symexTarget("ds_rx")
proc pBR(x: int) =
  if x == 50: return
  gBR.x = x
  let r = wBR(gBR)
  if r == 50: symexTarget("br_r50")
  if r == x: symexTarget("br_rx")
proc pBC(x: int) =
  if x == 50: return
  gBC.x = x
  let r = wBC(gBC)
  if r == 50: symexTarget("bc_r50")
  if r == x: symexTarget("bc_rx")
proc pAl(x: int) =
  if x == 50: return
  gAl.x = x
  let r = wAl(gAl)
  if r == 50: symexTarget("al_r50")
  if r == x: symexTarget("al_rx")
proc pSetS(x: int) =
  if x == 50: return
  gSetS = {}
  let r = wSetS(gSetS)
  if r: symexTarget("sets_seen")
  else: symexTarget("sets_not")
proc pSetB(x: int) =
  if x == 50: return
  gSetB = {}
  let r = wSetB(gSetB)
  if r: symexTarget("setb_seen")
  else: symexTarget("setb_not")
proc pIntByref(x: int) =
  if x == 50: return
  gInt = x
  let r = wIntByref(gInt)
  if r == 50: symexTarget("ibr_r50")
  if r == x: symexTarget("ibr_rx")
proc pCopyPrg(x: int) =
  if x == 50: return
  gO4.x = x
  let r = wCopyPrg(gO4)
  if r == 50: symexTarget("cp_r50")
  if r == x: symexTarget("cp_rx")
proc pPtr2(x: int) =
  if x == 50: return
  var s = @[x]
  let p = addr s
  let r = wPtr2(p, s)
  if r == 50: symexTarget("ptr2_r50")
  if r == x: symexTarget("ptr2_rx")
proc pChain(x: int) =
  if x == 50: return
  gs = @[x]
  let r = vchain(gs)
  if r == 50: symexTarget("chain_r50")
  if r == x: symexTarget("chain_rx")
proc pMeth(x: int) =
  if x == 50: return
  gs = @[x]
  let b: B0 = D0()
  let r = wMeth(b, gs)
  if r == 50: symexTarget("meth_r50")
  if r == x: symexTarget("meth_rx")
proc pCb2(x: int) =
  if x == 50: return
  gs = @[x]
  let r = wCb2(wrS, gs)
  if r == 50: symexTarget("cb2_r50")
  if r == x: symexTarget("cb2_rx")
proc pVg(x: int) =
  if x == 50: return
  gs = @[x]
  let r = vgs(gs)
  if r == 50: symexTarget("vg_r50")
  if r == x: symexTarget("vg_rx")
proc pNoW(x: int) =
  if x == 50: return
  gs = @[x]
  let r = noW(gs)
  if r == x: symexTarget("now_rx")
  else: symexTarget("now_ne")

for x in [1, 2]:
  nat(pBox(x))
  nat(pDS(x))
  nat(pBR(x))
  nat(pBC(x))
  nat(pSetS(x))
  nat(pSetB(x))
  nat(pIntByref(x))
  nat(pCopyPrg(x))
  nat(pPtr2(x))
  nat(pChain(x))
  nat(pMeth(x))
  nat(pCb2(x))
  nat(pVg(x))
  nat(pNoW(x))

suite "tsymex_rfc0005_s8cq_byvalue4":
  test "verdicts against Nim":
    pin(pBox, "box_r50", true, sxUnknown)
    pin(pBox, "box_rx", false, sxUnknown)
    pin(pDS, "ds_r50", true, sxUnknown)
    pin(pDS, "ds_rx", false, sxUnknown)
    pin(pBR, "br_r50", true, sxUnknown)
    pin(pBR, "br_rx", false, sxUnknown)
    pin(pBC, "bc_r50", false, sxUnknown)
    pin(pBC, "bc_rx", true, sxUnknown)
    pin(pSetS, "sets_seen", false, sxUnknown)
    pin(pSetS, "sets_not", true, sxUnknown)
    pin(pSetB, "setb_seen", true, sxUnknown)
    pin(pSetB, "setb_not", false, sxUnknown)
    pin(pIntByref, "ibr_r50", true, sxUnknown)
    pin(pIntByref, "ibr_rx", false, sxUnknown)
    pin(pCopyPrg, "cp_r50", false, sxUnknown)
    pin(pCopyPrg, "cp_rx", true, sxUnknown)
    pin(pPtr2, "ptr2_r50", true, sxUnknown)
    pin(pPtr2, "ptr2_rx", false, sxUnknown)
    pin(pChain, "chain_r50", true, sxUnknown)
    pin(pChain, "chain_rx", false, sxUnknown)
    pin(pMeth, "meth_r50", true, sxUnknown)
    pin(pMeth, "meth_rx", false, sxUnknown)
    pin(pCb2, "cb2_r50", true, sxUnknown)
    pin(pCb2, "cb2_rx", false, sxUnknown)
    pin(pVg, "vg_r50", true, sxUnknown)
    pin(pVg, "vg_rx", false, sxUnknown)
    pin(pNoW, "now_rx", true, sxSat)
    pin(pNoW, "now_ne", false, sxUnsat)
