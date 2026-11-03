## RFC-0005 slice S8cq, item 3 -- a call in a location a lowering evaluates twice.
##
## Nim takes the address of the target once. A lowering that reads the target and
## writes it back lowers it twice, so `inc(getR()[])` called `getR` twice in the
## walk: a false `sxUnsat` on one call and a false `sxSat` on two. A lowering that
## evaluates its target apart now declines unless the target is proved free of a
## call (`lvalueHasCall`, an allowlist of node kinds). A shape that stays decided
## has its native answer pinned beside it.
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
import nelli/smt/canonicalize
import std/tables
type Sm = object
  a: int
type Big = object
  a: array[16, int]
var gs: seq[int]
var gSm: Sm
var gBig: Big
var gR: ref int
var gN: int

proc gWrite(a: seq[int]): int =
  gs[0] = 50
  a[0]
proc gWriteSm(a: Sm): int =
  gSm.a = 50
  a.a
proc gWriteBig(a: Big): int =
  gBig.a[0] = 50
  a.a[0]
proc wr() = gs[0] = 50
proc outerR(a: seq[int]): int =
  wr()
  a[0]

# item 2
proc rab(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]
# item 3
proc getR(): ref int =
  inc gN
  gR
proc sInc(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gR = new int
  gR[] = x
  inc(getR()[])
  if gN == 1: symexTarget("ir_once")
  if gN == 2: symexTarget("ir_twice")
proc sSwap(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gR = new int
  gR[] = x
  var y = 7
  swap(getR()[], y)
  if gN == 1 and y == x: symexTarget("sr_once")
  if gN == 2: symexTarget("sr_twice")
proc sDec(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gR = new int
  gR[] = x
  dec(getR()[])
  if gN == 1: symexTarget("dr_once")
  if gN == 2: symexTarget("dr_twice")
proc sPlus(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gR = new int
  gR[] = x
  getR()[] += 1
  if gN == 1: symexTarget("pe_once")
  if gN == 2: symexTarget("pe_twice")
proc sAsg(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gR = new int
  gR[] = x
  getR()[] = 3
  if gN == 1 and gR[] == 3: symexTarget("as_once")
  if gN == 2: symexTarget("as_twice")

var gSeqR: ref seq[int]
proc getSeqR(): ref seq[int] =
  inc gN
  gSeqR
proc sAdd(x: int) =
  gN = 0
  gSeqR = new seq[int]
  gSeqR[] = @[1, 2]
  getSeqR()[].add x
  if gN == 1: symexTarget("ad_once")
  if gN == 2: symexTarget("ad_twice")
proc sSetLen(x: int) =
  gN = 0
  gSeqR = new seq[int]
  gSeqR[] = @[x, 2]
  getSeqR()[].setLen(1)
  if gN == 1: symexTarget("sl_once")
  if gN == 2: symexTarget("sl_twice")
proc sDel(x: int) =
  gN = 0
  gSeqR = new seq[int]
  gSeqR[] = @[x, 2]
  getSeqR()[].del(0)
  if gN == 1: symexTarget("de_once")
  if gN == 2: symexTarget("de_twice")

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(sInc(x))
  nat(sSwap(x))
  nat(sDec(x))
  nat(sPlus(x))
  nat(sAsg(x))
  nat(sAdd(x))
  nat(sSetLen(x))
  nat(sDel(x))

suite "tsymex_rfc0005_s8cq_twice":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 252

  test "verdicts against Nim":
    pin(sInc, "ir_once", true, sxUnknown)
    pin(sInc, "ir_twice", false, sxUnknown)
    pin(sSwap, "sr_once", true, sxUnknown)
    pin(sSwap, "sr_twice", false, sxUnknown)
    pin(sDec, "dr_once", true, sxUnknown)
    pin(sDec, "dr_twice", false, sxUnknown)
    pin(sPlus, "pe_once", true, sxUnknown)
    pin(sPlus, "pe_twice", false, sxUnknown)
    pin(sAsg, "as_once", true, sxSat)
    pin(sAsg, "as_twice", false, sxUnsat)
    pin(sAdd, "ad_once", true, sxSat)
    pin(sAdd, "ad_twice", false, sxUnsat)
    pin(sSetLen, "sl_once", true, sxUnknown)
    pin(sSetLen, "sl_twice", false, sxUnknown)
    pin(sDel, "de_once", true, sxSat)
    pin(sDel, "de_twice", false, sxUnsat)
