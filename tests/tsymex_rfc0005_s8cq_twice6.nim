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
import std/[tables, sets, strutils, sequtils]
type RX = ref object
  x: int
type RSq = ref object
  s: seq[int]
type RStr = ref object
  st: string
type RAr = ref object
  a: array[3, int]
type VO = object
  x: int
var gN, gM: int
var gR: ref int
var gP: ptr int
var gO: RX
var gOS: RSq
var gOStr: RStr
var gOA: RAr
var gSR: ref seq[int]
var gStrR: ref string
var gAR: ref array[3, int]
var gTR: ref Table[string, int]
var gSetR: ref set[char]
var gRR: ref ref int
var gV: VO
var gOxs: seq[RX]
var gOSeq: seq[RSq]
var gA2: array[3, int]
var gPs: seq[ref int]
proc getR(): ref int =
  inc gN
  gR
proc getO(): RX =
  inc gN
  gO
proc getOS(): RSq =
  inc gN
  gOS
proc getOStr(): RStr =
  inc gN
  gOStr
proc getOA(): RAr =
  inc gN
  gOA
proc getSR(): ref seq[int] =
  inc gN
  gSR
proc getStrR(): ref string =
  inc gN
  gStrR
proc getAR(): ref array[3, int] =
  inc gN
  gAR
proc getTR(): ref Table[string, int] =
  inc gN
  gTR
proc getSetR(): ref set[char] =
  inc gN
  gSetR
proc getRR(): ref ref int =
  inc gN
  gRR
proc getVar(): var VO =
  inc gN
  gV
proc nextI(): int =
  inc gN
  0
proc bump(v: var int) = v += 1
proc bumpP(p: ptr int) = p[] += 1
var gR1: ref int
var gO1: RX
var gIdx: int
var gSq: seq[int]
proc gR2Init() = gR1 = gR
proc gO2Init() = gO1 = gO
proc chgR(): int =
  inc gN
  new(gR)
  1
proc chgO(): int =
  inc gN
  new(gO)
  1
proc chgI(): int =
  inc gN
  gIdx = 1
  1
proc chgIv(): int =
  inc gN
  gIdx = 1
  1
proc c37(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gV = VO(x: x)
  var y = 7
  inc(getVar().x)
  if gN == 1 and (gV.x == x + 1): symexTarget("c37_ok")
  if gN != 1 or not (gV.x == x + 1): symexTarget("c37_bad")
proc c38(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gV = VO(x: x)
  var y = 7
  getVar().x += 1
  if gN == 1 and (gV.x == x + 1): symexTarget("c38_ok")
  if gN != 1 or not (gV.x == x + 1): symexTarget("c38_bad")
proc c39(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gV = VO(x: x)
  var y = 7
  swap(getVar().x, y)
  if gN == 1 and (gV.x == 7 and y == x): symexTarget("c39_ok")
  if gN != 1 or not (gV.x == 7 and y == x): symexTarget("c39_bad")
proc c40(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  bump(getR()[])
  if gN == 1 and (gR[] == x + 1): symexTarget("c40_ok")
  if gN != 1 or not (gR[] == x + 1): symexTarget("c40_bad")
proc c41(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x
  var y = 7
  bump(getO().x)
  if gN == 1 and (gO.x == x + 1): symexTarget("c41_ok")
  if gN != 1 or not (gO.x == x + 1): symexTarget("c41_bad")
proc c42(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  bump(getSR()[][0])
  if gN == 1 and (gSR[][0] == x + 1): symexTarget("c42_ok")
  if gN != 1 or not (gSR[][0] == x + 1): symexTarget("c42_bad")
proc c43(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  bumpP(addr getR()[])
  if gN == 1 and (gR[] == x + 1): symexTarget("c43_ok")
  if gN != 1 or not (gR[] == x + 1): symexTarget("c43_bad")
proc c44(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  let f: proc (v: var int) {.nimcall.} = (if x == -5000: nil else: bump); f(getR()[])
  if gN == 1 and (gR[] == x + 1): symexTarget("c44_ok")
  if gN != 1 or not (gR[] == x + 1): symexTarget("c44_bad")
proc c45(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  for v in mitems(getSR()[]): v += 1
  if gN == 1 and (gSR[][0] == x + 1): symexTarget("c45_ok")
  if gN != 1 or not (gSR[][0] == x + 1): symexTarget("c45_bad")

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(c37(x))
  nat(c38(x))
  nat(c39(x))
  nat(c40(x))
  nat(c41(x))
  nat(c42(x))
  nat(c43(x))
  nat(c44(x))
  nat(c45(x))

suite "tsymex_rfc0005_s8cq_twice6":
  test "verdicts against Nim":
    # c37: inc(getVar().x)
    pin(c37, "c37_ok", true, sxUnknown)
    pin(c37, "c37_bad", false, sxUnknown)
    # c38: getVar().x += 1
    pin(c38, "c38_ok", true, sxUnknown)
    pin(c38, "c38_bad", false, sxUnknown)
    # c39: swap(getVar().x, y)
    pin(c39, "c39_ok", true, sxUnknown)
    pin(c39, "c39_bad", false, sxUnknown)
    # c40: bump(getR()[])
    pin(c40, "c40_ok", true, sxSat)
    pin(c40, "c40_bad", false, sxUnsat)
    # c41: bump(getO().x)
    pin(c41, "c41_ok", true, sxUnknown)
    pin(c41, "c41_bad", false, sxUnknown)
    # c42: bump(getSR()[][0])
    pin(c42, "c42_ok", true, sxUnknown)
    pin(c42, "c42_bad", false, sxUnknown)
    # c43: bumpP(addr getR()[])
    pin(c43, "c43_ok", true, sxUnknown)
    pin(c43, "c43_bad", false, sxUnknown)
    # c44: let f: proc (v: var int) {.nimcall.} = (if x == -5000: nil else: bump); f(getR()[])
    pin(c44, "c44_ok", true, sxUnknown)
    pin(c44, "c44_bad", false, sxUnknown)
    # c45: for v in mitems(getSR()[]): v += 1
    pin(c45, "c45_ok", false, sxUnknown)
    pin(c45, "c45_bad", true, sxUnknown)
