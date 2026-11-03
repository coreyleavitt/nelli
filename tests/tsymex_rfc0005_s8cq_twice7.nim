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
proc c46(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  for i, v in mpairs(getSR()[]): v += 1
  if gN == 1 and (gSR[][0] == x + 1): symexTarget("c46_ok")
  if gN != 1 or not (gSR[][0] == x + 1): symexTarget("c46_bad")
proc c47(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gTR); gTR[] = {"a": x}.toTable
  var y = 7
  for k, v in mpairs(getTR()[]): v += 1
  if gN == 1 and (gTR[]["a"] == x + 1): symexTarget("c47_ok")
  if gN != 1 or not (gTR[]["a"] == x + 1): symexTarget("c47_bad")
proc c48(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  (getR()[], y) = (3, 4)
  if gN == 1 and (gR[] == 3): symexTarget("c48_ok")
  if gN != 1 or not (gR[] == 3): symexTarget("c48_bad")
proc c49(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gA2 = [x, 2, 3]
  var y = 7
  swap(gA2[nextI()], y)
  if gN == 1 and (gA2[0] == 7 and y == x): symexTarget("c49_ok")
  if gN != 1 or not (gA2[0] == 7 and y == x): symexTarget("c49_bad")
proc c50(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gA2 = [x, 2, 3]
  var y = 7
  inc(gA2[nextI()])
  if gN == 1 and (gA2[0] == x + 1): symexTarget("c50_ok")
  if gN != 1 or not (gA2[0] == x + 1): symexTarget("c50_bad")
proc c51(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gA2 = [x, 2, 3]
  var y = 7
  gA2[nextI()] += 1
  if gN == 1 and (gA2[0] == x + 1): symexTarget("c51_ok")
  if gN != 1 or not (gA2[0] == x + 1): symexTarget("c51_bad")
proc c52(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOA); gOA.a = [x, 2, 3]
  var y = 7
  getOA().a[0] += 1
  if gN == 1 and (gOA.a[0] == x + 1): symexTarget("c52_ok")
  if gN != 1 or not (gOA.a[0] == x + 1): symexTarget("c52_bad")
proc c53(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOA); gOA.a = [x, 2, 3]
  var y = 7
  inc(getOA().a[0])
  if gN == 1 and (gOA.a[0] == x + 1): symexTarget("c53_ok")
  if gN != 1 or not (gOA.a[0] == x + 1): symexTarget("c53_bad")
proc c54(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOS); gOS.s = @[x, 2]
  var y = 7
  getOS().s[0] += 1
  if gN == 1 and (gOS.s[0] == x + 1): symexTarget("c54_ok")
  if gN != 1 or not (gOS.s[0] == x + 1): symexTarget("c54_bad")

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(c46(x))
  nat(c47(x))
  nat(c48(x))
  nat(c49(x))
  nat(c50(x))
  nat(c51(x))
  nat(c52(x))
  nat(c53(x))
  nat(c54(x))

suite "tsymex_rfc0005_s8cq_twice7":
  test "verdicts against Nim":
    # c46: for i, v in mpairs(getSR()[]): v += 1
    pin(c46, "c46_ok", false, sxUnknown)
    pin(c46, "c46_bad", true, sxUnknown)
    # c47: for k, v in mpairs(getTR()[]): v += 1
    pin(c47, "c47_ok", false, sxUnknown)
    pin(c47, "c47_bad", true, sxUnknown)
    # c48: (getR()[], y) = (3, 4)
    pin(c48, "c48_ok", true, sxSat)
    pin(c48, "c48_bad", false, sxUnsat)
    # c49: swap(gA2[nextI()], y)
    pin(c49, "c49_ok", true, sxUnknown)
    pin(c49, "c49_bad", false, sxUnknown)
    # c50: inc(gA2[nextI()])
    pin(c50, "c50_ok", true, sxUnknown)
    pin(c50, "c50_bad", false, sxUnknown)
    # c51: gA2[nextI()] += 1
    pin(c51, "c51_ok", true, sxUnknown)
    pin(c51, "c51_bad", false, sxUnknown)
    # c52: getOA().a[0] += 1
    pin(c52, "c52_ok", true, sxUnknown)
    pin(c52, "c52_bad", false, sxUnknown)
    # c53: inc(getOA().a[0])
    pin(c53, "c53_ok", true, sxUnknown)
    pin(c53, "c53_bad", false, sxUnknown)
    # c54: getOS().s[0] += 1
    pin(c54, "c54_ok", true, sxUnknown)
    pin(c54, "c54_bad", false, sxUnknown)
