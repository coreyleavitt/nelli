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
proc c55(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOS); gOS.s = @[x, 2]
  var y = 7
  inc(getOS().s[0])
  if gN == 1 and (gOS.s[0] == x + 1): symexTarget("c55_ok")
  if gN != 1 or not (gOS.s[0] == x + 1): symexTarget("c55_bad")
proc c56(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOS); gOS.s = @[x, 2]
  var y = 7
  getOS().s.del(0)
  if gN == 1 and (gOS.s.len == 1): symexTarget("c56_ok")
  if gN != 1 or not (gOS.s.len == 1): symexTarget("c56_bad")
proc c57(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x; gR2Init()
  var y = 7
  gR[] += chgR()
  if gN == 1 and (gR1[] == x + 1): symexTarget("c57_ok")
  if gN != 1 or not (gR1[] == x + 1): symexTarget("c57_bad")
proc c58(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x; gR2Init()
  var y = 7
  inc(gR[], chgR())
  if gN == 1 and (gR1[] == x + 1): symexTarget("c58_ok")
  if gN != 1 or not (gR1[] == x + 1): symexTarget("c58_bad")
proc c59(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x; gO2Init()
  var y = 7
  gO.x += chgO()
  if gN == 1 and (gO1.x == x + 1): symexTarget("c59_ok")
  if gN != 1 or not (gO1.x == x + 1): symexTarget("c59_bad")
proc c60(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x; gO2Init()
  var y = 7
  inc(gO.x, chgO())
  if gN == 1 and (gO1.x == x + 1): symexTarget("c60_ok")
  if gN != 1 or not (gO1.x == x + 1): symexTarget("c60_bad")
proc c61(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gIdx = 0; gA2 = [x, 2, 3]
  var y = 7
  gA2[gIdx] += chgI()
  if gN == 1 and (gA2[0] == x + 1): symexTarget("c61_ok")
  if gN != 1 or not (gA2[0] == x + 1): symexTarget("c61_bad")
proc c62(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gIdx = 0; gA2 = [x, 2, 3]
  var y = 7
  inc(gA2[gIdx], chgI())
  if gN == 1 and (gA2[0] == x + 1): symexTarget("c62_ok")
  if gN != 1 or not (gA2[0] == x + 1): symexTarget("c62_bad")
proc c63(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  gIdx = 0; gSq = @[x, 2, 3]
  var y = 7
  gSq[gIdx] += chgI()
  if gN == 1 and (gSq[0] == x + 1): symexTarget("c63_ok")
  if gN != 1 or not (gSq[0] == x + 1): symexTarget("c63_bad")

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(c55(x))
  nat(c56(x))
  nat(c57(x))
  nat(c58(x))
  nat(c59(x))
  nat(c60(x))
  nat(c61(x))
  nat(c62(x))
  nat(c63(x))

suite "tsymex_rfc0005_s8cq_twice8":
  test "verdicts against Nim":
    # c55: inc(getOS().s[0])
    pin(c55, "c55_ok", true, sxUnknown)
    pin(c55, "c55_bad", false, sxUnknown)
    # c56: getOS().s.del(0)
    pin(c56, "c56_ok", true, sxUnknown)
    pin(c56, "c56_bad", false, sxUnknown)
    # c57: gR[] += chgR()
    pin(c57, "c57_ok", false, sxUnsat)
    pin(c57, "c57_bad", true, sxSat)
    # c58: inc(gR[], chgR())
    pin(c58, "c58_ok", false, sxUnsat)
    pin(c58, "c58_bad", true, sxSat)
    # c59: gO.x += chgO()
    pin(c59, "c59_ok", false, sxUnknown)
    pin(c59, "c59_bad", true, sxUnknown)
    # c60: inc(gO.x, chgO())
    pin(c60, "c60_ok", false, sxUnsat)
    pin(c60, "c60_bad", true, sxSat)
    # c61: gA2[gIdx] += chgI()
    pin(c61, "c61_ok", false, sxUnsat)
    pin(c61, "c61_bad", true, sxSat)
    # c62: inc(gA2[gIdx], chgI())
    pin(c62, "c62_ok", false, sxUnsat)
    pin(c62, "c62_bad", true, sxSat)
    # c63: gSq[gIdx] += chgI()
    pin(c63, "c63_ok", false, sxUnsat)
    pin(c63, "c63_bad", true, sxSat)
