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
proc c22(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gRR); new(gRR[]); gRR[][] = x
  var y = 7
  inc(getRR()[][])
  if gN == 1 and (gRR[][] == x + 1): symexTarget("c22_ok")
  if gN != 1 or not (gRR[][] == x + 1): symexTarget("c22_bad")
proc c23(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  getSR()[].insert(9, 0)
  if gN == 1 and (gSR[].len == 3 and gSR[][0] == 9): symexTarget("c23_ok")
  if gN != 1 or not (gSR[].len == 3 and gSR[][0] == 9): symexTarget("c23_bad")
proc c24(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  let w = getSR()[].pop(); (if w != 2: gN = 9)
  if gN == 1 and (gSR[].len == 1): symexTarget("c24_ok")
  if gN != 1 or not (gSR[].len == 1): symexTarget("c24_bad")
proc c25(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  getSR()[].delete(0)
  if gN == 1 and (gSR[].len == 1 and gSR[][0] == 2): symexTarget("c25_ok")
  if gN != 1 or not (gSR[].len == 1 and gSR[][0] == 2): symexTarget("c25_bad")
proc c26(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gTR); gTR[] = {"a": x}.toTable
  var y = 7
  getTR()[]["a"] = 3
  if gN == 1 and (gTR[]["a"] == 3): symexTarget("c26_ok")
  if gN != 1 or not (gTR[]["a"] == 3): symexTarget("c26_bad")
proc c27(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gTR); gTR[] = {"a": x}.toTable
  var y = 7
  inc(getTR()[]["a"])
  if gN == 1 and (gTR[]["a"] == x + 1): symexTarget("c27_ok")
  if gN != 1 or not (gTR[]["a"] == x + 1): symexTarget("c27_bad")
proc c28(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gTR); gTR[] = {"a": x}.toTable
  var y = 7
  getTR()[].del("a")
  if gN == 1 and ("a" notin gTR[]): symexTarget("c28_ok")
  if gN != 1 or not ("a" notin gTR[]): symexTarget("c28_bad")
proc c29(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSetR); gSetR[] = {'a'}
  var y = 7
  getSetR()[].incl('b')
  if gN == 1 and ('b' in gSetR[]): symexTarget("c29_ok")
  if gN != 1 or not ('b' in gSetR[]): symexTarget("c29_bad")
proc c30(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gTR); gTR[] = {"a": x}.toTable
  var y = 7
  inc(getTR()[].mgetOrPut("a", 0))
  if gN == 1 and (gTR[]["a"] == x + 1): symexTarget("c30_ok")
  if gN != 1 or not (gTR[]["a"] == x + 1): symexTarget("c30_bad")
proc c31(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x; gPs = @[gR]
  var y = 7
  inc(gPs[nextI()][])
  if gN == 1 and (gR[] == x + 1): symexTarget("c31_ok")
  if gN != 1 or not (gR[] == x + 1): symexTarget("c31_bad")
proc c32(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x; gPs = @[gR]
  var y = 7
  gPs[nextI()][] += 1
  if gN == 1 and (gR[] == x + 1): symexTarget("c32_ok")
  if gN != 1 or not (gR[] == x + 1): symexTarget("c32_bad")
proc c33(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x; gOxs = @[gO]
  var y = 7
  inc(gOxs[nextI()].x)
  if gN == 1 and (gO.x == x + 1): symexTarget("c33_ok")
  if gN != 1 or not (gO.x == x + 1): symexTarget("c33_bad")
proc c34(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x; gOxs = @[gO]
  var y = 7
  gOxs[nextI()].x += 1
  if gN == 1 and (gO.x == x + 1): symexTarget("c34_ok")
  if gN != 1 or not (gO.x == x + 1): symexTarget("c34_bad")
proc c35(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x; gOxs = @[gO]
  var y = 7
  swap(gOxs[nextI()].x, y)
  if gN == 1 and (gO.x == 7 and y == x): symexTarget("c35_ok")
  if gN != 1 or not (gO.x == 7 and y == x): symexTarget("c35_bad")
proc c36(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOS); gOS.s = @[x, 2]; gOSeq = @[gOS]
  var y = 7
  gOSeq[nextI()].s.add(1)
  if gN == 1 and (gOS.s.len == 3): symexTarget("c36_ok")
  if gN != 1 or not (gOS.s.len == 3): symexTarget("c36_bad")
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

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(c22(x))
  nat(c23(x))
  nat(c24(x))
  nat(c25(x))
  nat(c26(x))
  nat(c27(x))
  nat(c28(x))
  nat(c29(x))
  nat(c30(x))
  nat(c31(x))
  nat(c32(x))
  nat(c33(x))
  nat(c34(x))
  nat(c35(x))
  nat(c36(x))
  nat(c37(x))
  nat(c38(x))
  nat(c39(x))
  nat(c40(x))
  nat(c41(x))
  nat(c42(x))
  nat(c43(x))

suite "tsymex_rfc0005_s8cq_twice3":
  test "verdicts against Nim":
    # c22: inc(getRR()[][])
    pin(c22, "c22_ok", true, sxUnknown)
    pin(c22, "c22_bad", false, sxUnknown)
    # c23: getSR()[].insert(9, 0)
    pin(c23, "c23_ok", true, sxSat)
    pin(c23, "c23_bad", false, sxUnsat)
    # c24: let w = getSR()[].pop(); (if w != 2: gN = 9)
    pin(c24, "c24_ok", true, sxUnknown)
    pin(c24, "c24_bad", false, sxUnknown)
    # c25: getSR()[].delete(0)
    pin(c25, "c25_ok", true, sxUnknown)
    pin(c25, "c25_bad", false, sxUnknown)
    # c26: getTR()[]['a'] = 3
    pin(c26, "c26_ok", true, sxUnknown)
    pin(c26, "c26_bad", false, sxUnknown)
    # c27: inc(getTR()[]['a'])
    pin(c27, "c27_ok", true, sxUnknown)
    pin(c27, "c27_bad", false, sxUnknown)
    # c28: getTR()[].del('a')
    pin(c28, "c28_ok", true, sxUnknown)
    pin(c28, "c28_bad", false, sxUnknown)
    # c29: getSetR()[].incl('b')
    pin(c29, "c29_ok", true, sxUnknown)
    pin(c29, "c29_bad", false, sxUnknown)
    # c30: inc(getTR()[].mgetOrPut('a', 0))
    pin(c30, "c30_ok", true, sxUnknown)
    pin(c30, "c30_bad", false, sxUnknown)
    # c31: inc(gPs[nextI()][])
    pin(c31, "c31_ok", true, sxUnknown)
    pin(c31, "c31_bad", false, sxUnknown)
    # c32: gPs[nextI()][] += 1
    pin(c32, "c32_ok", true, sxUnknown)
    pin(c32, "c32_bad", false, sxUnknown)
    # c33: inc(gOxs[nextI()].x)
    pin(c33, "c33_ok", true, sxUnknown)
    pin(c33, "c33_bad", false, sxUnknown)
    # c34: gOxs[nextI()].x += 1
    pin(c34, "c34_ok", true, sxUnknown)
    pin(c34, "c34_bad", false, sxUnknown)
    # c35: swap(gOxs[nextI()].x, y)
    pin(c35, "c35_ok", true, sxUnknown)
    pin(c35, "c35_bad", false, sxUnknown)
    # c36: gOSeq[nextI()].s.add(1)
    pin(c36, "c36_ok", true, sxUnknown)
    pin(c36, "c36_bad", false, sxUnknown)
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
