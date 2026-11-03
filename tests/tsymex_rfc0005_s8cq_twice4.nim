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
proc c19(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  wasMoved(getR()[])
  if gN == 1 and (gR[] == 0): symexTarget("c19_ok")
  if gN != 1 or not (gR[] == 0): symexTarget("c19_bad")
proc c20(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  let m = move(getR()[]); (if m != x: gN = 9)
  if gN == 1 and (gR[] == 0 or gR[] == x): symexTarget("c20_ok")
  if gN != 1 or not (gR[] == 0 or gR[] == x): symexTarget("c20_bad")
proc c21(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gRR); new(gRR[]); gRR[][] = x
  var y = 7
  new(getRR()[])
  if gN == 1 and (gRR[][] == 0): symexTarget("c21_ok")
  if gN != 1 or not (gRR[][] == 0): symexTarget("c21_bad")
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

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(c19(x))
  nat(c20(x))
  nat(c21(x))
  nat(c22(x))
  nat(c23(x))
  nat(c24(x))
  nat(c25(x))
  nat(c26(x))
  nat(c27(x))

suite "tsymex_rfc0005_s8cq_twice4":
  test "verdicts against Nim":
    # c19: wasMoved(getR()[])
    pin(c19, "c19_ok", true, sxSat)
    pin(c19, "c19_bad", false, sxUnsat)
    # c20: let m = move(getR()[]); (if m != x: gN = 9)
    pin(c20, "c20_ok", true, sxUnknown)
    pin(c20, "c20_bad", false, sxUnknown)
    # c21: new(getRR()[])
    pin(c21, "c21_ok", false, sxUnknown)
    pin(c21, "c21_bad", true, sxUnknown)
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
