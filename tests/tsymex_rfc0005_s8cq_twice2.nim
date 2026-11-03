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
proc c01(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x
  var y = 7
  inc(getO().x)
  if gN == 1 and (gO.x == x + 1): symexTarget("c01_ok")
  if gN != 1 or not (gO.x == x + 1): symexTarget("c01_bad")
proc c02(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x
  var y = 7
  getO().x += 1
  if gN == 1 and (gO.x == x + 1): symexTarget("c02_ok")
  if gN != 1 or not (gO.x == x + 1): symexTarget("c02_bad")
proc c03(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gO); gO.x = x
  var y = 7
  swap(getO().x, y)
  if gN == 1 and (gO.x == 7 and y == x): symexTarget("c03_ok")
  if gN != 1 or not (gO.x == 7 and y == x): symexTarget("c03_bad")
proc c04(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOS); gOS.s = @[x, 2]
  var y = 7
  getOS().s.add(1)
  if gN == 1 and (gOS.s.len == 3): symexTarget("c04_ok")
  if gN != 1 or not (gOS.s.len == 3): symexTarget("c04_bad")
proc c05(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOS); gOS.s = @[x, 2]
  var y = 7
  getOS().s.setLen(1)
  if gN == 1 and (gOS.s.len == 1): symexTarget("c05_ok")
  if gN != 1 or not (gOS.s.len == 1): symexTarget("c05_bad")
proc c06(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOStr); gOStr.st = "ab"
  var y = 7
  getOStr().st.add('c')
  if gN == 1 and (gOStr.st == "abc"): symexTarget("c06_ok")
  if gN != 1 or not (gOStr.st == "abc"): symexTarget("c06_bad")
proc c07(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gOStr); gOStr.st = "ab"
  var y = 7
  getOStr().st &= "c"
  if gN == 1 and (gOStr.st == "abc"): symexTarget("c07_ok")
  if gN != 1 or not (gOStr.st == "abc"): symexTarget("c07_bad")
proc c08(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  inc(getR()[], 2)
  if gN == 1 and (gR[] == x + 2): symexTarget("c08_ok")
  if gN != 1 or not (gR[] == x + 2): symexTarget("c08_bad")
proc c09(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  getR()[] *= 2
  if gN == 1 and (gR[] == x * 2): symexTarget("c09_ok")
  if gN != 1 or not (gR[] == x * 2): symexTarget("c09_bad")
proc c10(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gStrR); gStrR[] = "ab"
  var y = 7
  getStrR()[] &= "c"
  if gN == 1 and (gStrR[] == "abc"): symexTarget("c10_ok")
  if gN != 1 or not (gStrR[] == "abc"): symexTarget("c10_bad")
proc c11(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gStrR); gStrR[] = "ab"
  var y = 7
  getStrR()[].add('c')
  if gN == 1 and (gStrR[] == "abc"): symexTarget("c11_ok")
  if gN != 1 or not (gStrR[] == "abc"): symexTarget("c11_bad")
proc c12(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gAR); gAR[] = [x, 2, 3]
  var y = 7
  getAR()[][0] += 1
  if gN == 1 and (gAR[][0] == x + 1): symexTarget("c12_ok")
  if gN != 1 or not (gAR[][0] == x + 1): symexTarget("c12_bad")
proc c13(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gAR); gAR[] = [x, 2, 3]
  var y = 7
  inc(getAR()[][0])
  if gN == 1 and (gAR[][0] == x + 1): symexTarget("c13_ok")
  if gN != 1 or not (gAR[][0] == x + 1): symexTarget("c13_bad")
proc c14(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gAR); gAR[] = [x, 2, 3]
  var y = 7
  swap(getAR()[][0], y)
  if gN == 1 and (gAR[][0] == 7 and y == x): symexTarget("c14_ok")
  if gN != 1 or not (gAR[][0] == 7 and y == x): symexTarget("c14_bad")
proc c15(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  getSR()[][0] += 1
  if gN == 1 and (gSR[][0] == x + 1): symexTarget("c15_ok")
  if gN != 1 or not (gSR[][0] == x + 1): symexTarget("c15_bad")
proc c16(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  inc(getSR()[][0])
  if gN == 1 and (gSR[][0] == x + 1): symexTarget("c16_ok")
  if gN != 1 or not (gSR[][0] == x + 1): symexTarget("c16_bad")
proc c17(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gSR); gSR[] = @[x, 2]
  var y = 7
  swap(getSR()[][0], y)
  if gN == 1 and (gSR[][0] == 7 and y == x): symexTarget("c17_ok")
  if gN != 1 or not (gSR[][0] == 7 and y == x): symexTarget("c17_bad")
proc c18(x: int) =
  if x > 1000 or x < -1000: return
  gN = 0
  new(gR); gR[] = x
  var y = 7
  reset(getR()[])
  if gN == 1 and (gR[] == 0): symexTarget("c18_ok")
  if gN != 1 or not (gR[] == 0): symexTarget("c18_bad")
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

for x in [-3, 0, 3, 5, 7, 49, 51]:
  nat(c01(x))
  nat(c02(x))
  nat(c03(x))
  nat(c04(x))
  nat(c05(x))
  nat(c06(x))
  nat(c07(x))
  nat(c08(x))
  nat(c09(x))
  nat(c10(x))
  nat(c11(x))
  nat(c12(x))
  nat(c13(x))
  nat(c14(x))
  nat(c15(x))
  nat(c16(x))
  nat(c17(x))
  nat(c18(x))
  nat(c19(x))
  nat(c20(x))
  nat(c21(x))
  nat(c22(x))

suite "tsymex_rfc0005_s8cq_twice2":
  test "verdicts against Nim":
    # c01: inc(getO().x)
    pin(c01, "c01_ok", true, sxUnknown)
    pin(c01, "c01_bad", false, sxUnknown)
    # c02: getO().x += 1
    pin(c02, "c02_ok", true, sxUnknown)
    pin(c02, "c02_bad", false, sxUnknown)
    # c03: swap(getO().x, y)
    pin(c03, "c03_ok", true, sxUnknown)
    pin(c03, "c03_bad", false, sxUnknown)
    # c04: getOS().s.add(1)
    pin(c04, "c04_ok", true, sxUnknown)
    pin(c04, "c04_bad", false, sxUnknown)
    # c05: getOS().s.setLen(1)
    pin(c05, "c05_ok", true, sxUnknown)
    pin(c05, "c05_bad", false, sxUnknown)
    # c06: getOStr().st.add('c')
    pin(c06, "c06_ok", true, sxUnknown)
    pin(c06, "c06_bad", false, sxUnknown)
    # c07: getOStr().st &= 'c'
    pin(c07, "c07_ok", true, sxUnknown)
    pin(c07, "c07_bad", false, sxUnknown)
    # c08: inc(getR()[], 2)
    pin(c08, "c08_ok", true, sxUnknown)
    pin(c08, "c08_bad", false, sxUnknown)
    # c09: getR()[] *= 2
    pin(c09, "c09_ok", true, sxUnknown)
    pin(c09, "c09_bad", false, sxUnknown)
    # c10: getStrR()[] &= 'c'
    pin(c10, "c10_ok", true, sxUnknown)
    pin(c10, "c10_bad", false, sxUnknown)
    # c11: getStrR()[].add('c')
    pin(c11, "c11_ok", true, sxSat)
    pin(c11, "c11_bad", false, sxUnsat)
    # c12: getAR()[][0] += 1
    pin(c12, "c12_ok", true, sxUnknown)
    pin(c12, "c12_bad", false, sxUnknown)
    # c13: inc(getAR()[][0])
    pin(c13, "c13_ok", true, sxUnknown)
    pin(c13, "c13_bad", false, sxUnknown)
    # c14: swap(getAR()[][0], y)
    pin(c14, "c14_ok", true, sxUnknown)
    pin(c14, "c14_bad", false, sxUnknown)
    # c15: getSR()[][0] += 1
    pin(c15, "c15_ok", true, sxUnknown)
    pin(c15, "c15_bad", false, sxUnknown)
    # c16: inc(getSR()[][0])
    pin(c16, "c16_ok", true, sxUnknown)
    pin(c16, "c16_bad", false, sxUnknown)
    # c17: swap(getSR()[][0], y)
    pin(c17, "c17_ok", true, sxUnknown)
    pin(c17, "c17_bad", false, sxUnknown)
    # c18: reset(getR()[])
    pin(c18, "c18_ok", true, sxSat)
    pin(c18, "c18_bad", false, sxUnsat)
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
