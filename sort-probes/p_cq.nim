## S8cq items 1, 2, 3 (direct-call by-value sharing, var-returning actual, a call evaluated twice)
import std/tables
import h
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

proc sDirect(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  gs = s0
  let r = gWrite(gs)
  if r == 50: symexTarget("dg_r50")
  if r == x: symexTarget("dg_rx")
proc sSm(x: int) =
  if x == 50: return
  gSm = Sm(a: x)
  let r = gWriteSm(gSm)
  if r == 50: symexTarget("sm_r50")
  if r == x: symexTarget("sm_rx")
proc sBig(x: int) =
  if x == 50: return
  gBig.a[0] = x
  let r = gWriteBig(gBig)
  if r == 50: symexTarget("bg_r50")
  if r == x: symexTarget("bg_rx")
proc sInner(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  var s = s0
  proc inner(a: seq[int]): int =
    s[0] = 50
    a[0]
  let r = inner(s)
  if r == 50: symexTarget("in_r50")
  if r == x: symexTarget("in_rx")
proc sOuter(s0: seq[int]) =
  if s0.len != 1: return
  let x = s0[0]
  if x == 50: return
  gs = s0
  let r = outerR(gs)
  if r == 50: symexTarget("ou_r50")
  if r == x: symexTarget("ou_rx")

# item 2
proc rab(v: var int; t: Table[string, int]; k: string): int =
  v += 1
  t[k]
proc sVc(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return
  var t = t0
  let r = rab(t["a"], t, "a")
  if r == x + 1: symexTarget("vc_rx1")
  if r == x: symexTarget("vc_rx")

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
  nat(sDirect(@[x])); nat(sSm(x)); nat(sBig(x)); nat(sInner(@[x])); nat(sOuter(@[x]))
  nat(sVc({"a": x}.toTable)); nat(sInc(x)); nat(sSwap(x)); nat(sDec(x)); nat(sPlus(x)); nat(sAsg(x))
  nat(sAdd(x)); nat(sSetLen(x)); nat(sDel(x))
natDump()
v(sDirect, "dg_r50")
v(sDirect, "dg_rx")
v(sSm, "sm_r50")
v(sSm, "sm_rx")
v(sBig, "bg_r50")
v(sBig, "bg_rx")
v(sInner, "in_r50")
v(sInner, "in_rx")
v(sOuter, "ou_r50")
v(sOuter, "ou_rx")
v(sVc, "vc_rx1")
v(sVc, "vc_rx")
v(sInc, "ir_once")
v(sInc, "ir_twice")
v(sSwap, "sr_once")
v(sSwap, "sr_twice")
v(sDec, "dr_once")
v(sDec, "dr_twice")
v(sPlus, "pe_once")
v(sPlus, "pe_twice")
v(sAsg, "as_once")
v(sAsg, "as_twice")
v(sAdd, "ad_once")
v(sAdd, "ad_twice")
v(sSetLen, "sl_once")
v(sSetLen, "sl_twice")
v(sDel, "de_once")
v(sDel, "de_twice")
