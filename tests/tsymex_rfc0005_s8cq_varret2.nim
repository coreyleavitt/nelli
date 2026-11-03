## RFC-0005 slice S8cq, item 2 -- a call returning `var T` as an actual.
##
## `rab(t["a"], t, "a")`'s callee writes the location through both actuals, and a
## temporary in the walk does not see it. Every form that stays exact is pinned
## against Nim, and every other form declines; the list is in the RFC.
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
import std/[tables]
type
  V = object
    x: int
var gTb: Table[string, int]
var gV: V
var gq: seq[int]
var gy: int
var gNn: int
proc at(s: var seq[int]): var int = (inc gNn; s[0])
proc getVar(): var V = (inc gNn; gV)
proc rab(a: var int; t: var Table[string, int]; k: string): int =
  t[k] = 50
  a
proc rs(a: var int; s: var seq[int]): int =
  s[0] = 50
  a
proc bump(a: var int) = inc a
proc rval(a: int; t: var Table[string, int]): int =
  t["a"] = 50
  a
proc g1(a: var int; t: var Table[string, int]): int =
  t["a"] = 50
  a
proc g2(a: var int; t: var Table[string, int]): int = g1(a, t)
proc glob(a: var int): int =
  gTb["a"] = 50
  a
proc globS(a: var int): int =
  gq[0] = 50
  a
method m(b: ref RootObj; a: var int; t: var Table[string, int]): int {.base.} =
  t["a"] = 50
  a
proc gen[T](a: var T; t: var Table[string, T]): T =
  t["a"] = 50
  a
proc mk(x: int): Table[string, int] =
  result["a"] = x
proc p10(x: int) =   # addr of a table bracket
  if x == 50: return
  var t = mk(x)
  let p = addr t["a"]
  t["a"] = 50
  if p[] == 50: symexTarget("p10_w")
  else: symexTarget("p10_n")
proc p11(x: int) =   # var formal chain
  if x == 50: return
  var t = mk(x)
  let r = g2(t["a"], t)
  if r == 50: symexTarget("p11_r50")
  if r == x: symexTarget("p11_rx")
proc p12(x: int) =   # method
  if x == 50: return
  var t = mk(x)
  let b = new(RootObj)
  let r = m(b, t["a"], t)
  if r == 50: symexTarget("p12_r50")
  if r == x: symexTarget("p12_rx")
proc p13(x: int) =   # generic
  if x == 50: return
  var t = mk(x)
  let r = gen(t["a"], t)
  if r == 50: symexTarget("p13_r50")
  if r == x: symexTarget("p13_rx")
proc p14(x: int) =   # var-return actual, the seq peer
  if x == 50: return
  var s = @[x]
  let r = rs(at(s), s)
  if r == 50: symexTarget("p14_r50")
  if r == x: symexTarget("p14_rx")
proc p15(x: int) =   # global Table reached by name
  if x == 50: return
  gTb = mk(x)
  let r = glob(gTb["a"])
  if r == 50: symexTarget("p15_r50")
  if r == x: symexTarget("p15_rx")
proc p16(x: int) =   # var return through the global seq
  if x == 50: return
  gq = @[x]
  let r = globS(at(gq))
  if r == 50: symexTarget("p16_r50")
  if r == x: symexTarget("p16_rx")
proc p17(x: int) =   # mgetOrPut with a by-value actual
  if x == 50: return
  var t = mk(x)
  let r = rval(mgetOrPut(t, "a", 0), t)
  if r == 50: symexTarget("p17_r50")
  if r == x: symexTarget("p17_rx")
proc p18(x: int) =   # table bracket inside mpairs
  if x == 50: return
  var t = mk(x)
  var r = 0
  for k, v in t.mpairs:
    r = rab(t[k], t, k)
  if r == 50: symexTarget("p18_r50")
  if r == x: symexTarget("p18_rx")

for x in [1, 2]:
  nat(p10(x))
  nat(p11(x))
  nat(p12(x))
  nat(p13(x))
  nat(p14(x))
  nat(p15(x))
  nat(p16(x))
  nat(p17(x))
  nat(p18(x))

suite "tsymex_rfc0005_s8cq_varret2":
  test "verdicts against Nim":
    pin(p10, "p10_w", true, sxUnknown)
    pin(p10, "p10_n", false, sxUnknown)
    pin(p11, "p11_r50", true, sxUnknown)
    pin(p11, "p11_rx", false, sxUnknown)
    pin(p12, "p12_r50", true, sxUnknown)
    pin(p12, "p12_rx", false, sxUnknown)
    pin(p13, "p13_r50", true, sxUnknown)
    pin(p13, "p13_rx", false, sxUnknown)
    pin(p14, "p14_r50", true, sxUnknown)
    pin(p14, "p14_rx", false, sxUnknown)
    pin(p15, "p15_r50", true, sxUnknown)
    pin(p15, "p15_rx", false, sxUnknown)
    pin(p16, "p16_r50", true, sxUnknown)
    pin(p16, "p16_rx", false, sxUnknown)
    pin(p17, "p17_r50", false, sxUnsat)
    pin(p17, "p17_rx", true, sxSat)
    pin(p18, "p18_r50", true, sxUnknown)
    pin(p18, "p18_rx", false, sxUnknown)
