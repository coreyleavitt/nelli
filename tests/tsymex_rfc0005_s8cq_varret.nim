## RFC-0005 slice S8cq, item 2 -- a call returning `var T` as an actual.
##
## `rab(t["a"], t, "a")`'s callee writes the location through both actuals, and a
## temporary in the walk does not see it. Every form that stays exact is pinned
## against Nim, and every other form declines; the list is in the RFC.
import std/[unittest, strutils, sets]
import nelli
import nelli/symex
import ./s8cu_helpers except show

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
proc p01(x: int) =   # table bracket, peer
  if x == 50: return
  var t = mk(x)
  let r = rab(t["a"], t, "a")
  if r == 50: symexTarget("p01_r50")
  if r == x: symexTarget("p01_rx")
proc p02(x: int) =   # mgetOrPut actual, peer
  if x == 50: return
  var t = mk(x)
  let r = rab(mgetOrPut(t, "a", 0), t, "a")
  if r == 50: symexTarget("p02_r50")
  if r == x: symexTarget("p02_rx")
proc p03(x: int) =   # var-return of a user routine, field
  if x == 50: return
  gV.x = x
  let r = glob(getVar().x)
  if r == x: symexTarget("p03_rx")
  else: symexTarget("p03_ne")
proc p04(x: int) =   # table bracket alone
  if x == 50: return
  var t = mk(x)
  bump(t["a"])
  if t["a"] == x + 1: symexTarget("p04_one")
  else: symexTarget("p04_ne")
proc p05(x: int) =   # var-return under assignment
  if x == 50: return
  var s = @[x]
  gNn = 0
  at(s) = 3
  if gNn == 1 and s[0] == 3: symexTarget("p05_once")
  else: symexTarget("p05_ne")
proc p06(x: int) =
  if x == 50: return
  var s = @[x]
  gNn = 0
  inc at(s)
  if gNn == 1: symexTarget("p06_once")
  else: symexTarget("p06_ne")
proc p07(x: int) =
  if x == 50: return
  var s = @[x]
  gNn = 0
  at(s) += 2
  if gNn == 1: symexTarget("p07_once")
  else: symexTarget("p07_ne")
proc p08(x: int) =
  if x == 50: return
  var s = @[x]
  gNn = 0
  bump(at(s))
  if gNn == 1 and s[0] == x + 1: symexTarget("p08_once")
  else: symexTarget("p08_ne")
proc p09(x: int) =
  if x == 50: return
  var s = @[x]
  gy = 7
  gNn = 0
  swap(at(s), gy)
  if gNn == 1 and s[0] == 7 and gy == x: symexTarget("p09_once")
  else: symexTarget("p09_ne")

for x in [1, 2]:
  nat(p01(x))
  nat(p02(x))
  nat(p03(x))
  nat(p04(x))
  nat(p05(x))
  nat(p06(x))
  nat(p07(x))
  nat(p08(x))
  nat(p09(x))

suite "tsymex_rfc0005_s8cq_varret":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 252

  test "verdicts against Nim":
    pin(p01, "p01_r50", true, sxUnknown)
    pin(p01, "p01_rx", false, sxUnknown)
    pin(p02, "p02_r50", true, sxUnknown)
    pin(p02, "p02_rx", false, sxUnknown)
    pin(p03, "p03_rx", true, sxUnknown)
    pin(p03, "p03_ne", false, sxUnknown)
    pin(p04, "p04_one", true, sxUnknown)
    pin(p04, "p04_ne", false, sxUnknown)
    pin(p05, "p05_once", true, sxUnknown)
    pin(p05, "p05_ne", false, sxUnknown)
    pin(p06, "p06_once", true, sxUnknown)
    pin(p06, "p06_ne", false, sxUnknown)
    pin(p07, "p07_once", true, sxUnknown)
    pin(p07, "p07_ne", false, sxUnknown)
    pin(p08, "p08_once", true, sxUnknown)
    pin(p08, "p08_ne", false, sxUnknown)
    pin(p09, "p09_once", true, sxUnknown)
    pin(p09, "p09_ne", false, sxUnknown)

  test "the native-hit side of each shape is a K9 decline pin":
    # RFC-0016 SND-01: a var-returning actual is never decided (exact model:
    # PRC-36); each shape's native-hit label is declined, not refuted.
    let k = cellKey(faCallShape, "varReturnActual")
    pinDecline(p01, k, feUnsupportedOp, tLabel("p01_r50"))
    pinDecline(p02, k, feUnsupportedOp, tLabel("p02_r50"))
    pinDecline(p03, k, feUnsupportedOp, tLabel("p03_rx"))
    pinDecline(p04, k, feUnsupportedOp, tLabel("p04_one"))
    pinDecline(p05, k, feUnsupportedStmtKind, tLabel("p05_once"))
    pinDecline(p06, k, feUnsupportedOp, tLabel("p06_once"))
    pinDecline(p07, k, feUnsupportedOp, tLabel("p07_once"))
    pinDecline(p08, k, feUnsupportedOp, tLabel("p08_once"))
    pinDecline(p09, k, feUnsupportedOp, tLabel("p09_once"))
