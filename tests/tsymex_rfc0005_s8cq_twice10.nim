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
import std/[tables]
type
  OS = object
    s: seq[int]
    n: int
  OA = object
    a: array[3, int]
  UB = object
    d: seq[int]
var gOS: OS
var gOA: OA
var gs: seq[int]
var gTb: Table[string, int]
var gN: int
var gUB: UB
var gX: int
proc getOS(): var OS = (inc gN; gOS)
proc getS(): var seq[int] = (inc gN; gs)
proc nextI(): int = (inc gN; 0)
proc key(): string = (inc gN; "a")
proc getT(): var Table[string, int] = (inc gN; gTb)
proc `[]`(u: var UB; i: int): var int = (inc gN; u.d[i])
proc byV(a: var int) = inc a
proc byOA(a: var openArray[int]) = a[0] = 9
proc rd(): seq[int] = (inc gN; gs)
iterator twice(a: var seq[int]): var int =
  yield a[0]
  yield a[0]
template rst(x: int) =
  gN = 0
  gs = @[x, 2]
  gOS = OS(s: @[x, 2])
  gOA = OA()
  gX = x
proc q01(x: int) =
  rst(x)
  getOS().s.insert(5, 0)
  if gN == 1 and gOS.s[0] == 5: symexTarget("q01_once") else: symexTarget("q01_ne")
proc q02(x: int) =
  rst(x)
  gOA.a[nextI()] = 3
  if gN == 1 and gOA.a[0] == 3: symexTarget("q02_once") else: symexTarget("q02_ne")
proc q03(x: int) =
  rst(x)
  gUB.d = @[x]
  gUB[nextI()] = 3
  if gN == 2 and gUB.d[0] == 3: symexTarget("q03_once") else: symexTarget("q03_ne")
proc q04(x: int) =
  rst(x)
  gUB.d = @[x]
  inc gUB[0]
  if gN == 1 and gUB.d[0] == x + 1: symexTarget("q04_once") else: symexTarget("q04_ne")
proc q05(x: int) =
  rst(x)
  for v in mitems(getS()): v = 3
  if gN != 0 and gs[0] == 3: symexTarget("q05_w") else: symexTarget("q05_ne")
proc q06(x: int) =
  rst(x)
  var t = 0
  for v in items(rd()): t += v
  if gN == 1 and t == x + 2: symexTarget("q06_once") else: symexTarget("q06_ne")
proc q07(x: int) =
  rst(x)
  var t = 0
  for i, v in pairs(rd()): t += v
  if gN == 1 and t == x + 2: symexTarget("q07_once") else: symexTarget("q07_ne")
proc q08(x: int) =
  rst(x)
  gTb = {"a": x}.toTable
  inc getT()[key()]
  if gN == 2: symexTarget("q08_once") else: symexTarget("q08_ne")
proc q09(x: int) =
  rst(x)
  gTb = {"a": x}.toTable
  gTb[key()] = 3
  if gN == 1: symexTarget("q09_once") else: symexTarget("q09_ne")

for x in [1, 2]:
  nat(q01(x))
  nat(q02(x))
  nat(q03(x))
  nat(q04(x))
  nat(q05(x))
  nat(q06(x))
  nat(q07(x))
  nat(q08(x))
  nat(q09(x))

suite "tsymex_rfc0005_s8cq_twice10":
  test "verdicts against Nim":
    pin(q01, "q01_once", true, sxUnknown)
    pin(q01, "q01_ne", false, sxUnknown)
    pin(q02, "q02_once", true, sxUnknown)
    pin(q02, "q02_ne", false, sxUnknown)
    pin(q03, "q03_once", true, sxUnknown)
    pin(q03, "q03_ne", false, sxUnknown)
    pin(q04, "q04_once", true, sxUnknown)
    pin(q04, "q04_ne", false, sxUnknown)
    pin(q05, "q05_w", true, sxUnknown)
    pin(q05, "q05_ne", false, sxUnknown)
    pin(q06, "q06_once", true, sxSat)
    pin(q06, "q06_ne", false, sxRaised)
    pin(q07, "q07_once", true, sxSat)
    pin(q07, "q07_ne", false, sxRaised)
    pin(q08, "q08_once", true, sxUnknown)
    pin(q08, "q08_ne", false, sxUnknown)
    pin(q09, "q09_once", true, sxUnknown)
    pin(q09, "q09_ne", false, sxUnknown)
