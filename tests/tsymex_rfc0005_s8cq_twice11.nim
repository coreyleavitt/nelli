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
proc q10(x: int) =
  rst(x)
  gTb = {"a": x}.toTable
  discard gTb.mgetOrPut(key(), 0)
  if gN == 1: symexTarget("q10_once") else: symexTarget("q10_ne")
proc q11(x: int) =
  rst(x)
  byV(gs[nextI()])
  if gN == 1 and gs[0] == x + 1: symexTarget("q11_once") else: symexTarget("q11_ne")
proc q12(x: int) =
  rst(x)
  byOA(getS())
  if gN == 1 and gs[0] == 9: symexTarget("q12_once") else: symexTarget("q12_ne")
proc q13(x: int) =
  rst(x)
  gs[nextI()] = gs[nextI()] + 1
  if gN == 2: symexTarget("q13_two") else: symexTarget("q13_ne")
proc q14(x: int) =
  rst(x)
  newSeq(getS(), 2)
  if gN == 1 and gs[0] == 0: symexTarget("q14_once") else: symexTarget("q14_ne")
proc q15(x: int) =
  rst(x)
  gs.setLen(nextI() + 1)
  if gN == 1 and gs.len == 1: symexTarget("q15_once") else: symexTarget("q15_ne")
proc q16(x: int) =
  rst(x)
  getOS().n = 3
  if gN == 1 and gOS.n == 3: symexTarget("q16_once") else: symexTarget("q16_ne")
proc q17(x: int) =
  rst(x)
  getS()[0] = 3
  if gN == 1 and gs[0] == 3: symexTarget("q17_once") else: symexTarget("q17_ne")
proc q18(x: int) =
  rst(x)
  let (a, b) = (getS()[0], getS()[1])
  if gN == 2 and a == x and b == 2: symexTarget("q18_two") else: symexTarget("q18_ne")

for x in [1, 2]:
  nat(q10(x))
  nat(q11(x))
  nat(q12(x))
  nat(q13(x))
  nat(q14(x))
  nat(q15(x))
  nat(q16(x))
  nat(q17(x))
  nat(q18(x))

suite "tsymex_rfc0005_s8cq_twice11":
  test "verdicts against Nim":
    pin(q10, "q10_once", true, sxUnknown)
    pin(q10, "q10_ne", false, sxUnknown)
    pin(q11, "q11_once", true, sxSat)
    pin(q11, "q11_ne", false, sxRaised)
    pin(q12, "q12_once", true, sxUnknown)
    pin(q12, "q12_ne", false, sxUnknown)
    pin(q13, "q13_two", true, sxSat)
    pin(q13, "q13_ne", false, sxRaised)
    pin(q14, "q14_once", true, sxUnknown)
    pin(q14, "q14_ne", false, sxUnknown)
    pin(q15, "q15_once", true, sxSat)
    pin(q15, "q15_ne", false, sxUnsat)
    pin(q16, "q16_once", true, sxUnknown)
    pin(q16, "q16_ne", false, sxUnknown)
    pin(q17, "q17_once", true, sxUnknown)
    pin(q17, "q17_ne", false, sxUnknown)
    pin(q18, "q18_two", true, sxSat)
    pin(q18, "q18_ne", false, sxUnsat)
