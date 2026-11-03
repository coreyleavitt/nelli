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
proc q19(x: int) =
  rst(x)
  getS().del(nextI())
  if gN == 2 and gs.len == 1: symexTarget("q19_two") else: symexTarget("q19_ne")
proc q20(x: int) =
  rst(x)
  getS().add(nextI())
  if gN == 2 and gs.len == 3: symexTarget("q20_two") else: symexTarget("q20_ne")
proc q21(x: int) =
  rst(x)
  getOS().s[nextI()] += 1
  if gN == 2: symexTarget("q21_two") else: symexTarget("q21_ne")
proc q22(x: int) =
  rst(x)
  var s2 = @[x]
  discard s2.pop()
  discard getS().pop()
  if gN == 1 and gs.len == 1: symexTarget("q22_once") else: symexTarget("q22_ne")

for x in [1, 2]:
  nat(q19(x))
  nat(q20(x))
  nat(q21(x))
  nat(q22(x))

suite "tsymex_rfc0005_s8cq_twice12":
  test "verdicts against Nim":
    pin(q19, "q19_two", true, sxUnknown)
    pin(q19, "q19_ne", false, sxUnknown)
    pin(q20, "q20_two", true, sxUnknown)
    pin(q20, "q20_ne", false, sxUnknown)
    pin(q21, "q21_two", true, sxUnknown)
    pin(q21, "q21_ne", false, sxUnknown)
    pin(q22, "q22_once", true, sxUnknown)
    pin(q22, "q22_ne", false, sxUnknown)
