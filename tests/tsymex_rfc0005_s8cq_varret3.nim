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
proc p19(x: int) =   # field of a var-return, assignment
  if x == 50: return
  gV.x = x
  gNn = 0
  getVar().x = 3
  if gNn == 1 and gV.x == 3: symexTarget("p19_once")
  else: symexTarget("p19_ne")
proc p20(x: int) =   # let of a var return
  if x == 50: return
  var s = @[x]
  let r = at(s)
  s[0] = 50
  if r == x: symexTarget("p20_copy")
  else: symexTarget("p20_ne")
proc p21(x: int) =   # table get via var bind
  if x == 50: return
  var t = mk(x)
  t["a"] += 1
  if t["a"] == x + 1: symexTarget("p21_one")
  else: symexTarget("p21_ne")
proc p22(x: int) =   # inc over a mgetOrPut
  if x == 50: return
  var t = mk(x)
  inc mgetOrPut(t, "a", 0)
  if t["a"] == x + 1: symexTarget("p22_one")
  else: symexTarget("p22_ne")

for x in [1, 2]:
  nat(p19(x))
  nat(p20(x))
  nat(p21(x))
  nat(p22(x))

suite "tsymex_rfc0005_s8cq_varret3":
  test "verdicts against Nim":
    pin(p19, "p19_once", true, sxUnknown)
    pin(p19, "p19_ne", false, sxUnknown)
    pin(p20, "p20_copy", true, sxSat)
    pin(p20, "p20_ne", false, sxUnknown)
    pin(p21, "p21_one", true, sxSat)
    pin(p21, "p21_ne", false, sxRaised)
    pin(p22, "p22_one", true, sxSat)
    pin(p22, "p22_ne", false, sxRaised)
