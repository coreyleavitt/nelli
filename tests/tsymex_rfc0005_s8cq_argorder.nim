## RFC-0005 slice S8cq -- the order a call's arguments are read in.
##
## Nim's C backend reads an argument where it stands, into a temporary, when a
## symbol it names is the root of a location a LATER argument may write (under
## `addr`, a `var` actual, a mutating magic): `ccgcalls.genParams` /
## `withTmpIfNeeded` (Nim 2.2.10; ARC, atomic ARC and ORC; a type under 1024
## bytes; never an `openArray` formal). Any other argument is read in the call
## expression, after every later argument's call, which is hoisted to a
## statement on both backends. So `bxK(r.x, bxSetInt(r.x))` reads `r.x` as 1,
## where S8cq's walk read 10: a false `sxUnsat` on `field_e` and a false
## `sxSat` on `field_l`. The walk follows that rule (`nimArgTemps`), and
## declines (`feEvalOrderUnmodelled`) where the backend's choice rests on what
## the typed AST does not show: two captured variables (one environment after
## lambda lifting), a temporary of a type whose bits are not its value (a ref
## a later argument may free, a seq sharing its payload), a `var` actual whose
## cell a later argument may move.
##
## Each pin has three columns: Nim (the input loop below, on the backend this
## suite is compiled for), the walk, and main at 6cbfe8f (recorded, not run:
## `main` names what that tree answered, for the record of what moved). Every
## native column was also run on c and cpp, the same on both.
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
             want, main: SymexStatusKind; declines: bool) =
  ## Nim's answer, then the walk's: neither may contradict the other.
  block:
    let r = symexFind(fn, tLabel(lbl))
    var parts: seq[string]
    var order = false
    for e in r.errors:
      parts.add $e.kind
      if e.kind == feEvalOrderUnmodelled: order = true
    checkpoint lbl & " walk=" & $r.status & " main=" & $main & " [" &
               parts.join(", ") & "]"
    check (lbl in natHits) == nativeHit
    check r.status == want
    check order == declines
    check not (nativeHit and r.status == sxUnsat)
    check not (not nativeHit and r.status == sxSat)

type
  BxR = object
    x: int
  BxN = object
    i: BxR
  BxBig = object
    a: array[200, int]
  BxSm = object
    a: array[4, int]

proc bxK(a, b: int): int = a * 100 + b
proc bxSetInt(x: var int): int = (x = 10; 0)
proc bxNoW(x: var int): int = x - x
proc bxSetPtr(p: ptr int): int = (p[] = 10; 0)
proc bxSetIdx(i: var int): int = (i = 1; 0)
proc bxId(a: int): int = a
proc bxVK(a: var int; b: int): int = a * 100 + b
proc bxNewP(p: var ref BxR): int = (p = BxR.new; p.x = 10; 0)
proc bxBigK(a: BxBig; b: int): int = a.a[0] * 100 + b
proc bxBigSet(a: var BxBig): int = (a.a[0] = 10; 0)
proc bxSmK(a: BxSm; b: int): int = a.a[0] * 100 + b
proc bxSmSet(a: var BxSm): int = (a.a[0] = 10; 0)
var gx: int
proc bxSetG(): int = (gx = 10; 0)

proc fField(v: int) =
  symexAssume(v > -100 and v < 100)
  var r = BxR(x: v)
  let t = bxK(r.x, bxSetInt(r.x))
  if v == 1 and t == 100: symexTarget("field_e")
  if v == 1 and t == 1000: symexTarget("field_l")
proc fLocal(v: int) =
  symexAssume(v > -100 and v < 100)
  var x = v
  let t = bxK(x, bxSetInt(x))
  if v == 1 and t == 100: symexTarget("local_e")
  if v == 1 and t == 1000: symexTarget("local_l")
proc fElem(v: int) =
  symexAssume(v > -100 and v < 100)
  var a = [v, v, v]
  var i = 1
  let t = bxK(a[i], bxSetInt(a[i]))
  if v == 1 and t == 100: symexTarget("elem_e")
  if v == 1 and t == 1000: symexTarget("elem_l")
proc fIdx(v: int) =
  symexAssume(v > -100 and v < 100)
  var a = [v, 7, 9]
  var i = 0
  let t = bxK(a[i], bxSetIdx(i))
  if v == 1 and t == 100: symexTarget("idx_e")
  if v == 1 and t == 700: symexTarget("idx_l")
proc fDeref(v: int) =
  symexAssume(v > -100 and v < 100)
  var p = new int
  p[] = v
  let t = bxK(p[], bxSetInt(p[]))
  if v == 1 and t == 100: symexTarget("deref_e")
  if v == 1 and t == 1000: symexTarget("deref_l")
proc fDerefQ(v: int) =
  symexAssume(v > -100 and v < 100)
  var p = new int
  p[] = v
  let q = p
  let t = bxK(p[], bxSetInt(q[]))
  if v == 1 and t == 100: symexTarget("derefq_e")
  if v == 1 and t == 1000: symexTarget("derefq_l")
proc fNested(v: int) =
  symexAssume(v > -100 and v < 100)
  var n = BxN(i: BxR(x: v))
  let t = bxK(n.i.x, bxSetInt(n.i.x))
  if v == 1 and t == 100: symexTarget("nested_e")
  if v == 1 and t == 1000: symexTarget("nested_l")
proc fLater(v: int) =
  symexAssume(v > -100 and v < 100)
  var r = BxR(x: v)
  let t = bxK(bxSetInt(r.x), r.x)
  if v == 1 and t == 1: symexTarget("later_e")
  if v == 1 and t == 10: symexTarget("later_l")
proc fClos(v: int) =
  symexAssume(v > -100 and v < 100)
  var off = 0
  var f = proc (a, b: int): int = a * 100 + b + off
  var r = BxR(x: v)
  let t = f(r.x, bxSetInt(r.x))
  if v == 1 and t == 100: symexTarget("clos_e")
  if v == 1 and t == 1000: symexTarget("clos_l")
proc fClosLater(v: int) =
  symexAssume(v > -100 and v < 100)
  var off = 0
  var f = proc (a, b: int): int = a * 100 + b + off
  var r = BxR(x: v)
  let t = f(bxSetInt(r.x), r.x)
  if v == 1 and t == 1: symexTarget("closlater_e")
  if v == 1 and t == 10: symexTarget("closlater_l")
proc fNoW(v: int) =
  symexAssume(v > -100 and v < 100)
  var r = BxR(x: v)
  let t = bxK(r.x, bxNoW(r.x))
  if v == 1 and t == 100: symexTarget("now_e")
  if v == 1 and t != 100: symexTarget("now_l")
proc fAddr(v: int) =
  symexAssume(v > -100 and v < 100)
  var r = BxR(x: v)
  let t = bxK(r.x, bxSetPtr(addr r.x))
  if v == 1 and t == 100: symexTarget("addr_e")
  if v == 1 and t == 1000: symexTarget("addr_l")
proc fGlob(v: int) =
  symexAssume(v > -100 and v < 100)
  gx = v
  let t = bxK(gx, bxSetG())
  if v == 1 and t == 100: symexTarget("glob_e")
  if v == 1 and t == 1000: symexTarget("glob_l")
proc fCallArg(v: int) =
  symexAssume(v > -100 and v < 100)
  var r = BxR(x: v)
  let t = bxK(bxId(r.x), bxSetInt(r.x))
  if v == 1 and t == 100: symexTarget("callarg_e")
  if v == 1 and t == 1000: symexTarget("callarg_l")
proc fVarAddr(v: int) =
  symexAssume(v > -100 and v < 100)
  var p = BxR.new
  p.x = v
  let t = bxVK(p.x, bxNewP(p))
  if v == 1 and t == 100: symexTarget("varaddr_e")
  if v == 1 and t == 1000: symexTarget("varaddr_l")
proc fBig(v: int) =
  symexAssume(v > -100 and v < 100)
  var b: BxBig
  b.a[0] = v
  let t = bxBigK(b, bxBigSet(b))
  if v == 1 and t == 100: symexTarget("big_e")
  if v == 1 and t == 1000: symexTarget("big_l")
proc fSm(v: int) =
  symexAssume(v > -100 and v < 100)
  var b: BxSm
  b.a[0] = v
  let t = bxSmK(b, bxSmSet(b))
  if v == 1 and t == 100: symexTarget("sm_e")
  if v == 1 and t == 1000: symexTarget("sm_l")

proc bxRK(p: ref BxR; b: int): int = p.x * 100 + b
proc bxSqK(s: seq[int]; b: int): int = s[0] * 100 + b
proc bxSqSet(s: var seq[int]): int = (s[0] = 10; 0)
proc bxSkK(a: int; s: sink seq[int]): int = a * 100 + s.len
proc fLift(v: int) =
  symexAssume(v > -100 and v < 100)
  var p = new int
  p[] = v
  var q = p
  let c = proc (): int = p[] + q[]
  let t = bxK(p[], bxSetInt(q[]))
  if v == 1 and t == 100 and c() > -1000: symexTarget("lift_e")
  if v == 1 and t == 1000: symexTarget("lift_l")
proc fRefArg(v: int) =
  symexAssume(v > -100 and v < 100)
  var p = BxR.new
  p.x = v
  let keep = p
  let t = bxRK(p, bxNewP(p))
  if v == 1 and t == 100 and keep.x == v: symexTarget("refarg_e")
  if v == 1 and t == 1000: symexTarget("refarg_l")
proc fSeqArg(v: int) =
  symexAssume(v > -100 and v < 100)
  var s = @[v, 2]
  let t = bxSqK(s, bxSqSet(s))
  if v == 1 and t == 100: symexTarget("seqarg_e")
  if v == 1 and t == 1000: symexTarget("seqarg_l")
proc fVarField(v: int) =
  symexAssume(v > -100 and v < 100)
  var r = BxR(x: v)
  let t = bxVK(r.x, bxSetInt(r.x))
  if v == 1 and t == 100: symexTarget("varfield_e")
  if v == 1 and t == 1000: symexTarget("varfield_l")
proc fSink(v: int) =
  symexAssume(v > -100 and v < 100)
  var s = @[v, 2]
  let t = bxSkK(s[0], s)
  if v == 1 and t == 102: symexTarget("sink_e")
  if v == 1 and t != 102: symexTarget("sink_l")

for v in [-3, 0, 1, 2, 5]:
  nat(fField(v)); nat(fLocal(v)); nat(fElem(v)); nat(fIdx(v))
  nat(fDeref(v)); nat(fDerefQ(v)); nat(fNested(v)); nat(fLater(v))
  nat(fClos(v)); nat(fClosLater(v)); nat(fNoW(v)); nat(fAddr(v))
  nat(fGlob(v)); nat(fCallArg(v)); nat(fVarAddr(v)); nat(fBig(v)); nat(fSm(v))
  nat(fLift(v)); nat(fRefArg(v)); nat(fSeqArg(v)); nat(fVarField(v)); nat(fSink(v))

suite "tsymex_rfc0005_s8cq_argorder":
  test "walker version floor":
    check parseInt(symexWalkerVersion) >= 263

  test "argument order against Nim":
    # a field `r.x`
    pin(fField, "field_e", true, sxSat, sxSat, false)
    pin(fField, "field_l", false, sxUnsat, sxUnsat, false)
    # a plain local
    pin(fLocal, "local_e", true, sxSat, sxUnsat, false)
    pin(fLocal, "local_l", false, sxUnsat, sxSat, false)
    # an array element `a[i]`
    pin(fElem, "elem_e", true, sxSat, sxSat, false)
    pin(fElem, "elem_l", false, sxUnsat, sxUnsat, false)
    # an element whose index a later argument writes
    pin(fIdx, "idx_e", true, sxSat, sxSat, false)
    pin(fIdx, "idx_l", false, sxUnsat, sxUnsat, false)
    # a deref `p[]`
    pin(fDeref, "deref_e", true, sxSat, sxSat, false)
    pin(fDeref, "deref_l", false, sxUnsat, sxUnsat, false)
    # a deref through another name (`q[]`, `q == p`)
    pin(fDerefQ, "derefq_e", false, sxUnsat, sxSat, false)
    pin(fDerefQ, "derefq_l", true, sxSat, sxUnsat, false)
    # a nested field `n.i.x`
    pin(fNested, "nested_e", true, sxSat, sxSat, false)
    pin(fNested, "nested_l", false, sxUnsat, sxUnsat, false)
    # the alias in a later argument
    pin(fLater, "later_e", false, sxUnsat, sxSat, false)
    pin(fLater, "later_l", true, sxSat, sxUnsat, false)
    # through a closure call
    pin(fClos, "clos_e", true, sxSat, sxSat, false)
    pin(fClos, "clos_l", false, sxUnsat, sxUnsat, false)
    # a closure call, alias in a later argument
    pin(fClosLater, "closlater_e", false, sxUnsat, sxSat, false)
    pin(fClosLater, "closlater_l", true, sxSat, sxUnsat, false)
    # a `var` argument that is not written
    pin(fNoW, "now_e", true, sxSat, sxSat, false)
    pin(fNoW, "now_l", false, sxUnsat, sxUnsat, false)
    # `addr r.x` in a later argument
    pin(fAddr, "addr_e", true, sxSat, sxUnknown, false)
    pin(fAddr, "addr_l", false, sxUnsat, sxUnknown, false)
    # a global the later callee writes by name
    pin(fGlob, "glob_e", false, sxUnsat, sxSat, false)
    pin(fGlob, "glob_l", true, sxSat, sxUnsat, false)
    # an earlier argument that is a call
    pin(fCallArg, "callarg_e", true, sxSat, sxSat, false)
    pin(fCallArg, "callarg_l", false, sxUnsat, sxUnsat, false)
    # a `var` actual whose ref a later argument replaces
    pin(fVarAddr, "varaddr_e", true, sxUnknown, sxUnknown, true)
    pin(fVarAddr, "varaddr_l", false, sxUnknown, sxUnknown, true)
    # a `var` actual on a field path
    pin(fVarField, "varfield_e", false, sxUnsat, sxSat, false)
    pin(fVarField, "varfield_l", true, sxSat, sxUnsat, false)
    # a by-value object of 1600 bytes
    pin(fBig, "big_e", false, sxUnsat, sxUnknown, false)
    pin(fBig, "big_l", true, sxSat, sxUnknown, false)
    # a by-value object of 32 bytes
    pin(fSm, "sm_e", true, sxSat, sxUnknown, false)
    pin(fSm, "sm_l", false, sxUnsat, sxUnknown, false)
    # two captured variables (one environment)
    pin(fLift, "lift_e", true, sxUnknown, sxSat, true)
    pin(fLift, "lift_l", false, sxUnknown, sxUnsat, true)
    # a ref a later argument replaces
    pin(fRefArg, "refarg_e", true, sxUnknown, sxUnknown, true)
    pin(fRefArg, "refarg_l", false, sxUnknown, sxUnknown, true)
    # a seq a later argument writes
    pin(fSeqArg, "seqarg_e", false, sxUnknown, sxUnsat, true)
    pin(fSeqArg, "seqarg_l", true, sxUnknown, sxSat, true)
    # beside a later `sink` formal
    pin(fSink, "sink_e", true, sxSat, sxSat, false)
    pin(fSink, "sink_l", false, sxUnsat, sxUnsat, false)
