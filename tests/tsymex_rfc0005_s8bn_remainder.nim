## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
import std/[unittest, strutils, options]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

template declines(fn: typed, lbl: string, ek: SymexErrorKind,
                  needle: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == ek and needle in e.msg: named = true
    check named

template confirmed(fn: typed, lbl: string): untyped =
  ## A sound `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

# ---- 1-2. ptr alias witnesses ------------------------------------------------
#
# RFC-0005 S8bn items 1 and 2. S8bh aimed a `ptr` of unknown origin at a
# ref object's field, a global or a `var` parameter, and the `sxSat` was
# sound; but its witness replayed only when the field's object was built
# before the pointer (parameter order), and never for a global or a `var`
# parameter (the snapshot held no cell for either).

type PQ = ref object
  x: int
  s: string

var gPI: int
var gPS: string

proc sutPOrder(pi: ptr int; q: PQ) =
  ## The pointer's parameter comes before its target object's.
  if q == nil or pi == nil: return
  q.x = 1
  pi[] = 2
  if q.x == 2: symexTarget("po")

proc sutPOrderStr(ps: ptr string; k: int; q: PQ) =
  if q == nil or ps == nil: return
  q.s = "a"
  ps[] = "b"
  if q.s == "b" and k == 3: symexTarget("pos")

proc sutPGlobal(pi: ptr int) =
  if pi == nil: return
  gPI = 1
  pi[] = 2
  if gPI == 2: symexTarget("pg")

proc sutPGlobalStr(ps: ptr string) =
  if ps == nil: return
  gPS = "a"
  ps[] = "b"
  if gPS == "b": symexTarget("pgs")

proc sutPVar(v: var int; pi: ptr int) =
  if pi == nil: return
  v = 1
  pi[] = 2
  if v == 2: symexTarget("pv")

proc sutPVarFirst(pi: ptr int; v: var int) =
  ## The pointer before the `var` parameter it addresses.
  if pi == nil: return
  v = 1
  pi[] = 2
  if v == 2: symexTarget("pvf")

proc sutPVarStr(v: var string; ps: ptr string) =
  if ps == nil: return
  v = "a"
  ps[] = "b"
  if v == "b": symexTarget("pvs")

suite "S8bn (1-2): ptr alias witnesses":

  test "nim":
    let q = PQ(x: 0)
    sutPOrder(addr q.x, q)
    check q.x == 2
    sutPGlobal(addr gPI)
    check gPI == 2
    var v = 0
    sutPVar(v, addr v)
    check v == 2
    sutPVarFirst(addr v, v)
    check v == 2

  test "the pointer's parameter before its target object's":
    ## RED: `roRefuted` -- the witness built `pi` before `q`, so `pi` kept
    ## its own cell.
    confirmed(sutPOrder, "po")
    confirmed(sutPOrderStr, "pos")

  test "a pointer aimed at a global":
    ## RED: `roRefuted` -- the snapshot held no cell for the global.
    confirmed(sutPGlobal, "pg")
    confirmed(sutPGlobalStr, "pgs")

  test "a pointer aimed at a var parameter":
    ## RED: `roRefuted` -- the snapshot held no cell for the parameter.
    confirmed(sutPVar, "pv")
    confirmed(sutPVarFirst, "pvf")
    confirmed(sutPVarStr, "pvs")

# ---- 3. a var formal whose actual no pointer can address --------------------
#
# RFC-0005 S8bn item 3. While a callee (or a closure) runs, S8bh declined
# every deref of a `ptr T` of unknown origin when any frame had a `var`
# formal that may hold a T: the walk copies the formal in and out, so a
# store through a pointer into the actual's location would miss the
# formal. A local whose address is never taken is no pointer's target: no
# store through a pointer of unknown origin can reach it.

proc bumpVia(v: var int; pi: ptr int) =
  v = 1
  pi[] = 2

proc fwdVia(v: var int; pi: ptr int) = bumpVia(v, pi)

proc writeVia(pi: ptr int) = pi[] = 9

proc sutVFLocal(pi: ptr int) =
  if pi == nil: return
  var x = 0
  bumpVia(x, pi)
  if x == 1: symexTarget("vfl")
  if x != 1: symexTarget("vfl_dead")

proc sutVFFwd(pi: ptr int) =
  ## The callee passes its own `var` formal on: still the caller's local.
  if pi == nil: return
  var x = 0
  fwdVia(x, pi)
  if x == 1: symexTarget("vff")
  if x != 1: symexTarget("vff_dead")

proc sutVFClosure(pi: ptr int) =
  if pi == nil: return
  let f = proc (a: var int) =
    a = 1
    pi[] = 2
  var x = 0
  f(x)
  if x == 1: symexTarget("vfc")
  if x != 1: symexTarget("vfc_dead")

proc sutVFAddrTaken(pi: ptr int) =
  ## Control: the local's address is taken, so a pointer may be it.
  if pi == nil: return
  var x = 0
  writeVia(addr x)
  bumpVia(x, pi)
  if x == 1: symexTarget("vfa")

proc sutVFRootVar(v: var int; pi: ptr int) =
  ## Control: the SUT's own `var` parameter, forwarded.
  if pi == nil: return
  fwdVia(v, pi)
  if v == 2: symexTarget("vfr")

type VQ = ref object
  x: int

proc sutVFHeap(q: VQ; pi: ptr int) =
  ## Control: a heap field.
  if q == nil or pi == nil: return
  bumpVia(q.x, pi)
  if q.x == 2: symexTarget("vfh")

suite "S8bn (3): a var formal whose actual no pointer can address":

  test "nim":
    var y = 0
    sutVFLocal(addr y)
    check y == 2
    var v = 0
    sutVFRootVar(v, addr v)
    check v == 2
    let q = VQ()
    sutVFHeap(q, addr q.x)
    check q.x == 2

  test "a local whose address is never taken":
    ## RED: `sxUnknown` (`feUnsupportedOp`, naming S8bh).
    discard clean(sutVFLocal, "vfl", sxSat)
    discard clean(sutVFLocal, "vfl_dead", sxUnsat)
    discard clean(sutVFFwd, "vff", sxSat)
    discard clean(sutVFFwd, "vff_dead", sxUnsat)
    discard clean(sutVFClosure, "vfc", sxSat)
    discard clean(sutVFClosure, "vfc_dead", sxUnsat)

  test "a location a pointer may address still declines":
    declines(sutVFAddrTaken, "vfa", feUnsupportedOp, "RFC-0005 S8bh")
    declines(sutVFRootVar, "vfr", feUnsupportedOp, "RFC-0005 S8bh")
    declines(sutVFHeap, "vfh", feUnsupportedOp, "RFC-0005 S8bh")

# ---- 5. an always-raising closure is a raise ---------------------------------
#
# RFC-0005 S8bn item 5. A closure whose every body path raises reported
# `ceClosureBodyDiverged` (a halt, the run `sxUnknown`) beside the raise it
# had already routed to the caller (`drainClosureRaises`): the raise is the
# body's whole behaviour, not a divergence.

proc sutCloRaise(k: int) =
  let f = proc () = raise newException(ValueError, "always")
  try:
    f()
    symexTarget("clr_dead")
  except ValueError:
    if k == 3: symexTarget("clr")

proc sutCloRaiseVal(k: int) =
  let f = proc (a: int): int =
    if a > 0: raise newException(ValueError, "pos")
    raise newException(IOError, "nonpos")
  try:
    discard f(k)
    symexTarget("clv_dead")
  except ValueError:
    if k == 2: symexTarget("clv")
  except IOError:
    if k == -2: symexTarget("clk")

proc sutCloEscape(k: int) =
  let f = proc () = raise newException(ValueError, "out")
  f()

suite "S8bn (5): an always-raising closure is a raise":

  test "nim":
    sutCloRaise(3)
    sutCloRaiseVal(2)
    expect ValueError: sutCloEscape(0)

  test "every body path raises":
    ## RED: `sxUnknown` (`ceClosureBodyDiverged`).
    discard clean(sutCloRaise, "clr", sxSat)
    discard clean(sutCloRaise, "clr_dead", sxUnsat)
    discard clean(sutCloRaiseVal, "clv", sxSat)
    discard clean(sutCloRaiseVal, "clk", sxSat)
    discard clean(sutCloRaiseVal, "clv_dead", sxUnsat)
    let r = symexFind(sutCloEscape, tRaisedExn("ValueError"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised
    for e in r.errors: check e.severity == sevHint

# ---- 6b. S8bk's late address on a call through a proc value -----------------
#
# RFC-0005 S8bn item 6 (S8bk's integration note). Nim takes a `var` / `addr`
# actual's address AT THE CALL, after every later argument: `let f = touch;
# f(gB.x, moveB())` compiles to `T1_ = moveB(); f(&(*gB).x, T1_)`, so when
# `moveB` rebinds `gB` the callee reads and writes the new object. S8bh's
# call through a proc value copied the value in (or filled the `addr` cell)
# where the argument stood and wrote it back through the late address. Only
# the address's checks (an index's bound) run where the argument stands; a
# later call that changes what one read declines.

type LBox = ref object
  x: int

var gB: LBox
var gLArr: array[3, int]
var gLs: seq[int]
var gLi: int

proc moveB(): int =
  gB = LBox(x: 100)
  0

proc bumpLArr(): int =
  gLArr[0] = 50
  0

proc bumpLs(): int =
  gLs[0] = 50
  0

proc incLi(): int =
  inc gLi
  0

proc ltouch(v: var int; k: int) = v = v + 5 + k
proc ltouchP(v: ptr int; k: int) = v[] = v[] + 5 + k

proc sutLateCopy(k: int) =
  if k < 0 or k > 1000: return
  let f = ltouch
  gB = LBox(x: k)
  let old = gB
  f(gB.x, moveB())
  if gB.x == 105 and old.x == k and k == 3: symexTarget("lcp")
  if gB.x != 105 or old.x != k: symexTarget("lcp_dead")

proc sutLateAddr(k: int) =
  if k < 0 or k > 1000: return
  let f = ltouchP
  gB = LBox(x: k)
  let old = gB
  f(addr gB.x, moveB())
  if gB.x == 105 and old.x == k and k == 9: symexTarget("lad")
  if gB.x != 105 or old.x != k: symexTarget("lad_dead")

proc sutLateArr(k: int) =
  ## The later call writes the element: the callee reads it after.
  if k < 0 or k > 1000: return
  let f = ltouch
  gLArr = [k, 20, 30]
  gLi = 0
  f(gLArr[gLi], bumpLArr())
  if gLArr[0] == 55 and k == 6: symexTarget("lar")
  if gLArr[0] != 55: symexTarget("lar_dead")

proc sutLateSeq(k: int) =
  if k < 0 or k > 1000: return
  let f = ltouch
  gLs = @[k, 20, 30]
  gLi = 0
  f(gLs[gLi], bumpLs())
  if gLs[0] == 55 and k == 7: symexTarget("lsq")
  if gLs[0] != 55: symexTarget("lsq_dead")

proc sutLateIdxMoved(k: int) =
  ## The later call moves the index Nim checked: UB, declined.
  if k < 0 or k > 1000: return
  let f = ltouch
  gLArr = [k, 20, 30]
  gLi = 0
  f(gLArr[gLi], incLi())
  if gLArr[1] == 25 and k == 1: symexTarget("lim")

suite "S8bn (6b): a by-address argument's address is taken at the call":

  test "nim":
    gB = LBox(x: 3)
    let old = gB
    let f = ltouch
    f(gB.x, moveB())
    check gB.x == 105 and old.x == 3
    gB = LBox(x: 3)
    let old2 = gB
    let g = ltouchP
    g(addr gB.x, moveB())
    check gB.x == 105 and old2.x == 3
    gLArr = [6, 20, 30]
    gLi = 0
    f(gLArr[gLi], bumpLArr())
    check gLArr[0] == 55
    gLs = @[7, 20, 30]
    f(gLs[gLi], bumpLs())
    check gLs[0] == 55

  test "a copy-in and an addr cell at the call":
    ## RED: the dead labels `sxSat` (false), the live ones `sxUnsat`.
    discard clean(sutLateCopy, "lcp", sxSat)
    discard clean(sutLateCopy, "lcp_dead", sxUnsat)
    discard clean(sutLateAddr, "lad", sxSat)
    discard clean(sutLateAddr, "lad_dead", sxUnsat)
    discard clean(sutLateArr, "lar", sxSat)
    discard clean(sutLateArr, "lar_dead", sxUnsat)
    discard clean(sutLateSeq, "lsq", sxSat)
    discard clean(sutLateSeq, "lsq_dead", sxUnsat)

  test "a later call that moves a checked index declines":
    declines(sutLateIdxMoved, "lim", feUnsupportedOp, "never checked")
