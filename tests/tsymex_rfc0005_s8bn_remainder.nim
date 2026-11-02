## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
import std/[unittest, strutils, options, macros, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser

macro progOf(fn: typed): untyped =
  ## The `SymexProgram` `symexFind` would build for `fn`, so a test can read
  ## the raw `RawResult` (its `candidates`), which `symexFind` folds away.
  let parsed = parseEntryImpl(fn, "progOf",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  let b = parsed.bodyNimNode
  let p = parsed.paramsNimNode
  let pr = parsed.procsNimNode
  let u = parsed.userExnHierarchyNimNode
  let pe = parsed.parseErrorsNimNode
  result = quote do:
    SymexProgram(params: `p`, body: `b`, procs: `pr`,
                 userExnHierarchy: `u`, parseErrors: `pe`)

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
  ## A heap field. RFC-0005 batch 6: S8bs passes a heap lvalue by reference
  ## (`byRefSub`), so the callee writes the cell itself, not a copy, and a
  ## pointer into it needs no decline.
  if q == nil or pi == nil: return
  bumpVia(q.x, pi)
  if q.x == 2: symexTarget("vfh")
  if q.x != 1 and q.x != 2: symexTarget("vfh_dead")

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

  test "a heap field is passed by reference (S8bs)":
    ## Was a decline (the copy-in/copy-out formal). Native: the "nim" test
    ## above reaches `q.x == 2` with `pi = addr q.x`; the witness replays.
    confirmed(sutVFHeap, "vfh")
    discard clean(sutVFHeap, "vfh_dead", sxUnsat)

# ---- 4. a ptr into an aggregate -----------------------------------------------
#
# RFC-0005 S8bn item 4. A `ptr` of unknown origin that may address a part of
# a by-value aggregate global or `var` parameter, or an element of a seq held
# in the heap, declined (`feUnsupportedOp`, "by-value aggregate this model
# holds no cell for" / "held in a heap cell"). Each such part is now a
# candidate target named by S8ax's element-alias identity (root, path,
# snapshot index): a field, an array element, a seq element (its index is
# the pointer's own, within the seq's input length). A seq whose length the
# path changed still declines: a resize may move its elements.

type
  HS4 = ref object
    xs: seq[int]
  PO4 = object
    a, b: int

proc sutPTupVar(t: var tuple[a, b: int]; p: ptr int) =
  if p == nil: return
  t.a = 0
  t.b = 5
  p[] = 7
  if t.b == 7: symexTarget("ptv")
  if t.a == 7 and t.b == 7: symexTarget("ptv_dead")

proc sutPObjVar(p: ptr int; o: var PO4) =
  ## The pointer before the object it addresses a field of.
  if p == nil: return
  o.a = 0
  p[] = 4
  if o.a == 4: symexTarget("pov")

proc sutPArrVar(a: var array[3, int]; p: ptr int) =
  if p == nil: return
  a[0] = 0
  a[1] = 0
  p[] = 4
  if a[1] == 4: symexTarget("pav")
  if a[0] == 4 and a[1] == 4: symexTarget("pav_dead")

proc sutPSeqVar(s: var seq[int]; p: ptr int) =
  if p == nil or s.len < 2: return
  s[0] = 0
  s[1] = 0
  p[] = 9
  if s[1] == 9: symexTarget("psv")
  if s[0] == 9 and s[1] == 9: symexTarget("psv_dead")

proc sutPSeqGrow(s: var seq[int]; p: ptr int) =
  if p == nil: return
  s.add 1
  p[] = 3
  if s[0] == 3: symexTarget("psg")

proc sutPTabVar(t: var Table[string, int]; p: ptr int) =
  if p == nil or not t.hasKey("a"): return
  t["a"] = 0
  p[] = 5
  if t["a"] == 5: symexTarget("ptb")

proc sutPTabGrow(t: var Table[string, int]; p: ptr int) =
  if p == nil: return
  t["fresh"] = 1
  p[] = 3
  if t.len == 1: symexTarget("ptbg")

proc sutPSetVar(s: var HashSet[int]; p: ptr int) =
  ## A set's members have no address: no pointer reaches them.
  if p == nil: return
  s.incl 4
  p[] = 9
  if 9 in s and not (4 in s): symexTarget("pss_dead")
  if 4 in s: symexTarget("pss")

proc sutPHeapSeqPop(h: HS4; p: ptr int) =
  ## A length changed and changed back: `add` may have moved the elements.
  if h == nil or p == nil or h.xs.len < 1: return
  h.xs.add 1
  discard h.xs.pop()
  p[] = 6
  if h.xs[0] == 6: symexTarget("phsp")

proc sutPTabDel(t: var Table[string, int]; p: ptr int) =
  ## A deletion may shift the other entries.
  if p == nil or not t.hasKey("a") or not t.hasKey("b"): return
  t.del("b")
  p[] = 5
  if t["a"] == 5: symexTarget("ptbd")

proc sutPHeapSeq(h: HS4; p: ptr int) =
  if h == nil or p == nil or h.xs.len < 1: return
  h.xs[0] = 1
  p[] = 6
  if h.xs[0] == 6: symexTarget("phs")

suite "S8bn (4): a ptr into an aggregate":

  test "nim":
    var t: tuple[a, b: int]
    sutPTupVar(t, addr t.b)
    check t.b == 7
    var o: PO4
    sutPObjVar(addr o.a, o)
    check o.a == 4
    var a: array[3, int]
    sutPArrVar(a, addr a[1])
    check a[1] == 4
    var s = @[5, 5]
    sutPSeqVar(s, addr s[1])
    check s[1] == 9
    var tb = {"a": 1}.toTable
    sutPTabVar(tb, addr tb["a"])
    check tb["a"] == 5
    let h = HS4(xs: @[0])
    sutPHeapSeq(h, addr h.xs[0])
    check h.xs[0] == 6

  test "a field or element of a by-value aggregate":
    ## RED: sxUnknown, `feUnsupportedOp` "by-value aggregate this model
    ## holds no cell for".
    confirmed(sutPTupVar, "ptv")
    discard clean(sutPTupVar, "ptv_dead", sxUnsat)
    confirmed(sutPObjVar, "pov")
    confirmed(sutPArrVar, "pav")
    discard clean(sutPArrVar, "pav_dead", sxUnsat)

  test "an element of a seq":
    ## RED: sxUnknown, as above.
    confirmed(sutPSeqVar, "psv")
    discard clean(sutPSeqVar, "psv_dead", sxUnsat)

  test "an element of a seq held in the heap":
    ## RED: sxUnknown, `feUnsupportedOp` "held in a heap cell".
    confirmed(sutPHeapSeq, "phs")
    declines(sutPHeapSeqPop, "phsp", feUnsupportedOp, "may dangle")

  test "a seq the path resized still declines":
    declines(sutPSeqGrow, "psg", feUnsupportedOp, "may dangle")

  test "a value of a table, and a set's members":
    ## RED: sxUnknown, `feUnsupportedOp` "by-value aggregate this model
    ## holds no cell for".
    confirmed(sutPTabVar, "ptb")
    declines(sutPTabGrow, "ptbg", feUnsupportedOp, "may dangle")
    declines(sutPTabDel, "ptbd", feUnsupportedOp, "may dangle")
    discard clean(sutPSetVar, "pss", sxSat)
    discard clean(sutPSetVar, "pss_dead", sxUnsat)

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
    ## RFC-0005 batch 6: S8bk's `placeLateAddr` (on the base) replaces the
    ## port S8bn made of it; its decline kind is `feEvalOrderUnmodelled`.
    declines(sutLateIdxMoved, "lim", feEvalOrderUnmodelled, "never checked")

# ---- 9. a parameter's run-type tags follow its static type ------------------
#
# RFC-0005 S8bn item 9. S8bh stored a hierarchy object's run-type tag per
# depth at allocation, but a parameter's tags were free: a `Mid9` parameter
# could carry a tag no `Mid9` has. When it aliases a `Base9` parameter, a
# down-conversion of the `Base9` one could then fail although the object is
# a `Mid9` (a `sxSat` no Nim value reaches).

type
  Base9 = ref object of RootObj
    x: int
  Mid9 = ref object of Base9
    y: int
  Leaf9 = ref object of Mid9
  Side9 = ref object of Base9

proc sutTagAlias(b: Base9; d: Mid9) =
  if b == nil or d == nil: return
  if Base9(d) == b:
    try:
      let m = Mid9(b)
      if m.y == d.y: symexTarget("ta")
    except ObjectConversionDefect:
      symexTarget("ta_dead")

proc sutTagSide(b: Base9; s: Side9) =
  ## A `Side9` is never a `Mid9`.
  if s == nil: return
  if Base9(s) == b:
    try:
      discard Mid9(b)
      symexTarget("ts_dead")
    except ObjectConversionDefect:
      symexTarget("ts")

proc sutTagFree(b: Base9) =
  ## Control: a `Base9` parameter may be any descendant.
  if b == nil: return
  try:
    discard Leaf9(b)
    symexTarget("tf_leaf")
  except ObjectConversionDefect:
    symexTarget("tf_raise")

suite "S8bn (9): a parameter's run-type tags follow its static type":

  test "nim":
    let m = Mid9(x: 1, y: 2)
    sutTagAlias(m, m)
    let s = Side9()
    sutTagSide(s, s)

  test "a parameter aliasing another of a deeper static type":
    ## RED: `ta_dead` / `ts_dead` `sxSat` (false): the tags were free.
    discard clean(sutTagAlias, "ta", sxSat)
    discard clean(sutTagAlias, "ta_dead", sxUnsat)
    discard clean(sutTagSide, "ts", sxSat)
    discard clean(sutTagSide, "ts_dead", sxUnsat)
    discard clean(sutTagFree, "tf_leaf", sxSat)
    discard clean(sutTagFree, "tf_raise", sxSat)

# ---- 6. proc fields and methods ----------------------------------------------
#
# RFC-0005 S8bn item 6. A call through a proc field (`o.f(x)`) and a method
# call declined (S8bh's audit). A proc field is a call through a proc value
# (S8bh's path, `var` effects included); a method call dispatches over the
# overrides on the run-type tag. A target the walk cannot resolve havocs
# what the callee could write: its `var` actuals, the heap and the globals.

proc setBoth6(a, b: var int) =
  b = 2
  a = 1

proc setOne6(a, b: var int) =
  a = 7

type Ops6 = object
  f: proc (a, b: var int) {.nimcall.}
  k: int

type ROps6 = ref object
  f: proc (a, b: var int) {.nimcall.}

proc sutProcField(k: int) =
  let o = Ops6(f: setBoth6, k: k)
  var x = k
  var y = k
  o.f(x, y)
  if x != 1 or y != 2: symexTarget("pf_dead")
  if x == 1 and y == 2 and k == 3: symexTarget("pf")

proc sutProcFieldPick(k: int) =
  var o = Ops6(f: setBoth6)
  if k > 0: o.f = setOne6
  var x = 0
  var y = 0
  o.f(x, y)
  if k > 0 and x != 7: symexTarget("pp_dead")
  if k <= 0 and x != 1: symexTarget("pp2_dead")
  if x == 7: symexTarget("pp")

proc sutProcFieldRef(k: int) =
  ## A proc field of a heap object: the assignments to it are its targets.
  let o = ROps6(f: setBoth6)
  if k > 5: o.f = setOne6
  var x = 0
  var y = 0
  o.f(x, y)
  if k > 5 and x != 7: symexTarget("pr_dead")
  if k <= 5 and (x != 1 or y != 2): symexTarget("pr2_dead")
  if x == 7: symexTarget("pr")

proc sutProcFieldIn(o: ROps6) =
  ## An input's proc field: no assignment the walk sees names its proc.
  if o == nil: return
  var x = 0
  var y = 0
  o.f(x, y)
  if x == 1: symexTarget("pin")

proc sutProcFieldNilRef(k: int) =
  ## A field `new` left nil, never called: the nil code is not dispatched.
  let o = ROps6()
  var x = 0
  var y = 0
  if k > 0: o.f = setBoth6
  if k > 0: o.f(x, y)
  if x == 1 and k <= 0: symexTarget("pn_dead")
  if x == 1: symexTarget("pn")

proc sutProcFieldExpr(k: int) =
  ## In an expression position.
  let o = Ops6(f: setBoth6, k: k)
  var x = k
  var y = k
  o.f(x, y)
  let s = x + y
  if s != 3: symexTarget("pe_dead")

type
  Shape6 = ref object of RootObj
    w: int
  Square6 = ref object of Shape6
  Disc6 = ref object of Shape6

method setM6(o: Shape6; a: var int) {.base.} = a = 5
method setM6(o: Square6; a: var int) = a = 6

proc sutMethod(k: int) =
  let o: Shape6 = Square6()
  var x = k
  o.setM6(x)
  if x != 6: symexTarget("m_dead")
  if x == 6 and k == 2: symexTarget("m")

proc sutMethodParam(o: Shape6; k: int) =
  ## The dynamic type picks the override: a `Disc6` has none of its own.
  if o == nil: return
  var x = k
  o.setM6(x)
  if x == 6: symexTarget("mp6")
  if x == 5: symexTarget("mp5")
  if x != 5 and x != 6: symexTarget("mp_dead")

var gHav: int

proc sutUnknownGlobal(f: proc (a: var int) {.nimcall.}; k: int) =
  ## An unknown target may write any global it can reach.
  gHav = 3
  var x = 0
  f(x)
  if gHav != 3: symexTarget("ug_moved")

suite "S8bn (6): proc fields and methods":

  test "nim":
    var x = 3
    var y = 3
    let o = Ops6(f: setBoth6)
    o.f(x, y)
    check x == 1 and y == 2
    let s: Shape6 = Square6()
    s.setM6(x)
    check x == 6
    let d: Shape6 = Disc6()
    d.setM6(x)
    check x == 5

  test "a call through a proc field":
    ## RED: `sxUnknown` (`feUnsupportedStmtKind`, `o.f`).
    discard clean(sutProcField, "pf", sxSat)
    discard clean(sutProcField, "pf_dead", sxUnsat)
    discard clean(sutProcFieldPick, "pp", sxSat)
    discard clean(sutProcFieldPick, "pp_dead", sxUnsat)
    discard clean(sutProcFieldPick, "pp2_dead", sxUnsat)
    discard clean(sutProcFieldExpr, "pe_dead", sxUnsat)

  test "a proc field of a heap object":
    discard clean(sutProcFieldRef, "pr", sxSat)
    discard clean(sutProcFieldRef, "pr_dead", sxUnsat)
    discard clean(sutProcFieldRef, "pr2_dead", sxUnsat)
    discard clean(sutProcFieldNilRef, "pn", sxSat)
    discard clean(sutProcFieldNilRef, "pn_dead", sxUnsat)

  test "a heap proc field no assignment names declines":
    declines(sutProcFieldIn, "pin", feUnsupportedOp, "no assignment")

  test "a method call dispatches on the run-type tag":
    ## RED: `sxUnknown` (`feUnsupportedOp`, `setM6`).
    discard clean(sutMethod, "m", sxSat)
    discard clean(sutMethod, "m_dead", sxUnsat)
    discard clean(sutMethodParam, "mp6", sxSat)
    discard clean(sutMethodParam, "mp5", sxSat)
    discard clean(sutMethodParam, "mp_dead", sxUnsat)

  test "an unknown target havocs the globals it may write":
    declines(sutUnknownGlobal, "ug_moved", ceClosureUnknownCallee, "`f`")
    ## RED: no candidate -- the global kept its value past the call, and
    ## only the path's taint stood for the havoc.
    let r = runSymex(progOf(sutUnknownGlobal), tLabel("ug_moved"))
    checkpoint $r.status & " " & show(r.errors)
    check r.candidates.len > 0

# ---- 7. the `of` operator and `nil` literals ----------------------------------
#
# RFC-0005 S8bn item 7. `x of T` was unsupported, and a `nil` literal parsed
# only in a comparison and a ref field's constructor value: `let b: Base =
# nil` declined. `of` is a test of the run-type tag (S8bh's per-depth tags,
# `inheritTagKey`); a `nil` literal is the type's nil in every typed position.

type
  Base7 = ref object of RootObj
    x: int
  Mid7 = ref object of Base7
  Leaf7 = ref object of Mid7
  Side7 = ref object of Base7

proc sutOf(b: Base7) =
  if b of Mid7: symexTarget("of_mid")
  elif b of Side7: symexTarget("of_side")
  elif b != nil: symexTarget("of_base")
  else: symexTarget("of_nil")

proc sutOfLocal(k: int) =
  var b: Base7 = Side7(x: k)
  if k > 0: b = Leaf7(x: k)
  if b of Mid7 and k <= 0: symexTarget("ofl_dead")
  if not (b of Mid7) and k > 0: symexTarget("ofl2_dead")
  if not (b of Base7): symexTarget("ofl3_dead")
  if b of Leaf7 and k == 2: symexTarget("ofl")

proc sutOfStatic(m: Mid7) =
  ## Statically true for a non-nil ref of the type or a subtype.
  if m != nil and not (m of Base7): symexTarget("ofs_dead")
  if m != nil and m of Mid7: symexTarget("ofs")

proc takes7(b: Base7): int =
  if b == nil: 0 else: 1

proc sutNil(k: int) =
  let b: Base7 = nil
  var p: ptr int = nil
  var c = Mid7(x: k)
  if k > 0: c = nil
  let n = takes7(nil)
  if b != nil or p != nil or n != 0: symexTarget("nl_dead")
  if k > 0 and c != nil: symexTarget("nl2_dead")
  if c == nil and k == 1: symexTarget("nl")

proc retNil(k: int): Base7 =
  if k > 0: return nil
  Base7(x: k)

proc sutNilRet(k: int) =
  let r = retNil(k)
  if k > 0 and r != nil: symexTarget("nr_dead")
  if r == nil and k == 4: symexTarget("nr")

suite "S8bn (7): the `of` operator and nil literals":

  test "nim":
    check not (Base7(nil) of Mid7)
    let l: Base7 = Leaf7()
    check l of Mid7 and l of Leaf7 and not (l of Side7)
    sutOfLocal(2)
    sutNil(1)

  test "`of` tests the run-type tag":
    ## RED: `sxUnknown` (`of` unsupported).
    discard clean(sutOf, "of_mid", sxSat)
    discard clean(sutOf, "of_side", sxSat)
    discard clean(sutOf, "of_base", sxSat)
    discard clean(sutOf, "of_nil", sxSat)
    discard clean(sutOfLocal, "ofl", sxSat)
    discard clean(sutOfLocal, "ofl_dead", sxUnsat)
    discard clean(sutOfLocal, "ofl2_dead", sxUnsat)
    discard clean(sutOfLocal, "ofl3_dead", sxUnsat)
    discard clean(sutOfStatic, "ofs", sxSat)
    discard clean(sutOfStatic, "ofs_dead", sxUnsat)

  test "a nil literal in every typed position":
    ## RED: `sxUnknown` (the literal did not parse).
    discard clean(sutNil, "nl", sxSat)
    discard clean(sutNil, "nl_dead", sxUnsat)
    discard clean(sutNil, "nl2_dead", sxUnsat)
    discard clean(sutNilRet, "nr", sxSat)
    discard clean(sutNilRet, "nr_dead", sxUnsat)

# ---- 8. generic, inheritable and case-object hierarchies ----------------------
#
# RFC-0005 S8bn item 8. S8bh's shared address space (one `Ref_<root>` sort,
# a field's heap keyed on its declaring type) covered a chain of plain
# objects under `RootObj`. A `{.inheritable.}` root, `of RootRef`, a generic
# hierarchy and one whose root is a case object kept per-type keying: a
# conversion among them was ill-sorted, and two parameters of two static
# types never aliased.

type
  IBase8 {.inheritable.} = ref object
    x: int
  IMid8 = ref object of IBase8
    y: int
  RBase8 = ref object of RootRef
    x: int
  RMid8 = ref object of RBase8
  CKind8 = enum ckA, ckB
  CBase8 = ref object of RootObj
    case k: CKind8
    of ckA: a: int
    of ckB: b: int
  CMid8 = ref object of CBase8
    z: int

proc sutInhAlias(b: IBase8; d: IMid8) =
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2 and IBase8(d) == b: symexTarget("ia")
  if d.x != 2 and IBase8(d) == b: symexTarget("ia_dead")

proc sutRootRefAlias(b: RBase8; d: RMid8) =
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2: symexTarget("ra")
  if d.x != 1 and d.x != 2: symexTarget("ra_dead")

proc sutCaseAlias(b: CBase8; d: CMid8) =
  if b == nil or d == nil: return
  d.z = 1
  if CBase8(d) == b and b.k == ckA:
    b.a = 2
    if d.a == 2: symexTarget("ca")
    if d.a != 2: symexTarget("ca_dead")

proc sutCaseDown(k: int) =
  let b: CBase8 = CMid8(k: ckB, b: k, z: 3)
  let d = CMid8(b)
  if d.z != 3 or d.b != k: symexTarget("cd_dead")
  if d.z == 3 and k == 5: symexTarget("cd")

suite "S8bn (8): generic, inheritable and case-object hierarchies":

  test "nim":
    let d = IMid8()
    sutInhAlias(d, d)
    check d.x == 2
    let c = CMid8(k: ckA)
    sutCaseAlias(c, c)
    check c.a == 2

  test "an inheritable root and `of RootRef`":
    discard clean(sutInhAlias, "ia", sxSat)
    discard clean(sutInhAlias, "ia_dead", sxUnsat)
    discard clean(sutRootRefAlias, "ra", sxSat)
    discard clean(sutRootRefAlias, "ra_dead", sxUnsat)

  test "a hierarchy rooted at a case object":
    discard clean(sutCaseAlias, "ca", sxSat)
    discard clean(sutCaseAlias, "ca_dead", sxUnsat)
    discard clean(sutCaseDown, "cd", sxSat)
    discard clean(sutCaseDown, "cd_dead", sxUnsat)

# ---- 8b. generic hierarchies ----------------------------------------------------
#
# RFC-0005 S8bn item 8. A generic object type was not classified at all
# (`G[int]`, by value or by ref, was `feUnsupportedParamType`), so a generic
# hierarchy had no address space to join. An instance is now classified
# with its arguments substituted into the body, keyed on the instance, and a
# generic parent (`of GBase8[T]`) joins the chain as a plain parent does.

type
  GBase8[T] = ref object of RootObj
    x: T
  GMid8[T] = ref object of GBase8[T]
    y: T
  GPair8[A, B] = object
    a: A
    b: seq[B]
  GNode8[T] = ref object
    v: T
    next: GNode8[T]

proc sutGenAlias(b: GBase8[int]; d: GMid8[int]) =
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2 and GBase8[int](d) == b: symexTarget("ga")
  if d.x != 2 and GBase8[int](d) == b: symexTarget("ga_dead")

proc sutGenDown(k: int) =
  let b: GBase8[int] = GMid8[int](x: k, y: 4)
  let d = GMid8[int](b)
  if d.y != 4: symexTarget("gd_dead")
  if d.x == 3: symexTarget("gd")
  try:
    discard GMid8[int](GBase8[int](x: 1))
    symexTarget("gd2_dead")
  except ObjectConversionDefect:
    discard

proc sutGenValue(p: GPair8[int, int]) =
  if p.a == 5 and p.b.len == 1 and p.b[0] == 2: symexTarget("gv")

proc sutGenList(n: GNode8[int]) =
  if n != nil and n.next != nil and n.next.v == 4: symexTarget("gl")

suite "S8bn (8b): generic hierarchies":

  test "nim":
    let g = GMid8[int]()
    sutGenAlias(g, g)
    check g.x == 2
    expect ObjectConversionDefect:
      discard GMid8[int](GBase8[int](x: 1))

  test "a generic hierarchy shares one address space":
    ## RED: sxUnknown, `feUnsupportedParamType` "GBase8[int]".
    confirmed(sutGenAlias, "ga")
    discard clean(sutGenAlias, "ga_dead", sxUnsat)
    discard clean(sutGenDown, "gd", sxSat)
    discard clean(sutGenDown, "gd_dead", sxUnsat)
    discard clean(sutGenDown, "gd2_dead", sxUnsat)

  test "a generic object, by value and recursive":
    ## RED: sxUnknown, `feUnsupportedParamType`.
    confirmed(sutGenValue, "gv")
    confirmed(sutGenList, "gl")

suite "S8bn: walker version":

  test "the walker version is at least S8bn's":
    check parseInt(symexWalkerVersion) >= 215
