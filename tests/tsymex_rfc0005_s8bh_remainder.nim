## RFC-0005 (soundness channels) slice S8bh -- S8bf's remainder.
##
## Three soundness findings S8bf reported and did not fix:
##
## 1. A call through a proc-valued variable dropped its `var` writes: the
##    closure-call arm (`applyClosureGround`) lowered the arguments by value
##    and had no copy-out, so `let f = setBoth; f(x, y)` left `x` as it was
##    (a false `sxSat` for `x != 1`). The same held for every indirect call
##    that reaches that arm: a lambda, a generic callee's proc parameter, a
##    proc passed to a callee, and a heap actual (`f(p.x, y)`).
## 2. A `ptr` parameter never addressed a ref object's field: `q.x = 1;
##    pi[] = 2; if q.x == 2` was `sxUnsat`, but Nim reaches it with
##    `pi = addr q.x`.
## 3. Converting a ref up its inheritance chain built an ill-sorted term:
##    `Base(d) == b` was `weInternalWalkerFault`.
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

# ---- 1. var writes through an indirect call ---------------------------------

type Box = ref object
  x: int
  y: int

proc setBoth(a, b: var int) =
  ## Writes `b`, then `a`: on one location, `a`'s write is the last.
  b = 2
  a = 1

proc setOne(a: var int) =
  a = 4

proc retV(a: var int): int =
  a = 9
  result = 1

proc setRaise(a: var int; k: int) =
  a = 5
  if k > 0: raise newException(ValueError, "after the write")

proc sutPV(k: int) =
  let f = setBoth
  var x = k
  var y = k
  f(x, y)
  if x != 1 or y != 2: symexTarget("pv_dead")
  if x == 1 and y == 2 and k == 3: symexTarget("pv")

proc sutPVSame(k: int) =
  ## One variable passed twice: one location, written in the callee's order.
  let f = setBoth
  var x = k
  f(x, x)
  if x != 1: symexTarget("pvs_dead")
  if x == 1 and k == 4: symexTarget("pvs")

proc sutLam(k: int) =
  if k < -1000 or k > 1000: return
  let f = proc (a: var int) = a = a + 7
  var x = k
  f(x)
  if x != k + 7: symexTarget("lam_dead")
  if x == 10: symexTarget("lam")

proc sutLamCap(k: int) =
  ## The lambda reads a capture that is not the actual.
  if k < -1000 or k > 1000: return
  let c = k * 2
  let f = proc (a: var int) = a = c + 1
  var x = k
  f(x)
  if x != 2 * k + 1: symexTarget("lc_dead")
  if x == 7: symexTarget("lc")

proc applyG[F](f: F; a, b: var int) = f(a, b)

proc sutGen(k: int) =
  ## A generic callee's proc parameter, its `var` formals forwarded.
  var x = k
  var y = k
  applyG(setBoth, x, y)
  if x != 1 or y != 2: symexTarget("gen_dead")
  if x == 1 and k == 5: symexTarget("gen")

proc applyP(f: proc (a, b: var int) {.nimcall.}; a, b: var int) = f(a, b)

proc sutHof(k: int) =
  ## A proc passed to a callee.
  var x = k
  var y = k
  applyP(setBoth, x, y)
  if x != 1 or y != 2: symexTarget("hof_dead")
  if y == 2 and k == 6: symexTarget("hof")

proc sutExpr(k: int) =
  ## A call in an expression: the write lands before the operand after it.
  let f = retV
  var x = k
  let r = f(x) + x
  if x != 9 or r != 10: symexTarget("ex_dead")
  if r == 10 and k == 2: symexTarget("ex")

proc sutCond(k: int) =
  let f = setOne
  var x = k
  if k > 3:
    f(x)
  if k > 3 and x != 4: symexTarget("cd_dead")
  if k <= 3 and x != k: symexTarget("cd2_dead")
  if x == 4 and k == 9: symexTarget("cd")

proc sutRaise(k: int) =
  ## A write before a raise is seen by the handler.
  let f = setRaise
  var x = k
  try:
    f(x, k)
  except ValueError:
    if x != 5: symexTarget("rs_dead")
    if x == 5 and k == 1: symexTarget("rs")
  if x != 5: symexTarget("rs2_dead")

proc sutField(k: int) =
  ## A field of a value tuple.
  var t = (a: k, b: k)
  let f = setOne
  f(t.a)
  if t.a != 4 or t.b != k: symexTarget("vf_dead")
  if t.a == 4 and k == 8: symexTarget("vf")

proc sutHeap(k: int) =
  let f = setBoth
  let p = Box(x: k)
  var y = k
  f(p.x, y)
  if p.x != 1 or y != 2: symexTarget("h_dead")
  if p.x == 1 and k == 3: symexTarget("h")

proc sutHeapPeers(k: int) =
  ## Two heap actuals through different refs to one cell (S8bf's shape).
  let f = setBoth
  let p = Box(x: k)
  let q = p
  f(p.x, q.x)
  if p.x != 1: symexTarget("hp_dead")
  if q.x == 1 and k == 4: symexTarget("hp")

proc sutHeapParams(p, q: Box) =
  ## Two parameter refs: one cell exactly when `p == q`.
  if p == nil or q == nil: return
  let f = setBoth
  f(p.x, q.x)
  if p == q and p.x != 1: symexTarget("hq_dead")
  if p == q and p.x == 1: symexTarget("hq_same")
  if p != q and p.x == 1 and q.x == 2: symexTarget("hq_diff")
  if p != q and q.x != 2: symexTarget("hq_diff_dead")

proc sutHeapFresh(k: int) =
  ## Two allocations: two cells, each with its own write.
  let f = setBoth
  let p = Box(x: k)
  let q = Box(x: k)
  f(p.x, q.x)
  if p.x != 1 or q.x != 2: symexTarget("hf_dead")
  if p.x == 1 and q.x == 2 and k == 5: symexTarget("hf")

proc setBothP(a, b: ptr int) =
  b[] = 2
  a[] = 1

proc sutAddr(k: int) =
  let f = setBothP
  var x = k
  var y = k
  f(addr x, addr y)
  if x != 1 or y != 2: symexTarget("ad_dead")
  if x == 1 and k == 6: symexTarget("ad")

proc sutAddrSame(k: int) =
  let f = setBothP
  var x = k
  f(addr x, addr x)
  if x != 1: symexTarget("as_dead")
  if x == 1 and k == 7: symexTarget("as")

proc sutAddrPeers(k: int) =
  let f = setBothP
  let p = Box(x: k)
  let q = p
  f(addr p.x, addr q.x)
  if p.x != 1: symexTarget("ap_dead")
  if p.x == 1 and k == 8: symexTarget("ap")

proc sutCapAlias(k: int) =
  ## The actual is also the lambda's capture: one location in Nim (`a = 1`
  ## writes `c`, so `c + a` is 2); the walk keeps a copy of each.
  var c = k
  let f = proc (a: var int) =
    a = 1
    a = c + a
  f(c)
  if c != 2: symexTarget("ca_dead")

proc sutUnknown(f: proc (a, b: var int) {.nimcall.}; k: int) =
  ## A proc parameter of the code under test: no target to walk.
  var x = k
  var y = k
  f(x, y)
  if x == k: symexTarget("uk")
  if x != k: symexTarget("uk_moved")

proc sutUnknownHeap(f: proc (a: var int) {.nimcall.}; p: Box) =
  ## The unknown target may also write any heap cell.
  if p == nil: return
  p.y = 3
  var x = 0
  f(x)
  if p.y != 3: symexTarget("ukh_moved")

proc sutHeapCapture(k: int) =
  ## The lambda reaches the actual's cell through its capture: `cap.x = 5`
  ## lands on `p.x` after the formal's write (Nim: 5).
  let p = Box(x: k)
  let cap = p
  let f = proc (a: var int) =
    a = 1
    cap.x = 5
  f(p.x)
  if p.x != 5: symexTarget("hc_dead")

proc sutHeapCaptureOther(k: int) =
  ## A capture of a type that holds no ref to a `Box` cell: no decline.
  let t = (a: k, b: k)
  let p = Box(x: k)
  let f = proc (a: var int) = a = t.a + 1
  if k > 1000 or k < -1000: return
  f(p.x)
  if p.x != k + 1: symexTarget("hco_dead")
  if p.x == 4: symexTarget("hco")

var gPtr: ptr int

proc sutAddrEscape(k: int) =
  ## The body keeps the pointer: a cell for the call is not Nim's address.
  let f = proc (a: ptr int) =
    gPtr = a
    a[] = 1
  var x = k
  f(addr x)
  if x != 1: symexTarget("ae_dead")

type Ops = object
  f: proc (a, b: var int) {.nimcall.}

proc sutProcField(k: int) =
  let o = Ops(f: setBoth)
  var x = k
  var y = k
  o.f(x, y)
  if x != 1: symexTarget("pfld_dead")

type Shape = ref object of RootObj
type Square = ref object of Shape

method setM(o: Shape; a: var int) {.base.} = a = 5
method setM(o: Square; a: var int) = a = 6

proc sutMethod(k: int) =
  let o: Shape = Square()
  var x = k
  o.setM(x)
  if x != 6: symexTarget("m_dead")

suite "S8bh (1): var writes through an indirect call":

  test "nim":
    var x = 3
    var y = 3
    let f = setBoth
    f(x, y)
    check x == 1 and y == 2
    f(x, x)
    check x == 1
    applyG(setBoth, x, y)
    check x == 1
    let g = retV
    x = 2
    let r = g(x) + x
    check x == 9 and r == 10
    let p = Box(x: 3)
    let q = p
    f(p.x, q.x)
    check p.x == 1
    let fp = setBothP
    fp(addr p.x, addr q.x)
    check p.x == 1
    var c = 3
    let h = proc (a: var int) =
      a = 1
      a = c + a
    h(c)
    check c == 2
    var t = (a: 1, b: 1)
    let s1 = setOne
    s1(t.a)
    check t.a == 4
    let o: Shape = Square()
    o.setM(x)
    check x == 6

  test "a proc-valued variable":
    ## RED: `sxSat` (a false one) -- the var writes were dropped.
    discard clean(sutPV, "pv_dead", sxUnsat)
    discard clean(sutPV, "pv", sxSat)

  test "one variable passed twice":
    discard clean(sutPVSame, "pvs_dead", sxUnsat)
    discard clean(sutPVSame, "pvs", sxSat)

  test "a lambda":
    discard clean(sutLam, "lam_dead", sxUnsat)
    discard clean(sutLam, "lam", sxSat)
    discard clean(sutLamCap, "lc_dead", sxUnsat)
    discard clean(sutLamCap, "lc", sxSat)

  test "a generic callee's proc parameter":
    discard clean(sutGen, "gen_dead", sxUnsat)
    discard clean(sutGen, "gen", sxSat)

  test "a proc passed to a callee":
    discard clean(sutHof, "hof_dead", sxUnsat)
    discard clean(sutHof, "hof", sxSat)

  test "a call in an expression":
    discard clean(sutExpr, "ex_dead", sxUnsat)
    discard clean(sutExpr, "ex", sxSat)

  test "a call under a branch":
    discard clean(sutCond, "cd_dead", sxUnsat)
    discard clean(sutCond, "cd2_dead", sxUnsat)
    discard clean(sutCond, "cd", sxSat)

  test "a write before a raise":
    discard clean(sutRaise, "rs_dead", sxUnsat)
    discard clean(sutRaise, "rs", sxSat)
    discard clean(sutRaise, "rs2_dead", sxUnsat)

  test "a field of a value tuple":
    discard clean(sutField, "vf_dead", sxUnsat)
    discard clean(sutField, "vf", sxSat)

  test "a heap actual":
    discard clean(sutHeap, "h_dead", sxUnsat)
    discard clean(sutHeap, "h", sxSat)

  test "two heap actuals through different refs (S8bf's peers)":
    discard clean(sutHeapPeers, "hp_dead", sxUnsat)
    discard clean(sutHeapPeers, "hp", sxSat)
    discard clean(sutHeapParams, "hq_dead", sxUnsat)
    discard clean(sutHeapParams, "hq_same", sxSat)
    discard clean(sutHeapParams, "hq_diff", sxSat)
    discard clean(sutHeapParams, "hq_diff_dead", sxUnsat)
    discard clean(sutHeapFresh, "hf_dead", sxUnsat)
    discard clean(sutHeapFresh, "hf", sxSat)

  test "addr actuals":
    ## Before S8bh: `feUnsupportedExprKind` (`nnkAddr`), a decline.
    discard clean(sutAddr, "ad_dead", sxUnsat)
    discard clean(sutAddr, "ad", sxSat)
    discard clean(sutAddrSame, "as_dead", sxUnsat)
    discard clean(sutAddrSame, "as", sxSat)
    discard clean(sutAddrPeers, "ap_dead", sxUnsat)
    discard clean(sutAddrPeers, "ap", sxSat)

  test "an actual that is also the closure's capture declines":
    declines(sutCapAlias, "ca_dead", ceCaptureByRefUnmodelled, "`c`")

  test "an unknown target declines, and its effects are havocked":
    declines(sutUnknown, "uk", ceClosureUnknownCallee, "`f`")
    declines(sutUnknown, "uk_moved", ceClosureUnknownCallee, "`f`")
    declines(sutUnknownHeap, "ukh_moved", ceClosureUnknownCallee, "`f`")

  test "a heap actual the body reaches through a capture declines":
    declines(sutHeapCapture, "hc_dead", feUnsupportedOp, "outside its formals")
    discard clean(sutHeapCaptureOther, "hco_dead", sxUnsat)
    discard clean(sutHeapCaptureOther, "hco", sxSat)

  test "an addr actual whose pointer may escape declines":
    declines(sutAddrEscape, "ae_dead", feUnsupportedOp, "escape the call")

  test "a proc field and a method call are walked (S8bn)":
    ## They declined at S8bh; S8bn (item 6) walks a call through a proc
    ## field and dispatches a method call on the run-type tag.
    discard clean(sutProcField, "pfld_dead", sxUnsat)
    discard clean(sutMethod, "m_dead", sxUnsat)

# ---- 2. a ptr of unknown origin --------------------------------------------
#
# RFC-0005 S8bh item 2. A `ptr T` the SUT is handed (a parameter, a global,
# a field it reads) addressed only its own `ptr`-family cells: never a ref
# object's field, a global or a `var` parameter of type T, which Nim
# reaches with `addr q.x`, `addr g`, `addr v`.

type PQ = ref object
  x: int
  s: string
  b: bool

var gPI: int
var gPS: seq[int]

proc sutPField(q: PQ; pi: ptr int) =
  if q == nil or pi == nil: return
  q.x = 1
  pi[] = 2
  if q.x == 2: symexTarget("pfi")
  if q.x != 1 and q.x != 2: symexTarget("pfi_dead")

proc sutPFieldRead(q: PQ; pi: ptr int) =
  ## A read through the pointer sees the field's write.
  if q == nil or pi == nil: return
  pi[] = 5
  q.x = 7
  if pi[] == 7: symexTarget("pfr")

proc sutPString(q: PQ; ps: ptr string) =
  if q == nil or ps == nil: return
  q.s = "a"
  ps[] = "b"
  if q.s == "b": symexTarget("pfs")

proc sutPBoolDisjoint(q: PQ; pi: ptr int) =
  ## Control: an `int` pointer never addresses a `bool` field.
  if q == nil or pi == nil: return
  q.b = true
  pi[] = 0
  if not q.b: symexTarget("pfb_dead")

proc sutPFresh(pi: ptr int) =
  ## Control: the pointer predates an object the SUT allocates.
  if pi == nil: return
  let q = PQ(x: 1)
  pi[] = 2
  if q.x != 1: symexTarget("pfn_dead")

proc sutPGlobal(pi: ptr int) =
  if pi == nil: return
  gPI = 1
  pi[] = 2
  if gPI == 2: symexTarget("pg")
  if gPI != 1 and gPI != 2: symexTarget("pg_dead")

proc sutPVar(v: var int; pi: ptr int) =
  if pi == nil: return
  v = 1
  pi[] = 2
  if v == 2: symexTarget("pv2")
  if v != 1 and v != 2: symexTarget("pv2_dead")

proc sutPLocal(pi: ptr int) =
  ## Control: a local's address is never the caller's.
  if pi == nil: return
  var x = 1
  pi[] = 2
  if x != 1: symexTarget("pl_dead")

proc writeVia(pi: ptr int) =
  pi[] = 9

proc sutPCallee(q: PQ; pi: ptr int) =
  ## The write is in a callee.
  if q == nil or pi == nil: return
  q.x = 1
  writeVia(pi)
  if q.x == 9: symexTarget("pc")

proc bumpVia(v: var int; pi: ptr int) =
  v = 1
  pi[] = 2

proc sutPVarFormal(pi: ptr int) =
  ## A callee's `var` formal: a scoped decline (the walk copies it in and
  ## out, and the pointer may address its actual).
  if pi == nil: return
  var x = 0
  bumpVia(x, pi)
  if x == 1: symexTarget("pvf")

proc sutPSeqGlobal(pi: ptr int) =
  ## A global seq's element: a scoped decline.
  if pi == nil: return
  gPS = @[1]
  pi[] = 2
  if gPS[0] == 2: symexTarget("psg")

suite "S8bh (2): a ptr of unknown origin":

  test "nim":
    let q = PQ(x: 0)
    sutPField(q, addr q.x)
    check q.x == 2
    sutPGlobal(addr gPI)
    check gPI == 2
    var v = 0
    sutPVar(v, addr v)
    check v == 2

  test "a ptr parameter may address a ref object's field":
    ## RED: `sxUnsat` (a false one).
    let r = clean(sutPField, "pfi", sxSat)
    if r.status == sxSat:
      # The snapshot aims the pointer at the field (`"&<cell>.<field>"`),
      # and the typed witness hands it the field's address.
      var aimed = false
      for e in r.heapSnapshot:
        if e.name == "pi" and e.aliasRef == some("&q.x"): aimed = true
      check aimed
      check replayWitness(sutPField, r.witness, tLabel("pfi"), {}) ==
        roConfirmed
    discard clean(sutPField, "pfi_dead", sxUnsat)
    discard clean(sutPFieldRead, "pfr", sxSat)
    discard clean(sutPString, "pfs", sxSat)
    discard clean(sutPCallee, "pc", sxSat)

  test "disjoint controls":
    discard clean(sutPBoolDisjoint, "pfb_dead", sxUnsat)
    discard clean(sutPFresh, "pfn_dead", sxUnsat)
    discard clean(sutPLocal, "pl_dead", sxUnsat)

  test "a ptr parameter may address a global or a var parameter":
    ## RED: `sxUnsat` (false ones).
    discard clean(sutPGlobal, "pg", sxSat)
    discard clean(sutPGlobal, "pg_dead", sxUnsat)
    discard clean(sutPVar, "pv2", sxSat)
    discard clean(sutPVar, "pv2_dead", sxUnsat)

  test "a by-value aggregate global declines":
    ## S8bn (item 4): a seq element is a target now, but `gPS = @[1]`
    ## replaced the seq the pointer may have addressed: it may dangle.
    declines(sutPSeqGlobal, "psg", feUnsupportedOp, "may dangle")
    ## S8bn (item 3): `x` is a local whose address is never taken, so the
    ## pointer cannot address the formal's actual.
    discard clean(sutPVarFormal, "pvf", sxSat)

# ---- 3. a ref converted along its inheritance chain -------------------------
#
# RFC-0005 S8bh item 3. Every type of a hierarchy keyed its own `Ref_<id>`
# sort and its own field heaps, and a derived type's IR carried only the
# fields it declared itself. `Base(d)`, `let b: Base = d` and a `Base`
# parameter aliasing a `Mid` one therefore mixed two sorts (an ill-sorted
# term, `weInternalWalkerFault`), or read an inherited field from a heap the
# other static type never wrote (a false `sxUnsat`).

type
  Base3 = ref object of RootObj
    x: int
  Mid3 = ref object of Base3
    y: int
  Leaf3 = ref object of Mid3
    z: int
  Side3 = ref object of Base3
    y: string   ## a sibling's field of the same name and another type

proc sutCvEq(b: Base3; d: Mid3) =
  if Base3(d) == b and d != nil: symexTarget("cv")

proc sutCvLocal(k: int) =
  let d = Mid3(x: k, y: k)
  let b: Base3 = d
  if Base3(d) == b: symexTarget("cvl")
  if Base3(d) != b: symexTarget("cvl_dead")

proc sutCvField(k: int) =
  ## `setBoth(Base(d).x, b.x)`: one location passed twice.
  let d = Mid3(x: k, y: k)
  let b: Base3 = d
  setBoth(Base3(d).x, b.x)
  if d.x != 1: symexTarget("cvf_dead")
  if d.x == 1 and k == 3: symexTarget("cvf")

proc sutAliasParams(b: Base3; d: Mid3) =
  ## `b` and `d` may be one object (`sutAliasParams(m, m)`).
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2: symexTarget("apar")
  if d.x != 1 and d.x != 2: symexTarget("apar_dead")

proc sutAliasDisjoint(b: Base3; d: Mid3) =
  ## Control: two fresh objects never alias.
  let m = Mid3(x: 1)
  let n: Base3 = Base3(x: 5)
  n.x = 2
  if m.x != 1: symexTarget("adis_dead")

proc sutInheritedZero(k: int) =
  ## `Mid3()` zeroes the inherited `x` as well as its own `y`.
  let d = Mid3()
  if d.x != 0 or d.y != 0: symexTarget("iz_dead")
  if d.x == 0: symexTarget("iz")

proc sutUpRead(k: int) =
  let d = Mid3(x: k, y: 7)
  d.x = 3
  let b: Base3 = d
  if b.x != 3 or d.y != 7: symexTarget("ur_dead")
  b.x = 4
  if d.x == 4: symexTarget("ur")

proc sutSiblings(k: int) =
  ## `Mid3.y` and `Side3.y` are different fields.
  let s = Side3(x: k, y: "a")
  let m = Mid3(x: k, y: 3)
  if m.y != 3 or s.y != "a": symexTarget("sib_dead")
  if m.y == 3 and s.y == "a": symexTarget("sib")

proc sutDown(k: int) =
  let b: Base3 = Mid3(x: k, y: 4)
  let d = Mid3(b)
  if d.y != 4: symexTarget("dn_dead")
  if d.y == 4: symexTarget("dn")

proc sutDownLeaf(k: int) =
  ## A `Leaf3` is a `Mid3`.
  try:
    let b: Base3 = Leaf3(x: k, y: 4, z: 1)
    let d = Mid3(b)
    if d.y == 4: symexTarget("dl")
  except ObjectConversionDefect:
    symexTarget("dl_raise_dead")

proc sutDownFail(k: int) =
  ## A plain `Base3` is not a `Mid3`: ObjectConversionDefect.
  try:
    let b = Base3(x: k)
    let d = Mid3(b)
    if d.y == 0: symexTarget("dnf_dead")
  except ObjectConversionDefect:
    symexTarget("dnf_raise")

proc sutDownSide(k: int) =
  ## Nor is a sibling.
  try:
    let b: Base3 = Side3(x: k, y: "s")
    discard Mid3(b)
    symexTarget("dns_dead")
  except ObjectConversionDefect:
    symexTarget("dns_raise")

proc sutDownNil(b: Base3) =
  ## A nil converts: Nim checks a non-nil ref only.
  if b != nil: return
  try:
    let d = Mid3(b)
    if d == nil: symexTarget("dnn")
  except ObjectConversionDefect:
    symexTarget("dnn_raise_dead")

proc sutParamDown(b: Base3) =
  ## A parameter's dynamic type is any subtype of its static one.
  try:
    let d = Mid3(b)
    if d != nil: symexTarget("pdn")
  except ObjectConversionDefect:
    symexTarget("pdn_raise")

type
  BaseObj4 = object of RootObj
    x: int
  BaseR4 = ref BaseObj4
  DerObj4 = object of BaseObj4
    y: int
  DerR4 = ref DerObj4

proc sutObjStyle(b: BaseR4; d: DerR4) =
  ## The `ref Obj` spelling of a hierarchy (its nominal ids are the
  ## objects').
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2 and BaseR4(d) == b: symexTarget("os")
  if d.x != 2 and BaseR4(d) == b: symexTarget("os_dead")
  let e = DerR4(x: 3)
  if e.y != 0: symexTarget("os_zero_dead")
  try:
    discard DerR4(BaseR4(x: 1))
    symexTarget("os_down_dead")
  except ObjectConversionDefect:
    discard

suite "S8bh (3): a ref converted along its inheritance chain":

  test "nim":
    let m = Mid3(x: 1, y: 2)
    check Base3(m) == Base3(m)
    sutAliasParams(m, m)
    check m.x == 2
    expect ObjectConversionDefect:
      discard Mid3(Base3(x: 1))
    expect ObjectConversionDefect:
      discard Mid3(Base3(Side3()))
    check Mid3(Base3(Leaf3(y: 4))).y == 4
    check Mid3(Base3(nil)) == nil
    check Mid3().x == 0

  test "an up-conversion keeps the ref's identity":
    ## RED: `weInternalWalkerFault` (an ill-sorted term).
    let r = clean(sutCvEq, "cv", sxSat)
    if r.status == sxSat:
      check replayWitness(sutCvEq, r.witness, tLabel("cv"), {}) == roConfirmed
    discard clean(sutCvLocal, "cvl", sxSat)
    discard clean(sutCvLocal, "cvl_dead", sxUnsat)

  test "one location reached through two static types":
    ## RED: `sxRaised` (the ill-sorted index of a field heap).
    discard clean(sutCvField, "cvf_dead", sxUnsat)
    discard clean(sutCvField, "cvf", sxSat)
    discard clean(sutUpRead, "ur_dead", sxUnsat)
    discard clean(sutUpRead, "ur", sxSat)

  test "parameters of two static types may alias":
    ## RED: `sxUnsat` (a false one) -- two sorts never meet.
    let r = clean(sutAliasParams, "apar", sxSat)
    if r.status == sxSat:
      check replayWitness(sutAliasParams, r.witness, tLabel("apar"), {}) ==
        roConfirmed
    discard clean(sutAliasParams, "apar_dead", sxUnsat)
    discard clean(sutAliasDisjoint, "adis_dead", sxUnsat)

  test "a derived object's inherited fields are zeroed and distinct":
    discard clean(sutInheritedZero, "iz_dead", sxUnsat)
    discard clean(sutInheritedZero, "iz", sxSat)
    discard clean(sutSiblings, "sib_dead", sxUnsat)
    discard clean(sutSiblings, "sib", sxSat)

  test "a down-conversion checks the dynamic type":
    discard clean(sutDown, "dn_dead", sxUnsat)
    discard clean(sutDown, "dn", sxSat)
    discard clean(sutDownLeaf, "dl", sxSat)
    discard clean(sutDownLeaf, "dl_raise_dead", sxUnsat)
    ## RED: `sxRaised` (the walker never raised ObjectConversionDefect).
    discard clean(sutDownFail, "dnf_dead", sxUnsat)
    discard clean(sutDownFail, "dnf_raise", sxSat)
    discard clean(sutDownSide, "dns_dead", sxUnsat)
    discard clean(sutDownSide, "dns_raise", sxSat)
    discard clean(sutDownNil, "dnn", sxSat)
    discard clean(sutDownNil, "dnn_raise_dead", sxUnsat)

  test "the `ref Obj` spelling of a hierarchy":
    let r = clean(sutObjStyle, "os", sxSat)
    if r.status == sxSat:
      check replayWitness(sutObjStyle, r.witness, tLabel("os"), {}) ==
        roConfirmed
    discard clean(sutObjStyle, "os_dead", sxUnsat)
    discard clean(sutObjStyle, "os_zero_dead", sxUnsat)
    discard clean(sutObjStyle, "os_down_dead", sxUnsat)

  test "a parameter's down-conversion may go either way":
    let r = clean(sutParamDown, "pdn_raise", sxSat)
    if r.status == sxSat:
      check replayWitness(sutParamDown, r.witness, tLabel("pdn_raise"), {}) ==
        roConfirmed
    discard clean(sutParamDown, "pdn", sxSat)

suite "S8bh: walker version":
  test "symexWalkerVersion >= 208":
    check parseInt(symexWalkerVersion) >= 208
