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
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

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

  test "a proc field and a method call decline":
    declines(sutProcField, "pfld_dead", feUnsupportedStmtKind, "o.f")
    declines(sutMethod, "m_dead", feUnsupportedOp, "setM")

suite "S8bh: walker version":
  test "symexWalkerVersion >= 208":
    check parseInt(symexWalkerVersion) >= 208
