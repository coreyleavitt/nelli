## RFC-0016 K6c (W-10) -- `ptrUsesStayLocal`, `routeStoresThroughDeref` and
## `bindsViewWhole`.
##
## Each of the three made its own write/escape judgement in a denylist shape
## (D-05: one rule). K6c rebuilds them:
##
##  * `routeStoresThroughDeref` (a lifetime hook may store through a `ref` or a
##    `ptr`) IS `mayWrite`'s question and is now `routineMayWrite` -- the one
##    rule K6a built. The stdlib-argument rule of `mayWrite` takes the union of
##    the two scans it replaces (`argHoldsCell`: a `ptr`, a `ref` or a proc in any
##    part of the argument).
##  * `bindsViewWhole` (a callee holding the memory of a container) is a question
##    about aliasing, not writing, over the IR: its `else: discard` is now an
##    exhaustive `case`, so a statement kind added later must decide.
##  * `ptrUsesStayLocal` (a pointer does not outlive the call) is an escape
##    question; a store to a variable by name is not `mayWrite`'s. It is left as
##    it was.
##
## No SUT was found for which any of the three, as it stood, gave a false
## trusted verdict: each shape a probe built to slip past (an `addr` of a
## pointee's field, a `var` actual that returns its address, a `var c = t`, a
## `lent` result bound to a local, a tuple holding the container) either
## declined for another, earlier reason or was decided correctly. So these are
## precision pins: what each predicate must still prove, what it must still
## decline, each with a native run.
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template nativeLiveI(fn: typed; lbl: static string; want: bool) =
  block:
    var live = false
    for n in ns:
      if lbl in hits(fn(n)): live = true
    check live == want

template nativeLiveT(fn: typed; lbl: static string; want: bool) =
  block:
    var live = false
    for n in ns:
      if lbl in hits(fn({"a": n}.toTable)): live = true
    check live == want

template statusIs(fn: typed; lbl: static string; want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == want

template declinedWith(fn: typed; lbl: static string; why: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check why in show(r.errors)

# ---- routeStoresThroughDeref --------------------------------------------------

type
  RCell = ref object
    v: int
  StoreC = object
    v: int
    r: RCell
  CallC = object
    v: int
    r: RCell
  PlainC = object
    v: int
  WorkC = object
    v: int

proc bump(c: RCell) = c.v = 5
proc pureAdd(a, b: int): int = a + b

proc `=copy`(a: var StoreC; b: StoreC) =
  a.v = b.v
  a.r = b.r
  b.r.v = 5
proc `=copy`(a: var CallC; b: CallC) =
  a.v = b.v
  a.r = b.r
  bump(b.r)
proc `=copy`(a: var PlainC; b: PlainC) =
  a.v = b.v
proc `=copy`(a: var WorkC; b: WorkC) =
  var t = pureAdd(b.v, 1)
  if t > 3: t = t - 1
  a.v = b.v
  discard t

template storeShape(name: untyped; T: typedesc; lbl: static string) =
  proc name(k: int) =
    var c = RCell(v: 0)
    var x = T(v: k, r: c)
    var y = x
    x.v = 0
    if c.v != 0 and y.v == k: symexTarget(lbl & "_stored")

template plainShape(name: untyped; T: typedesc; lbl: static string) =
  proc name(k: int) =
    var x = T(v: k)
    var y = x
    x.v = 0
    if y.v != k: symexTarget(lbl & "_stored")
    if y.v == k: symexTarget(lbl & "_clean")

storeShape(store1, StoreC, "store1")
storeShape(call1, CallC, "call1")
plainShape(plain1, PlainC, "plain1")
plainShape(work1, WorkC, "work1")

suite "K6c: version floor":
  test "walker 293 or later":
    check parseInt(symexWalkerVersion) >= 293

suite "K6c: routeStoresThroughDeref is mayWrite":
  test "native: the hooks store through the ref, the plain ones do not":
    nativeLiveI(store1, "store1_stored", true)
    nativeLiveI(call1, "call1_stored", true)
    nativeLiveI(plain1, "plain1_stored", false)
    nativeLiveI(work1, "work1_stored", false)
  test "a hook storing through a global ref declines":
    declinedWith(store1, "store1_stored", "may store through a `ref` or a `ptr`")
  test "a hook whose walked callee stores through a ref declines":
    declinedWith(call1, "call1_stored", "may store through a `ref` or a `ptr`")
  test "a plain copy is decided":
    statusIs(plain1, "plain1_stored", sxUnsat)
    statusIs(plain1, "plain1_clean", sxSat)
  test "local work around the copy is decided":
    statusIs(work1, "work1_stored", sxUnsat)
    statusIs(work1, "work1_clean", sxSat)

# ---- bindsViewWhole -----------------------------------------------------------

template guardT(): untyped {.dirty.} =
  if t0.len != 1 or "a" notin t0: return
  let x = t0["a"]
  if x > 1000 or x < -1000: return

proc holdVar(v: var int; t: Table[string, int]; k: string): int =
  var c = t   # a cursor when never mutated
  v = 77
  c[k]
proc sHoldVar(t0: Table[string, int]) =
  guardT()
  if x == 77: return
  var t = t0
  for k, v in t.mpairs:
    if holdVar(v, t, k) == 77: symexTarget("hv_shared")

proc holdLoop(v: var int; t: Table[string, int]; k: string): int =
  var r = 0
  for w in t.values:   # `lent`: reads the element live
    v = 77
    r = w
  r
proc sHoldLoop(t0: Table[string, int]) =
  guardT()
  if x == 77: return
  var t = t0
  for k, v in t.mpairs:
    if holdLoop(v, t, k) == 77: symexTarget("hl_shared")

proc holdTuple(v: var int; t: Table[string, int]; k: string): int =
  let c = (a: t, b: 1)   # a tuple constructor copies
  v = 77
  c.a[k]
proc sHoldTuple(t0: Table[string, int]) =
  guardT()
  if x == 77: return
  var t = t0
  for k, v in t.mpairs:
    if holdTuple(v, t, k) == 77: symexTarget("ht_shared")

proc holdNone(v: var int; t: Table[string, int]; k: string): int =
  let c = t.getOrDefault("zz")   # a scalar, not the container
  v = 77
  t[k] + c
proc sHoldNone(t0: Table[string, int]) =
  guardT()
  if x == 77: return
  var t = t0
  for k, v in t.mpairs:
    if holdNone(v, t, k) == 77: symexTarget("hn_shared")

suite "K6c: bindsViewWhole":
  test "native: a scalar read after the write sees it, a copy does not":
    nativeLiveT(sHoldNone, "hn_shared", true)
    nativeLiveT(sHoldLoop, "hl_shared", true)
    nativeLiveT(sHoldTuple, "ht_shared", false)
    nativeLiveT(sHoldVar, "hv_shared", false)
  test "a `var` copy of the whole declines":
    declinedWith(sHoldVar, "hv_shared", "holding the whole of one")
  test "a `lent` loop over the whole declines":
    declinedWith(sHoldLoop, "hl_shared", "holding the whole of one")
  test "a scalar read out of the container is decided (precision)":
    statusIs(sHoldNone, "hn_shared", sxSat)
  test "a tuple built from the container is a copy (precision)":
    statusIs(sHoldTuple, "ht_shared", sxUnsat)

# ---- ptrUsesStayLocal ---------------------------------------------------------

type Pr = object
  a: int
  b: int

var gq: ptr int

proc leakVar(x: var int): ptr int = addr x
proc keepFld(p: ptr Pr) = gq = addr p[].a
proc keepViaVar(p: ptr int) = gq = leakVar(p[])
proc keepWhole(p: ptr int) = gq = p
proc setTwo(p, q: ptr int; v: int) =
  p[] = v
  q[] = 3

proc sLocal(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var x = 1
  setTwo(addr x, addr x, v)
  if x == 3: symexTarget("pl_live")
  if x == v and v != 3: symexTarget("pl_dead")
proc sFld(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var x = Pr(a: 1, b: 2)
  keepFld(addr x)
  gq[] = v
  if x.a == v and v != 1: symexTarget("pf_live")
proc sVia(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var x = 1
  keepViaVar(addr x)
  gq[] = v
  if x == v and v != 1: symexTarget("pv_live")
proc sWhole(v: int) =
  symexAssume(v > -1000 and v < 1000)
  var x = 1
  keepWhole(addr x)
  gq[] = v
  if x == v and v != 1: symexTarget("pw_live")
  if x == 1 and v != 1: symexTarget("pw_dead")

suite "K6c: ptrUsesStayLocal":
  test "native: an escaped pointer writes the variable later":
    nativeLiveI(sFld, "pf_live", true)
    nativeLiveI(sVia, "pv_live", true)
    nativeLiveI(sWhole, "pw_live", true)
    nativeLiveI(sWhole, "pw_dead", false)
    nativeLiveI(sLocal, "pl_live", true)
    nativeLiveI(sLocal, "pl_dead", false)
  test "a pointer that stays local is a cell (precision)":
    statusIs(sLocal, "pl_live", sxSat)
    statusIs(sLocal, "pl_dead", sxUnsat)
  test "a pointer stored in a global is decided by the escape":
    statusIs(sWhole, "pw_live", sxSat)
    statusIs(sWhole, "pw_dead", sxUnsat)
  test "the address of a pointee's field, stored, is not decided":
    statusIs(sFld, "pf_live", sxUnknown)
  test "a pointee passed as `var` to a callee returning its address is not decided":
    statusIs(sVia, "pv_live", sxUnknown)
