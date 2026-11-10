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
##    question; a store to a variable by name is not `mayWrite`'s. It stays an
##    escape predicate (sharing `foreignWriteNode`/`opaqueRoutine`) and is now
##    fail-closed: an exhaustive `case`; its own verdict is pinned below.
##
## No SUT was found for which any of the three, as it stood, gave a false
## trusted verdict: each shape a probe built to slip past (an `addr` of a
## pointee's field, a `var` actual that returns its address, a `var c = t`, a
## `lent` result bound to a local, a tuple holding the container) either
## declined for another, earlier reason or was decided correctly. So these are
## precision pins: what each predicate must still prove, what it must still
## decline, each with a native run.
import std/[unittest, strutils, tables, sequtils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/dsl_parser
import std/macros
import ./s8cu_helpers

const ns = [-5, -1, 0, 1, 3, 4, 7, 12, 49, 51]

template nativeLiveI(fn: typed; lbl: static string; want: bool) =
  ## The declined shapes are not decided, so this native run is checked here;
  ## the decided ones are checked by `pinExact`'s witness and domain.
  block:
    var live = false
    for n in ns:
      if lbl in nativeRun(fn(n)).hits: live = true
    check live == want

template nativeLiveT(fn: typed; lbl: static string; want: bool) =
  block:
    var live = false
    for n in ns:
      if lbl in nativeRun(fn({"a": n}.toTable)).hits: live = true
    check live == want

template roDecided(fn: typed; want: SymexStatusKind; lbl: static string;
                   cell: static string; dom: untyped = boundaryInts) =
  ## The route proves the shape read-only: the walker decides the label and the
  ## native run agrees (the witness hits, or no domain value does).
  block:
    let r = pinExact(fn, cellKey(axReadOnly, cell), tLabel(lbl), dom)
    check r.status == want

template roDeclined(fn: typed; kind: SymexErrorKind; lbl: static string;
                    cell: static string; why: static string) =
  pinDecline(fn, cellKey(axReadOnly, cell), kind, tLabel(lbl), needle = why)

# Every input of interest: `guardT` returns before any label for a table that is
# not the single key "a" with a value in -1000 .. 1000.
let tableDom = exhaustive(toSeq(-1000 .. 1000).mapIt({"a": it}.toTable))

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
  test "walker 299 or later":
    check parseInt(symexWalkerVersion) >= 299

suite "K6c: routeStoresThroughDeref is mayWrite":
  test "native: the hooks store through the ref, the plain ones do not":
    nativeLiveI(store1, "store1_stored", true)
    nativeLiveI(call1, "call1_stored", true)
    nativeLiveI(plain1, "plain1_stored", false)
    nativeLiveI(work1, "work1_stored", false)
  test "a hook storing through a global ref declines":
    roDeclined(store1, feGlobalRouteUnproved, "store1_stored",
               "hookstore/direct-store", "may store through a `ref` or a `ptr`")
  test "a hook whose walked callee stores through a ref declines":
    roDeclined(call1, feGlobalRouteUnproved, "call1_stored",
               "hookstore/walked-store", "may store through a `ref` or a `ptr`")
  test "a plain copy is decided":
    roDecided(plain1, sxUnsat, "plain1_stored", "hookstore/plain")
    roDecided(plain1, sxSat, "plain1_clean", "hookstore/plain")
  test "local work around the copy is decided":
    roDecided(work1, sxUnsat, "work1_stored", "hookstore/local-work")
    roDecided(work1, sxSat, "work1_clean", "hookstore/local-work")

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
    roDeclined(sHoldVar, feUnsupportedOp, "hv_shared", "viewwhole/var-copy",
               "holding the whole of one")
  test "a `lent` loop over the whole declines":
    roDeclined(sHoldLoop, feUnsupportedOp, "hl_shared", "viewwhole/lent-loop",
               "holding the whole of one")
  test "a scalar read out of the container is decided (precision)":
    # The route lets it through (sat), but the loop is over a `Table`'s
    # `mpairs`, whose order is not modelled: the verdict is untrusted, so the
    # cell declines with `feTableIterOrder` and is pinned as a decline.
    check symexFind(sHoldNone, tLabel("hn_shared")).status == sxSat
    roDeclined(sHoldNone, feTableIterOrder, "hn_shared",
               "viewwhole/scalar-read", "")
  test "a tuple built from the container is a copy (precision)":
    roDecided(sHoldTuple, sxUnsat, "ht_shared", "viewwhole/tuple-copy", tableDom)

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

# The predicate's own verdict, asked of a callee's `ptr` formal. The two
# misjudged shapes decline in `symexFind` for another, earlier reason
# (`feUnsupportedExprKind` on `nnkAddr`), so the reason string cannot show the
# predicate: this is the focused test (the internal-test style of
# `tsymex_0016_k4a_table`, which imports `dsl_parser`).
macro formalStaysLocal(fn: typed; idx: static int): untyped =
  var seen: seq[string]
  newLit(ptrFormalStaysLocal(fn, idx, seen))

proc extSink(p: ptr int) {.importc: "extSink_k6c", cdecl.}
proc bumpV(x: var int) = x += 1
proc viaOpaque(p: ptr int) = extSink(p)
proc viaBump(p: ptr int) = bumpV(p[])
proc viaInc(p: ptr int) = inc p[]
proc cmpOnly(p: ptr int): bool = p != nil and p[] > 0
proc retAddr(p: ptr Pr): ptr int = addr p[].b
proc retWhole(p: ptr int): ptr int = p

suite "K6c: ptrUsesStayLocal (the predicate itself)":
  test "an address through a dereference escapes, independent of the expr gate":
    check not formalStaysLocal(keepFld, 0)
    check not formalStaysLocal(retAddr, 0)
  test "a pointee passed `var` to a callee returning its address escapes":
    check not formalStaysLocal(keepViaVar, 0)
  test "the pointer stored or returned escapes":
    check not formalStaysLocal(keepWhole, 0)
    check not formalStaysLocal(retWhole, 0)
  test "the pointer flowing into an opaque routine escapes":
    check not formalStaysLocal(viaOpaque, 0)
  test "local uses stay local (precision)":
    check formalStaysLocal(setTwo, 0)
    check formalStaysLocal(setTwo, 1)
    check formalStaysLocal(viaBump, 0)
    check formalStaysLocal(viaInc, 0)
    check formalStaysLocal(cmpOnly, 0)

suite "K6c: ptrUsesStayLocal":
  test "native: an escaped pointer writes the variable later":
    nativeLiveI(sFld, "pf_live", true)
    nativeLiveI(sVia, "pv_live", true)
    nativeLiveI(sWhole, "pw_live", true)
    nativeLiveI(sWhole, "pw_dead", false)
    nativeLiveI(sLocal, "pl_live", true)
    nativeLiveI(sLocal, "pl_dead", false)
  test "a pointer that stays local is a cell (precision)":
    roDecided(sLocal, sxSat, "pl_live", "ptrformal/local")
    roDecided(sLocal, sxUnsat, "pl_dead", "ptrformal/local")
  test "a pointer stored in a global is decided by the escape":
    roDecided(sWhole, sxSat, "pw_live", "ptrformal/global-store")
    roDecided(sWhole, sxUnsat, "pw_dead", "ptrformal/global-store")
  test "the address of a pointee's field, stored, is not decided":
    roDeclined(sFld, feUnsupportedExprKind, "pf_live", "ptrformal/field-addr", "")
  test "a pointee passed as `var` to a callee returning its address is not decided":
    roDeclined(sVia, feUnsupportedExprKind, "pv_live", "ptrformal/var-return", "")
