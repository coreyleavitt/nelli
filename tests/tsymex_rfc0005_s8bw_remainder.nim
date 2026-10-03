## RFC-0005 (soundness channels) slice S8bw -- S8bn's remainder.
##
## Item 1 is a SOUNDNESS finding (a crash class): a module-level global read
## before any write lowered to an `int` stand-in whatever its type, and the
## receiver checks it then reached were `doAssert`s or direct env lookups,
## reported as `weInternalWalkerFault`; an unbound object's discriminator
## reassignment was dropped, a false `sxSat`. Items 2-3 are PRECISION
## findings: declines where a finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
import std/[unittest, strutils, tables, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

template confirmed(fn: typed, lbl: string): untyped =
  ## A sound `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

template inBand(fn: typed, lbl: string, ek: SymexErrorKind,
                needle: string): untyped =
  ## A decline, named, and never a walker fault.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == ek and needle in e.msg: named = true
    check named

# ---- 1. a global's receiver never faults the walker --------------------------
#
# RFC-0005 S8bw item 1. A global read before any write was an `int` stand-in
# (`lower`'s `iekVar` arm, no prototype in scope), and the array, seq and
# string operations that then received it asserted its kind or looked the
# name up in the env directly: `weInternalWalkerFault`. The stand-in is now
# a value of the global's declared type, and each receiver check declines
# in-band.

type
  VK1 = enum vkA, vkB
  V1 = object
    case kind: VK1
    of vkA: a: int
    of vkB: b: int
  OA1 = object
    arr: array[3, int]
    n: int

var gArr1: array[4, int]
var gSeq1: seq[int]
var gSeqPop1: seq[int]
var gSeqDel1: seq[int]
var gSeqAdd1: seq[int]
var gV1: V1
var gObjA1: OA1
var gStrs1: seq[string]
var gB1: bool

proc sutArrWrite(k: int) =
  gArr1[2] = k
  if gArr1[2] == 5: symexTarget("aw")

proc sutObjArrWrite(k: int) =
  gObjA1.arr[1] = k
  if gObjA1.arr[1] == 5: symexTarget("oaw")

proc sutSeqWrite(k: int) =
  gSeq1[0] = k
  if k == 5: symexTarget("sqw")

proc sutSeqPop(k: int) =
  discard gSeqPop1.pop()
  if k == 5: symexTarget("sqp")

proc sutSeqDel(k: int) =
  gSeqDel1.del(0)
  if k == 5: symexTarget("sqd")

proc sutSeqAdd(k: int) =
  gSeqAdd1.add k
  if gSeqAdd1[^1] == 5: symexTarget("sqa")

proc sutMap(k: int) =
  let ys = gSeq1.map(proc (x: int): int = x + 1)
  if k == 5 and ys.len == 0: symexTarget("map")

proc sutJoin(k: int) =
  if gStrs1.join(",") == "a" and k == 5: symexTarget("join")

proc sutBool(k: int) =
  if gB1 and k == 5: symexTarget("gb")

proc sutReassign(k: int) =
  ## Nim raises `FieldDefect` from the zero value's branch (`vkA`).
  gV1.kind = vkB
  if k == 5: symexTarget("vr")

proc sutReassignSym(k: int) =
  gV1.kind = (if k == 1: vkA else: vkB)
  if k == 5: symexTarget("vrs")

proc sutLocalGlobal(k: int) =
  ## A `{.global.}` local keeps its value from the previous call.
  var a {.global.}: array[3, int]
  a[1] = k
  if a[1] == 5: symexTarget("lg")

suite "S8bw (1): a global's receiver never faults the walker":

  test "nim":
    sutArrWrite(5)
    check gArr1[2] == 5
    gArr1 = default(array[4, int])
    sutObjArrWrite(5)
    check gObjA1.arr[1] == 5
    gObjA1 = default(OA1)
    expect FieldDefect:
      sutReassign(5)
    expect IndexDefect:
      sutSeqWrite(5)
    expect IndexDefect:
      sutSeqPop(5)

  test "an array global's element, written then read":
    ## RED: `weInternalWalkerFault` -- AssertionDefect `recv.kind ==
    ## svArray` (`iekIndex` on the `int` stand-in). Item 1 made it decline
    ## in-band; item 2 decides it.
    confirmed(sutArrWrite, "aw")
    confirmed(sutObjArrWrite, "oaw")

  test "a seq global's element write, pop, del and add":
    ## RED: `sqw` leaked its lowering taint to the walk end
    ## (`weInternalWalkerFault`); `sqp` was a `KeyError`.
    inBand(sutSeqWrite, "sqw", feGlobalReadUnmodelled, "gSeq1")
    inBand(sutSeqPop, "sqp", feGlobalReadUnmodelled, "gSeqPop1")
    inBand(sutSeqDel, "sqd", feGlobalReadUnmodelled, "gSeqDel1")
    inBand(sutSeqAdd, "sqa", feGlobalReadUnmodelled, "gSeqAdd1")

  test "a higher-order call, a join and a bool test on a global":
    ## RED: AssertionDefect `seqSV.kind == svSeq` (`map`) and `recv.kind ==
    ## svSeq` (`join`).
    inBand(sutMap, "map", feGlobalReadUnmodelled, "gSeq1")
    inBand(sutJoin, "join", feGlobalReadUnmodelled, "gStrs1")
    inBand(sutBool, "gb", feGlobalReadUnmodelled, "gB1")

  test "a {.global.} local":
    ## RED: the build failed ("node has no type": the name is a pragma
    ## expression). Its later reads take the unbound name's `int`
    ## stand-in, which `iekIndex` now declines in-band.
    inBand(sutLocalGlobal, "lg", feUnsupportedStmtKind, "{.global.}")

  test "a discriminator reassignment of an unwritten global":
    ## RED: a clean `sxSat` -- the reassignment was dropped, and Nim raises
    ## `FieldDefect` on it from the zero value's branch.
    inBand(sutReassign, "vr", feGlobalReadUnmodelled, "gV1")
    inBand(sutReassignSym, "vrs", feGlobalReadUnmodelled, "gV1")

# ---- 2. aggregate globals ------------------------------------------------------
#
# RFC-0005 S8bw item 2. A tuple, object or array global was
# `feGlobalReadUnmodelled` at its first partial write: `g.a = v` rebuilds `g`
# from `v` and copies of its other parts, and the copies read the unbound
# global. A global read before its first write now holds one unwritten
# constant per leaf of its declared type; a rebuild's copies carry them
# back, and only a read that observes one declines -- as a scalar global
# read before any write does.

type
  O2 = object
    x, y: int
  N2 = object
    inner: O2
    z: int

var gTup2: tuple[a, b: int]
var gTupW2: tuple[a, b: int]
var gTupV2: tuple[a, b: int]
var gObj2: O2
var gObjP2: O2
var gN2: N2
var gArr2: array[4, int]
var gArrS2: array[4, int]
var gArrR2: array[4, int]
var gArrU2: array[4, int]
var gI2: int

proc setV2(v: var int; x: int) = v = x
proc setP2(p: ptr int; x: int) = p[] = x
proc setB2() = gTupW2.b = 7

proc sutTupField(k: int) =
  gTup2.a = k
  if gTup2.a == 5: symexTarget("tf")
  if gTup2.a == 5 and k != 5: symexTarget("tf_dead")

proc sutTupUnwritten(k: int) =
  gTup2.a = k
  if gTup2.b == 5: symexTarget("tf_unwritten")

proc sutTupWhole(k: int) =
  gTup2.a = k
  let t = gTup2
  if t.a == 5: symexTarget("tw")

proc sutObjFields(k: int) =
  gObj2.x = k
  gObj2.y = 1
  let o = gObj2
  if o.x == 5 and o.y == 1: symexTarget("of")
  if o.y != 1: symexTarget("of_dead")

proc sutNested(k: int) =
  gN2.inner.x = k
  if gN2.inner.x == 5: symexTarget("nf")
  if gN2.inner.x == 5 and k != 5: symexTarget("nf_dead")

proc sutNestedUnwritten(k: int) =
  gN2.inner.x = k
  if gN2.z == 5: symexTarget("nf_unwritten")

proc sutArrConst(k: int) =
  gArr2[2] = k
  if gArr2[2] == 5: symexTarget("ac")
  if gArr2[2] == 5 and k != 5: symexTarget("ac_dead")

proc sutArrConstUnwritten(k: int) =
  gArr2[2] = k
  if gArr2[1] == 5: symexTarget("ac_unwritten")

proc sutArrSym(k: int) =
  if k < 0 or k > 3: return
  gArrS2[k] = 5
  if gArrS2[k] == 5: symexTarget("as")
  if gArrS2[k] != 5: symexTarget("as_dead")

proc sutArrSymUnwritten(k: int) =
  if k < 0 or k > 3: return
  gArrS2[k] = 5
  if gArrS2[(k + 1) mod 4] == 5: symexTarget("as_unwritten")

proc sutArrRead(k: int) =
  for i in 0 .. 3: gArrR2[i] = i + 1
  if k >= 0 and k < 4 and gArrR2[k] == 3: symexTarget("ar")
  if k >= 0 and k < 4 and gArrR2[k] == 9: symexTarget("ar_dead")

proc sutVarParam(k: int) =
  gTupV2.a = 0
  setV2(gTupV2.a, k)
  if gTupV2.a == 5: symexTarget("vp")

proc sutVarUnwritten(k: int) =
  ## The `var` actual is copied in: a read, as for a scalar global.
  setV2(gArrU2[3], k)
  if gArrU2[3] == 5: symexTarget("vu")

proc sutAddr(k: int) =
  gObjP2.x = 0
  setP2(addr gObjP2.x, k)
  if gObjP2.x == 5: symexTarget("ad")
  let p = addr gObjP2.y
  p[] = k + 1
  if gObjP2.y == 6: symexTarget("ad_let")

proc sutCallee(k: int) =
  gTupW2.a = k
  setB2()
  if gTupW2.b == 7 and gTupW2.a == 5: symexTarget("cw")
  if gTupW2.b != 7: symexTarget("cw_dead")

proc sutScalar(k: int) =
  if gI2 == k: symexTarget("sc")

suite "S8bw (2): aggregate globals":

  test "nim":
    sutTupField(5)
    check gTup2.a == 5
    sutArrSym(2)
    check gArrS2[2] == 5
    sutVarParam(5)
    check gTupV2.a == 5
    sutAddr(5)
    check gObjP2.y == 6

  test "a field of a tuple, an object and a nested object":
    ## RED: sxUnknown, `feGlobalReadUnmodelled` -- the rebuild's copy of
    ## the other field read the unbound global.
    confirmed(sutTupField, "tf")
    discard clean(sutTupField, "tf_dead", sxUnsat)
    confirmed(sutObjFields, "of")
    discard clean(sutObjFields, "of_dead", sxUnsat)
    confirmed(sutNested, "nf")
    discard clean(sutNested, "nf_dead", sxUnsat)

  test "an element of an array global, at a constant and a symbolic index":
    ## RED: `weInternalWalkerFault` (base); item 1's in-band decline.
    confirmed(sutArrConst, "ac")
    discard clean(sutArrConst, "ac_dead", sxUnsat)
    confirmed(sutArrSym, "as")
    discard clean(sutArrSym, "as_dead", sxUnsat)
    confirmed(sutArrRead, "ar")
    discard clean(sutArrRead, "ar_dead", sxUnsat)

  test "a part no write reached declines, as a scalar global does":
    inBand(sutTupUnwritten, "tf_unwritten", feGlobalReadUnmodelled, "gTup2.b")
    inBand(sutTupWhole, "tw", feGlobalReadUnmodelled, "gTup2.b")
    inBand(sutNestedUnwritten, "nf_unwritten", feGlobalReadUnmodelled, "gN2.z")
    inBand(sutArrConstUnwritten, "ac_unwritten", feGlobalReadUnmodelled, "gArr2[1]")
    inBand(sutArrSymUnwritten, "as_unwritten", feGlobalReadUnmodelled, "gArrS2")
    inBand(sutVarUnwritten, "vu", feGlobalReadUnmodelled, "gArrU2[3]")
    inBand(sutScalar, "sc", feGlobalReadUnmodelled, "gI2")

  test "writes through a var parameter, addr, and a callee":
    ## RED: sxUnknown, `feGlobalReadUnmodelled`.
    confirmed(sutVarParam, "vp")
    confirmed(sutAddr, "ad")
    confirmed(sutAddr, "ad_let")
    confirmed(sutCallee, "cw")
    discard clean(sutCallee, "cw_dead", sxUnsat)

# S8bn item 4's global path, pinned there through `var` parameters because
# an aggregate global read declined: a `ptr` of unknown origin may address a
# field or element of a tuple, object or array global.

type PO2 = object
  a, b: int

var gPT2: tuple[a, b: int]
var gPO2: PO2
var gPA2: array[3, int]
var gPU2: tuple[a, b: int]

proc sutPtrTupGlobal(p: ptr int) =
  if p == nil: return
  gPT2.a = 0
  gPT2.b = 5
  p[] = 7
  if gPT2.b == 7: symexTarget("ptg")
  if gPT2.a == 7 and gPT2.b == 7: symexTarget("ptg_dead")

proc sutPtrObjGlobal(p: ptr int) =
  if p == nil: return
  gPO2.a = 0
  p[] = 4
  if gPO2.a == 4: symexTarget("pog")

proc sutPtrArrGlobal(p: ptr int) =
  if p == nil: return
  gPA2[0] = 0
  gPA2[1] = 0
  p[] = 4
  if gPA2[1] == 4: symexTarget("pag")
  if gPA2[0] == 4 and gPA2[1] == 4: symexTarget("pag_dead")

proc sutPtrUnwritten(p: ptr int) =
  ## `p` may address `gPU2.b`, which no write reached.
  if p == nil: return
  gPU2.a = 0
  if p[] == 9: symexTarget("pu")

suite "S8bw (2): S8bn item 4's global path, on globals":

  test "nim":
    sutPtrTupGlobal(addr gPT2.b)
    check gPT2.b == 7
    sutPtrObjGlobal(addr gPO2.a)
    check gPO2.a == 4
    sutPtrArrGlobal(addr gPA2[1])
    check gPA2[1] == 4

  test "a ptr into a field or element of an aggregate global":
    ## RED: sxUnknown, `feGlobalReadUnmodelled` (the global's first
    ## partial write).
    confirmed(sutPtrTupGlobal, "ptg")
    discard clean(sutPtrTupGlobal, "ptg_dead", sxUnsat)
    confirmed(sutPtrObjGlobal, "pog")
    confirmed(sutPtrArrGlobal, "pag")
    discard clean(sutPtrArrGlobal, "pag_dead", sxUnsat)

  test "a ptr that may address a part no write reached":
    inBand(sutPtrUnwritten, "pu", feGlobalReadUnmodelled, "gPU2.b")

# ---- 3. pointers into case objects; generic case objects; table values -------
#
# RFC-0005 S8bw item 3. A `ptr` of unknown origin that may address a part of
# a case object (a global, a `var` parameter) declined; an `else` branch's
# field of a heap case object was no candidate target at all, so a write
# through a pointer to one was never seen (a false miss); `addr` of a branch
# field was `heUnsafeCast`; a generic case object was
# `feUnsupportedParamType`; a pointer into a table of non-`int64` values
# declined. A branch field is a target while its branch is active; a
# dereference that may reach one whose branch is not declines that path
# (Nim reads or writes whatever the active branch holds there).

template confirmedWithInactive(fn: typed, lbl: string): untyped =
  ## A sound `sxSat` (replayed `roConfirmed`), beside which the dereference's
  ## inactive-branch candidates declined, named.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxSat
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.severity != sevHint:
        check e.kind == feUnsupportedOp
        check "not the active one" in e.msg
        named = true
    check named
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

type
  PK3 = enum pkA, pkB
  PV3 = object
    n: int
    case k: PK3
    of pkA: a: int
    of pkB: b, c: int
  PE3K = enum peK0, peK1, peK2
  PE3 = ref object
    case k: PE3K
    of peK0: a: int
    else: e: int
  PM3 = ref object
    case k: PE3K
    of peK0: a: int
    of peK1, peK2: m: int

var gPV3: PV3

proc sutPtrCaseGlobal(p: ptr int; x: int) =
  gPV3 = PV3(n: 0, k: pkB, b: 1, c: 2)
  p[] = x
  if gPV3.b == 5: symexTarget("pcg")

proc sutPtrCaseVar(v: var PV3; p: ptr int) =
  if v.k == pkB:
    p[] = 7
    if v.c == 7: symexTarget("pcv")
    if v.n == 7: symexTarget("pcn")

proc sutPtrCaseRead(v: var PV3; p: ptr int) =
  if v.k == pkA:
    if p[] == 3 and v.a == 3: symexTarget("pcr")

proc sutPtrElse(r: PE3; p: ptr int) =
  if r != nil and r.k == peK1:
    if r.e == 1:
      p[] = 5
      if r.e == 5: symexTarget("pce")

proc sutPtrMultiTag(r: PM3; p: ptr int) =
  if r != nil and r.k == peK2:
    if r.m == 1:
      p[] = 5
      if r.m == 5: symexTarget("pcm")

proc sutAddrBranch(v: var PV3) =
  if v.k == pkB:
    v.b = 3
    let q = addr v.b
    q[] = q[] + 1
    if v.b == 4: symexTarget("pab")

proc sutAddrInactive(v: var PV3) =
  if v.k == pkA:
    let q = addr v.b
    q[] = 4
    symexTarget("pai")

type
  GK3 = enum gkA, gkB
  GC3[T] = object
    n: int
    case k: GK3
    of gkA: a: T
    of gkB: b: T
  GR3[T] = ref object
    case k: GK3
    of gkA: a: T
    of gkB: s: string

proc sutGenCase(g: GC3[int]) =
  if g.k == gkB and g.b == 7 and g.n == 2: symexTarget("gc")
  if g.k == gkA and g.a == 7 and g.a != 7: symexTarget("gc_dead")

proc sutGenCaseStr(g: GC3[string]) =
  if g.k == gkA and g.a == "x": symexTarget("gcs")

proc sutGenCaseRef(g: GR3[int]) =
  if g != nil and g.k == gkB and g.s == "y": symexTarget("gcr")

proc sutGenCaseField(g: GC3[int]) =
  if g.k == gkA:
    if g.b == 1: symexTarget("gcf")

proc sutPtrTabI32(t: var Table[string, int32]; p: ptr int32) =
  if t.hasKey("a") and t["a"] == 1:
    p[] = 5
    if t["a"] == 5: symexTarget("pt32")

proc sutPtrTabBool(t: var Table[string, bool]; p: ptr bool) =
  if t.hasKey("a") and not t["a"]:
    p[] = true
    if t["a"]: symexTarget("ptb")

suite "S8bw (3): pointers into case objects":

  test "nim":
    var v = PV3(n: 0, k: pkB, b: 1, c: 2)
    sutPtrCaseVar(v, addr v.c)
    check v.c == 7
    gPV3 = PV3(k: pkB)
    sutPtrCaseGlobal(addr gPV3.b, 5)
    check gPV3.b == 5
    let r = PE3(k: peK1, e: 1)
    sutPtrElse(r, addr r.e)
    check r.e == 5
    var w = PV3(k: pkA)
    expect FieldDefect:
      sutAddrInactive(w)

  test "a ptr into a case object global or var parameter":
    ## RED: sxRaised / sxUnknown, `feUnsupportedOp` ("a case object, table,
    ## set or seq of aggregates") and no witness.
    confirmedWithInactive(sutPtrCaseGlobal, "pcg")
    confirmedWithInactive(sutPtrCaseVar, "pcv")
    confirmedWithInactive(sutPtrCaseVar, "pcn")
    confirmedWithInactive(sutPtrCaseRead, "pcr")

  test "a ptr into a heap case object's else branch":
    ## RED: sxRaised, no error: the `else` branch's field was no target.
    confirmedWithInactive(sutPtrElse, "pce")
    confirmedWithInactive(sutPtrMultiTag, "pcm")

  test "addr of a branch field":
    ## RED: sxUnknown, `heUnsafeCast`.
    confirmed(sutAddrBranch, "pab")
    discard clean(sutAddrInactive, "pai", sxRaised)
    block:
      let r = symexFind(sutAddrInactive, tFieldDefect())
      checkpoint show(r.errors)
      check r.status == sxRaised
      for e in r.errors: check e.severity == sevHint

suite "S8bw (3): generic case objects":

  test "a generic case object, monomorphized":
    ## RED: sxUnknown, `feUnsupportedParamType`.
    confirmed(sutGenCase, "gc")
    discard clean(sutGenCase, "gc_dead", sxUnsat)
    confirmed(sutGenCaseStr, "gcs")
    confirmed(sutGenCaseRef, "gcr")
    block:
      let r = symexFind(sutGenCaseField, tFieldDefect())
      checkpoint show(r.errors)
      check r.status == sxRaised

suite "S8bw (3): pointers into tables of narrower values":

  test "nim":
    var t = {"a": 1'i32}.toTable
    sutPtrTabI32(t, addr t["a"])
    check t["a"] == 5

  test "a ptr into a Table[string, int32] / Table[string, bool] value":
    ## RED: sxUnknown / sxRaised, `feUnsupportedOp` (a table this model
    ## holds no element identity for).
    confirmed(sutPtrTabI32, "pt32")
    confirmed(sutPtrTabBool, "ptb")

suite "S8bw: walker version":

  test "the walker version is at least S8bw's":
    check parseInt(symexWalkerVersion) >= 227
