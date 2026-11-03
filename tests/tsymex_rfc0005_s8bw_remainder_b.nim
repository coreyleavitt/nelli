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
##
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_s8bw_remainder`, `tsymex_rfc0005_s8bw_remainder_c`,
## `tsymex_rfc0005_s8bw_remainder_d`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 72 s).
import std/[unittest, strutils, tables, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import s8ct_platform   ## RFC-0005 S8ct

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
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

template candidate(fn: typed, lbl: string,
                   raised: set[SymexStatusKind] = {}): untyped =
  ## RFC-0005 batch 6 (S8bw on S8as). The global's entry value is modelled
  ## (S8as, `entryValueOf`): it may hold any value of its type when the
  ## property runs, so a read that observes a part no write reached taints
  ## the path `feGlobalHavoc` -- never `sxUnsat`, and a SAT is replayed. The
  ## replay runs on the global as the process holds it (zero here), so it
  ## may refute the hit; `raised` admits `sxRaised` where Nim raises on that
  ## value (the "nim" tests show it).
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown} + raised
    var havoc = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feGlobalHavoc: havoc = true
    check havoc

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

  test "a part no write reached is the global's entry value":
    ## RFC-0005 batch 6: as a scalar global's read before any write is
    ## (S8as), an observed part no write reached is its entry value, any
    ## of its type: a candidate (`feGlobalHavoc`), never `sxUnsat`.
    candidate(sutTupUnwritten, "tf_unwritten")
    candidate(sutTupWhole, "tw")
    candidate(sutNestedUnwritten, "nf_unwritten")
    candidate(sutArrConstUnwritten, "ac_unwritten")
    candidate(sutArrSymUnwritten, "as_unwritten")
    # RFC-0005 S8bz (item 3): the callee only writes its `var` formal, so the
    # copy in observes nothing and the hit is Nim's on any entry value.
    confirmed(sutVarUnwritten, "vu")
    candidate(sutScalar, "sc")

  test "writes through a var parameter, addr, and a callee":
    ## RED: sxUnknown, `feGlobalReadUnmodelled`.
    confirmed(sutVarParam, "vp")
    confirmed(sutAddr, "ad")
    confirmed(sutAddr, "ad_let")
    confirmed(sutCallee, "cw")
    discard clean(sutCallee, "cw_dead", sxUnsat)

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
