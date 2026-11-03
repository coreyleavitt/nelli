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
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_s8bw_remainder`, `tsymex_rfc0005_s8bw_remainder_b`,
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
    candidate(sutPtrUnwritten, "pu")   ## RFC-0005 batch 6: S8as's entry value

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
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

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
    ## set or seq of aggregates") and no witness. RFC-0005 S8bz (item 6): `a`
    ## and `b` are the same bytes, so nothing beside these hits declines.
    confirmed(sutPtrCaseGlobal, "pcg")
    confirmed(sutPtrCaseVar, "pcv")
    confirmed(sutPtrCaseVar, "pcn")
    confirmedWithInactive(sutPtrCaseRead, "pcr")

  test "a ptr into a heap case object's else branch":
    ## RED: sxRaised, no error: the `else` branch's field was no target.
    confirmed(sutPtrElse, "pce")   # RFC-0005 S8bz (item 6): `a` over `e`
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
