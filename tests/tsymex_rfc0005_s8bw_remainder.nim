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
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8bw_remainder_b`, `tsymex_rfc0005_s8bw_remainder_c`,
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
    ## RFC-0005 batch 6: an observed read of these globals is S8as's entry
    ## value (`candidate`); Nim raises `IndexDefect` on the empty seq the
    ## process holds (`sqw`, `sqp`, `sqd`: the replay's verdict).
    candidate(sutSeqWrite, "sqw", {sxRaised})
    candidate(sutSeqPop, "sqp", {sxRaised})
    candidate(sutSeqDel, "sqd", {sxRaised})
    candidate(sutSeqAdd, "sqa")

  test "a higher-order call, a join and a bool test on a global":
    ## RED: AssertionDefect `seqSV.kind == svSeq` (`map`) and `recv.kind ==
    ## svSeq` (`join`).
    ## RFC-0005 batch 6: S8as's entry values (`candidate`).
    candidate(sutMap, "map")
    candidate(sutJoin, "join")
    candidate(sutBool, "gb")

  test "a {.global.} local":
    ## RED: the build failed ("node has no type": the name is a pragma
    ## expression). RFC-0005 batch 6: S8be models a `{.global.}` local as
    ## the module-level variable Nim makes it (`isRoutineGlobal`), so the
    ## element written is the element read; the replay confirms it in Nim.
    confirmed(sutLocalGlobal, "lg")

  test "a discriminator reassignment of an unwritten global":
    ## RED: a clean `sxSat` -- the reassignment was dropped, and Nim raises
    ## `FieldDefect` on it from the zero value's branch.
    ## RFC-0005 S8cd: a case-object global is entry-modelled (this was a
    ## `feGlobalReadUnmodelled` decline), and Nim raises on the replay's value.
    ## RFC-0005 S8bz (item 3):
    ## the discriminator is a part read at its entry value, not a decline.
    candidate(sutReassign, "vr", {sxRaised})
    candidate(sutReassignSym, "vrs", {sxRaised})

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
