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
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_rfc0005_s8bw_remainder`, `tsymex_rfc0005_s8bw_remainder_b`,
## `tsymex_rfc0005_s8bw_remainder_c`. Split so that each part compiles and runs
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
