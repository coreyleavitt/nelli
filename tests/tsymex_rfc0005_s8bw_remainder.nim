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
    ## svArray` (`iekIndex` on the `int` stand-in).
    inBand(sutArrWrite, "aw", feGlobalReadUnmodelled, "gArr1")
    inBand(sutObjArrWrite, "oaw", feGlobalReadUnmodelled, "gObjA1")

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

suite "S8bw: walker version":

  test "the walker version is at least S8bw's":
    check parseInt(symexWalkerVersion) >= 227
