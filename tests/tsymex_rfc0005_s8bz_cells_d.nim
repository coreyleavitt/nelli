## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part B: the
## part of a seq's aggregate element and of a table's aggregate value as a
## location (items 1 and 2), and a whole aggregate's pointer, which has no such
## target yet and declines where it may address one. Every expectation is
## Nim's: a `confirmed` case's witness ran the real proc to the target.
##
## RFC-0005 S8cm: part 4 of 6 of this suite, with `tsymex_rfc0005_s8bz_cells`,
## `tsymex_rfc0005_s8bz_cells_b`, `tsymex_rfc0005_s8bz_cells_c`,
## `tsymex_rfc0005_s8bz_cells_e`, `tsymex_rfc0005_s8bz_cells_f`. Split so that
## each part compiles and runs in under 60 s on the Windows legs (the whole
## file took 87 s).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/types
import s8ct_platform

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
  ## A clean `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

template inBand(fn: typed, lbl: string, needle: string): untyped =
  ## A stated decline, never `sxUnsat`, never a walker fault.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feUnsupportedOp and needle in e.msg: named = true
    check named

type
  O1 = object
    x, y: int
  T1 = tuple[a, b: int]
  F1 = tuple[a: int, b: float]
  S1 = object
    s: string
    n: int
  N1 = object
    i: O1
    c: array[2, int]
  W1 = object
    xs: seq[int]
    n: int
  VK = enum vA, vB
  V1 = object
    case k: VK
    of vA: a: int
    of vB: b: string
  H1 = ref object
    xs: seq[O1]
  H2 = ref object
    t: Table[string, O1]
  H3 = ref object
    o: O1
    n: int

# Pointers into a table: a string or float value, a part of an aggregate value.

proc t2ptrs(t: var Table[string, string]; p: ptr string) =
  if t.hasKey("a") and t["a"] == "x":
    p[] = "y"
    if t["a"] == "y": symexTarget("t2ptrs")
proc t2ptrsDead(t: var Table[string, string]; p: ptr string) =
  if p != nil and t.hasKey("a") and t["a"] == "x":
    p[] = "y"
    if t["a"] != "x" and t["a"] != "y": symexTarget("t2ptrsDead")
proc t2ptrf(t: var Table[string, float]; p: ptr float) =
  if t.hasKey("a") and t["a"] == 1.0:
    p[] = 2.0
    if t["a"] == 2.0: symexTarget("t2ptrf")
proc t2ptro(t: var Table[string, O1]; p: ptr int) =
  if t.hasKey("a") and t["a"].x == 1:
    p[] = 2
    if t["a"].x == 2: symexTarget("t2ptro")
proc t2ptroDead(t: var Table[string, O1]; p: ptr int) =
  if p != nil and t.hasKey("a") and t["a"].x == 1:
    p[] = 2
    if t["a"].x != 1 and t["a"].x != 2: symexTarget("t2ptroDead")
proc t2ptrr(t: var Table[string, O1]; p: ptr int) =
  if p != nil and t.hasKey("a"):
    t["a"].y = 9
    if p[] == 9: symexTarget("t2ptrr")
proc t2ptrh(h: H2; p: ptr int) =
  if h != nil and "a" in h.t:
    p[] = 2
    if h.t["a"].x == 2: symexTarget("t2ptrh")
proc t2ptrint(t: var Table[int, O1]; p: ptr int) =
  if p != nil and 1 in t:
    p[] = 2
    if t[1].x == 2: symexTarget("t2ptrint")
proc t2ptrseq(t: var Table[string, seq[int]]; p: ptr int) =
  if "a" in t:
    p[] = 2
    symexTarget("t2ptrseq")

suite "S8bz (2): pointers into a table":
  test "a string and a float value":
    confirmed(t2ptrs, "t2ptrs")
    discard clean(t2ptrsDead, "t2ptrsDead", sxUnsat)
    confirmed(t2ptrf, "t2ptrf")
  test "a part of an aggregate value":
    confirmed(t2ptro, "t2ptro")
    discard clean(t2ptroDead, "t2ptroDead", sxUnsat)
    confirmed(t2ptrr, "t2ptrr")
    confirmed(t2ptrh, "t2ptrh")
  test "a key the pointer's model holds no key for stays a stated decline":
    inBand(t2ptrint, "t2ptrint", "no element identity")
    inBand(t2ptrseq, "t2ptrseq", "no element identity")
