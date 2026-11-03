## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part B: the
## part of a seq's aggregate element and of a table's aggregate value as a
## location (items 1 and 2), and a whole aggregate's pointer, which has no such
## target yet and declines where it may address one. Every expectation is
## Nim's: a `confirmed` case's witness ran the real proc to the target.
##
## RFC-0005 S8cm: part 6 of 6 of this suite, with `tsymex_rfc0005_s8bz_cells`,
## `tsymex_rfc0005_s8bz_cells_b`, `tsymex_rfc0005_s8bz_cells_c`,
## `tsymex_rfc0005_s8bz_cells_d`, `tsymex_rfc0005_s8bz_cells_e`. Split so that
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

# ---- a whole aggregate's pointer ----------------------------------------------
#
# RFC-0005 S8bz. `ptrTargets` lists scalar and string pointees only
# (`ptrScalarPointee`), so a `ptr O1` wrote its own cells, and a read of the
# variable it addressed never saw them: a clean `sxUnsat` where Nim reaches the
# target (the "nim" test). It declines now wherever a location may hold one;
# modelling it is reported in RFC-0005, "As landed (S8bz)".

var gO1: O1
proc w1(xs: var seq[O1]; p: ptr O1) =
  if p != nil and xs.len > 0 and xs[0].y == 1:
    p[] = O1(x: 2, y: 3)
    if xs[0].y == 3: symexTarget("w1")
proc w2(t: var Table[string, O1]; p: ptr O1) =
  if p != nil and "a" in t and t["a"].y == 1:
    p[] = O1(x: 2, y: 3)
    if t["a"].y == 3: symexTarget("w2")
proc w3(o: var O1; p: ptr O1) =
  if p != nil and o.y == 1:
    p[] = O1(x: 2, y: 3)
    if o.y == 3: symexTarget("w3")
proc w4(p: ptr O1) =
  gO1.y = 1
  if p != nil:
    p[] = O1(x: 2, y: 3)
    if gO1.y == 3: symexTarget("w4")
proc w5(o: var O1; p: ptr O1) =
  if p != nil and o.y == 1:
    p.y = 3
    if o.y == 3: symexTarget("w5")
proc w6(h: H3; p: ptr O1) =
  if h != nil and h.o.y == 1 and p != nil:
    p[] = O1(x: 2, y: 3)
    if h.o.y == 3: symexTarget("w6")
proc w7(o: O1; p: ptr O1) =
  # By value: no pointer addresses the copy.
  if p != nil:
    let v = p[]
    if v.y == 3 and o.y == 4: symexTarget("w7")
proc w8(p: ptr O1; k: int) =
  # No location of the type but the pointer's own.
  if p != nil:
    p.y = k
    if p.y == 7: symexTarget("w8")
proc w9(k: int) =
  var o = O1(x: 1, y: 2)
  let p = addr o
  p.y = k
  if o.y == 7: symexTarget("w9")

suite "S8bz: a whole aggregate's pointer":
  test "nim":
    var o = O1(x: 1, y: 1)
    w3(o, addr o)
    check o == O1(x: 2, y: 3)
    var xs = @[O1(x: 1, y: 1)]
    w1(xs, addr xs[0])
    check xs[0].y == 3
  test "a location of the type declines, never `sxUnsat`":
    inBand(w1, "w1", "no pointer identity")
    inBand(w2, "w2", "no pointer identity")
    inBand(w3, "w3", "no pointer identity")
    inBand(w4, "w4", "no pointer identity")
    inBand(w5, "w5", "no pointer identity")
    inBand(w6, "w6", "no pointer identity")
  test "none: as before":
    confirmed(w7, "w7")
    confirmed(w8, "w8")
    confirmed(w9, "w9")
