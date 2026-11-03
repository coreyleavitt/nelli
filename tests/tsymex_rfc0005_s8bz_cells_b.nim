## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part B: the
## part of a seq's aggregate element and of a table's aggregate value as a
## location (items 1 and 2), and a whole aggregate's pointer, which has no such
## target yet and declines where it may address one. Every expectation is
## Nim's: a `confirmed` case's witness ran the real proc to the target.
##
## RFC-0005 S8cm: part 2 of 6 of this suite, with `tsymex_rfc0005_s8bz_cells`,
## `tsymex_rfc0005_s8bz_cells_c`, `tsymex_rfc0005_s8bz_cells_d`,
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

# `addr xs[i].x`, and the write it is rewritten to.

proc s1addr(xs: var seq[O1]; k: int) =
  if xs.len > 2:
    let q = addr xs[1].x
    q[] = k
    if xs[1].x == 5: symexTarget("s1addr")
proc s1addrk(xs: var seq[O1]; k: int) =
  if xs.len > 2 and k >= 0 and k < 3:
    let q = addr xs[k].y
    q[] = 5
    if xs[k].y == 5 and k == 2: symexTarget("s1addrk")
proc s1keep(xs: var seq[O1]; k: int) =
  if xs.len > 2 and xs[0].x == 1 and xs[1].y == 2:
    xs[1].x = k
    if xs[1].x == 5 and xs[0].x == 1 and xs[1].y == 2: symexTarget("s1keep")
proc s1keepDead(xs: var seq[O1]; k: int) =
  if xs.len > 2 and xs[0].x == 1:
    xs[1].x = k
    if xs[0].x != 1: symexTarget("s1keepDead")
proc s1local(k: int) =
  var xs = @[O1(x: 1, y: 2), O1(x: 3, y: 4)]
  xs[1].y = k
  if xs[1].y == 5 and xs[0].y == 2 and xs[1].x == 3: symexTarget("s1local")
proc s1oob(xs: var seq[O1]; k: int) =
  xs[k].y = 5
  symexTarget("s1oob")

suite "S8bz (1): a field of a seq's aggregate element, in place":
  test "nim":
    var xs = @[O1(x: 1, y: 2), O1(x: 3, y: 4)]
    xs[1].y = 5
    check xs[1] == O1(x: 3, y: 5)
    check xs[0] == O1(x: 1, y: 2)
    var raised = false
    try: s1oob(xs, 9)
    except IndexDefect: raised = true
    check raised
  test "`addr xs[i].x`":
    confirmed(s1addr, "s1addr")
    confirmed(s1addrk, "s1addrk")
  test "the other parts and elements keep their values":
    confirmed(s1keep, "s1keep")
    discard clean(s1keepDead, "s1keepDead", sxUnsat)
    confirmed(s1local, "s1local")
  test "the index is checked":
    let r = symexFind(s1oob, tIndexError())
    check r.status == sxRaised
    confirmed(s1oob, "s1oob")
