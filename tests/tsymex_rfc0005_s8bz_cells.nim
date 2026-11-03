## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part B: the
## part of a seq's aggregate element and of a table's aggregate value as a
## location (items 1 and 2), and a whole aggregate's pointer, which has no such
## target yet and declines where it may address one. Every expectation is
## Nim's: a `confirmed` case's witness ran the real proc to the target.
##
## RFC-0005 S8cm: part 1 of 6 of this suite, with
## `tsymex_rfc0005_s8bz_cells_b`, `tsymex_rfc0005_s8bz_cells_c`,
## `tsymex_rfc0005_s8bz_cells_d`, `tsymex_rfc0005_s8bz_cells_e`,
## `tsymex_rfc0005_s8bz_cells_f`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 87 s).
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

# ---- 1. a part of a seq's aggregate element ------------------------------------
#
# RFC-0005 S8bz item 1. `ptrVarLeaves` had no identity for a seq of aggregates:
# "holds no element identity". Each part is a target now: the pointer's index,
# then the path below the element (S8bc's leaf-split arrays). A `var` seq's
# witness replays too: `witnessFidelity` refused a tree element unrun.

proc s1(xs: var seq[T1]; p: ptr int) =
  if xs.len > 0 and xs[0].a == 1:
    p[] = 5
    if xs[0].a == 5: symexTarget("s1")
proc s1o(xs: var seq[O1]; p: ptr int) =
  if xs.len > 1 and xs[1].y == 1:
    p[] = 5
    if xs[1].y == 5: symexTarget("s1o")
proc s1dead(xs: var seq[O1]; p: ptr int) =
  if p != nil and xs.len > 1 and xs[1].y == 1:
    p[] = 5
    if xs[1].y != 1 and xs[1].y != 5: symexTarget("s1dead")
proc s1r(xs: seq[O1]; p: ptr int) =
  # A by-value parameter's copy is no pointer's target: the pointer is free.
  if xs.len > 0 and xs[0].x == 1 and p[] == 9: symexTarget("s1r")
proc s1rv(xs: var seq[O1]; p: ptr int) =
  if p != nil and xs.len > 0 and xs[0].x == 1:
    xs[0].y = 7
    if p[] == 7 and xs[0].x == 1: symexTarget("s1rv")
proc s1f(xs: var seq[F1]; p: ptr float) =
  if xs.len > 0:
    p[] = 1.5
    if xs[0].b == 1.5: symexTarget("s1f")
proc s1s(xs: var seq[S1]; p: ptr string) =
  if xs.len > 0:
    p[] = "q"
    if xs[0].s == "q": symexTarget("s1s")
proc s1n(xs: var seq[N1]; p: ptr int) =
  if xs.len > 0:
    p[] = 7
    if xs[0].c[1] == 7: symexTarget("s1n")
proc s1n2(xs: var seq[N1]; p: ptr int) =
  if xs.len > 0:
    p[] = 7
    if xs[0].i.y == 7: symexTarget("s1n2")
proc s1h(h: H1; p: ptr int) =
  if h != nil and h.xs.len > 0:
    p[] = 7
    if h.xs[0].y == 7: symexTarget("s1h")
proc s1hdead(h: H1; p: ptr int) =
  if p != nil and h != nil and h.xs.len > 0 and h.xs[0].y == 1:
    p[] = 7
    if h.xs[0].y != 1 and h.xs[0].y != 7: symexTarget("s1hdead")
proc s1resize(xs: var seq[O1]; p: ptr int) =
  if xs.len > 0:
    xs.add O1(x: 1, y: 2)
    p[] = 7
    if xs[0].y == 7: symexTarget("s1resize")
proc s1nested(xs: var seq[W1]; p: ptr int) =
  if xs.len > 0:
    p[] = 7
    if xs[0].n == 7: symexTarget("s1nested")

suite "S8bz (1): a part of a seq's aggregate element":
  test "a store through the pointer, read back at the element":
    confirmed(s1, "s1")
    confirmed(s1o, "s1o")
    discard clean(s1dead, "s1dead", sxUnsat)
  test "a read through the pointer":
    confirmed(s1r, "s1r")
    confirmed(s1rv, "s1rv")
  test "a float, a string, a nested object or array":
    confirmed(s1f, "s1f")
    confirmed(s1s, "s1s")
    confirmed(s1n, "s1n")
    confirmed(s1n2, "s1n2")
  test "a seq held in a heap cell":
    confirmed(s1h, "s1h")
    discard clean(s1hdead, "s1hdead", sxUnsat)
  test "a resize, and a container inside the element, stay stated declines":
    inBand(s1resize, "s1resize", "a resize may move")
    inBand(s1nested, "s1nested", "no element identity")
