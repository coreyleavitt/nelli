## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part B: the
## part of a seq's aggregate element and of a table's aggregate value as a
## location (items 1 and 2), and a whole aggregate's pointer, which has no such
## target yet and declines where it may address one. Every expectation is
## Nim's: a `confirmed` case's witness ran the real proc to the target.
##
## RFC-0005 S8cm: part 5 of 6 of this suite, with `tsymex_rfc0005_s8bz_cells`,
## `tsymex_rfc0005_s8bz_cells_b`, `tsymex_rfc0005_s8bz_cells_c`,
## `tsymex_rfc0005_s8bz_cells_d`, `tsymex_rfc0005_s8bz_cells_f`. Split so that
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

# ---- a by-value part of a heap object -----------------------------------------
#
# RFC-0005 S8bz. A part of a by-value aggregate field of a `ref object` is a leaf
# heap of its own (S8ar), which `ptrTargets` never listed: a store through the
# pointer never reached a read of the part, a clean `sxUnsat` Nim contradicts.

proc h3w(h: H3; p: ptr int) =
  if p != nil and h != nil and h.o.y == 1:
    p[] = 3
    if h.o.y == 3: symexTarget("h3w")
proc h3r(h: H3; p: ptr int) =
  # The part is read first: the store below reaches it (`h3late`).
  if p != nil and h != nil and h.o.y >= 0:
    p[] = 1
    h.o.y = 4
    if p[] == 4: symexTarget("h3r")

proc h3late(h: H3; p: ptr int) =
  # The store came before this path held the part; it still reached it. Nim
  # cannot hit this target: never the false `sxSat`.
  if p != nil and h != nil:
    p[] = 1
    h.o.y = 4
    if p[] != 1 and p[] != 4: symexTarget("h3late")
proc h3lateN(h: H3; p: ptr int) =
  if p != nil and h != nil:
    p[] = 1
    let k = h.n
    if p[] != 1 and k == k: symexTarget("h3lateN")
proc h3lateHit(h: H3; p: ptr int) =
  if p != nil and h != nil:
    p[] = 1
    h.n = 4
    if p[] == 4: symexTarget("h3lateHit")
proc h3lateTwo(h: H3; p, q: ptr int) =
  # Another pointer's store, in order under the field's later write.
  if p != nil and q != nil and h != nil:
    q[] = 2
    p[] = 1
    let k = h.n
    if q[] == 1 and k == k: symexTarget("h3lateTwo")
proc h3lateDead(h: H3; p, q: ptr int) =
  if p != nil and q != nil and h != nil:
    q[] = 2
    p[] = 1
    let k = h.n
    if q[] != 1 and q[] != 2 and k == k: symexTarget("h3lateDead")
proc h3lateRead(h: H3; p: ptr int) =
  # A read between the store and the dereference that finds the part saw the
  # store: under the alias `k` is 1, and without it `p[]` is.
  if p != nil and h != nil:
    p[] = 1
    let k = h.o.y
    h.o.y = 5
    if p[] == 5 and k == 7: symexTarget("h3lateRead")
proc h3lateReadHit(h: H3; p: ptr int) =
  if p != nil and h != nil:
    p[] = 1
    let k = h.o.y
    h.o.y = 5
    if p[] == 5 and k == 1: symexTarget("h3lateReadHit")
proc h1late(h: H1; p: ptr int) =
  # A seq's element has no such store: a stated decline.
  if p != nil and h != nil:
    p[] = 1
    if h.xs.len > 0 and p[] != 1: symexTarget("h1late")

suite "S8bz: a by-value part of a heap object":
  test "nim":
    var h = H3(o: O1(x: 1, y: 1))
    h3w(h, addr h.o.y)
    check h.o.y == 3
    # `h3lateRead`, native: the read sees the store through the alias.
    h = H3(o: O1(x: 1, y: 1))
    let p3 = addr h.o.y
    p3[] = 1
    let k3 = h.o.y
    h.o.y = 5
    check p3[] == 5 and k3 == 1
  test "a target of the pointer":
    confirmed(h3w, "h3w")
    confirmed(h3r, "h3r")
  test "a store before the path held the part reaches it":
    discard clean(h3late, "h3late", sxUnsat)
    discard clean(h3lateN, "h3lateN", sxUnsat)
    confirmed(h3lateHit, "h3lateHit")
    # Both pointers at one object no parameter reaches, which a witness does
    # not hold (RFC-0005, "As landed (S8bz)"): no replay.
    discard clean(h3lateTwo, "h3lateTwo", sxSat)
    discard clean(h3lateDead, "h3lateDead", sxUnsat)
    discard clean(h3lateRead, "h3lateRead", sxUnsat)
    confirmed(h3lateReadHit, "h3lateReadHit")
  test "where it cannot: a stated decline":
    inBand(h1late, "h1late", "which that store did not reach")
