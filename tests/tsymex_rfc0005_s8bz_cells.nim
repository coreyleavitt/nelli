## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part B: the
## part of a seq's aggregate element and of a table's aggregate value as a
## location (items 1 and 2), and a whole aggregate's pointer, which has no such
## target yet and declines where it may address one. Every expectation is
## Nim's: a `confirmed` case's witness ran the real proc to the target.
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/types

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
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

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

# ---- 2. a table's aggregate value ---------------------------------------------
#
# RFC-0005 S8bz item 2. `isTableValTy` declined a tuple, object, array or case
# object value (`feUnsupportedWitnessType`). It is held as a container value is
# (S8at's leaf-split data arrays), and rendered part by part.

proc t2t(t: Table[string, T1]) =
  if t.hasKey("a") and t["a"].a == 3 and t["a"].b == 4: symexTarget("t2t")
proc t2o(t: var Table[string, O1]; k: int) =
  t["z"] = O1(x: k, y: 2)
  if t["z"].x == 5: symexTarget("t2o")
proc t2int(t: Table[int, O1]) =
  if 1 in t and t[1].y == 3: symexTarget("t2int")
proc t2arr(t: Table[string, array[2, int]]) =
  if "q" in t and t["q"][1] == 3: symexTarget("t2arr")
proc t2v(t: Table[string, V1]) =
  if "q" in t and t["q"].k == vB and t["q"].b == "w": symexTarget("t2v")
proc t2dflt(t: Table[string, T1]) =
  if t.getOrDefault("nope").a == 0 and t.len == 0: symexTarget("t2dflt")
proc t2w(t: var Table[string, O1]; k: int) =
  if "a" in t and t["a"].x == 2:
    t["a"].y = k
    if t["a"].y == 5 and t["a"].x == 2: symexTarget("t2w")
proc t2wDead(t: var Table[string, O1]; k: int) =
  if "a" in t and t["a"].x == 2:
    t["a"].y = k
    if t["a"].x != 2: symexTarget("t2wDead")
proc t2l(k: int) =
  var t = initTable[string, O1]()
  t["a"] = O1(x: 1, y: 2)
  t["a"].y = k
  if t["a"].y == 5 and t["a"].x == 1: symexTarget("t2l")
proc t2miss(t: var Table[string, O1]; s: string) =
  t[s].y = 5
  symexTarget("t2miss")
proc t2wv(t: var Table[string, V1]; k: int) =
  if "a" in t and t["a"].k == vA:
    t["a"].a = k
    if t["a"].a == 5: symexTarget("t2wv")

suite "S8bz (2): a table's aggregate value":
  test "nim":
    var t = {"a": O1(x: 2, y: 3)}.toTable
    t["a"].y = 5
    check t["a"] == O1(x: 2, y: 5)
    var raised = false
    try: t2miss(t, "nope")
    except KeyError: raised = true
    check raised
  test "read, as a tuple, an object, an array, a case object":
    confirmed(t2t, "t2t")
    confirmed(t2o, "t2o")
    confirmed(t2int, "t2int")
    confirmed(t2arr, "t2arr")
    confirmed(t2v, "t2v")
    confirmed(t2dflt, "t2dflt")
  test "a field written in place":
    confirmed(t2w, "t2w")
    discard clean(t2wDead, "t2wDead", sxUnsat)
    confirmed(t2l, "t2l")
    confirmed(t2wv, "t2wv")
    confirmed(t2miss, "t2miss")

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
