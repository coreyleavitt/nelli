## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part B: the
## part of a seq's aggregate element and of a table's aggregate value as a
## location (items 1 and 2), and a whole aggregate's pointer, which has no such
## target yet and declines where it may address one. Every expectation is
## Nim's: a `confirmed` case's witness ran the real proc to the target.
##
## RFC-0005 S8cm: part 3 of 6 of this suite, with `tsymex_rfc0005_s8bz_cells`,
## `tsymex_rfc0005_s8bz_cells_b`, `tsymex_rfc0005_s8bz_cells_d`,
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
