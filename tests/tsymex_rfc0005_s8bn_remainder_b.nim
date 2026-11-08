## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 2 of 6 of this suite, with
## `tsymex_rfc0005_s8bn_remainder`, `tsymex_rfc0005_s8bn_remainder_c`,
## `tsymex_rfc0005_s8bn_remainder_d`, `tsymex_rfc0005_s8bn_remainder_e`,
## `tsymex_rfc0005_s8bn_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 121 s).

import std/[unittest, strutils, options, macros, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser
import s8ct_platform   ## RFC-0005 S8ct
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8bn_remainder_b")

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
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

# ---- 1-2. ptr alias witnesses ------------------------------------------------
#
# RFC-0005 S8bn items 1 and 2. S8bh aimed a `ptr` of unknown origin at a
# ref object's field, a global or a `var` parameter, and the `sxSat` was
# sound; but its witness replayed only when the field's object was built
# before the pointer (parameter order), and never for a global or a `var`
# parameter (the snapshot held no cell for either).

type PQ = ref object
  x: int
  s: string

type VQ = ref object
  x: int

# ---- 4. a ptr into an aggregate -----------------------------------------------
#
# RFC-0005 S8bn item 4. A `ptr` of unknown origin that may address a part of
# a by-value aggregate global or `var` parameter, or an element of a seq held
# in the heap, declined (`feUnsupportedOp`, "by-value aggregate this model
# holds no cell for" / "held in a heap cell"). Each such part is now a
# candidate target named by S8ax's element-alias identity (root, path,
# snapshot index): a field, an array element, a seq element (its index is
# the pointer's own, within the seq's input length). A seq whose length the
# path changed still declines: a resize may move its elements.

type
  HS4 = ref object
    xs: seq[int]
  PO4 = object
    a, b: int

proc sutPTupVar(t: var tuple[a, b: int]; p: ptr int) =
  if p == nil: return
  t.a = 0
  t.b = 5
  p[] = 7
  if t.b == 7: symexTarget("ptv")
  if t.a == 7 and t.b == 7: symexTarget("ptv_dead")

proc sutPObjVar(p: ptr int; o: var PO4) =
  ## The pointer before the object it addresses a field of.
  if p == nil: return
  o.a = 0
  p[] = 4
  if o.a == 4: symexTarget("pov")

proc sutPArrVar(a: var array[3, int]; p: ptr int) =
  if p == nil: return
  a[0] = 0
  a[1] = 0
  p[] = 4
  if a[1] == 4: symexTarget("pav")
  if a[0] == 4 and a[1] == 4: symexTarget("pav_dead")

proc sutPSeqVar(s: var seq[int]; p: ptr int) =
  if p == nil or s.len < 2: return
  s[0] = 0
  s[1] = 0
  p[] = 9
  if s[1] == 9: symexTarget("psv")
  if s[0] == 9 and s[1] == 9: symexTarget("psv_dead")

proc sutPSeqGrow(s: var seq[int]; p: ptr int) =
  if p == nil: return
  s.add 1
  p[] = 3
  if s[0] == 3: symexTarget("psg")

proc sutPTabVar(t: var Table[string, int]; p: ptr int) =
  if p == nil or not t.hasKey("a"): return
  t["a"] = 0
  p[] = 5
  if t["a"] == 5: symexTarget("ptb")

proc sutPTabGrow(t: var Table[string, int]; p: ptr int) =
  if p == nil: return
  t["fresh"] = 1
  p[] = 3
  if t.len == 1: symexTarget("ptbg")

proc sutPSetVar(s: var HashSet[int]; p: ptr int) =
  ## A set's members have no address: no pointer reaches them.
  if p == nil: return
  s.incl 4
  p[] = 9
  if 9 in s and not (4 in s): symexTarget("pss_dead")
  if 4 in s: symexTarget("pss")

proc sutPHeapSeqPop(h: HS4; p: ptr int) =
  ## A length changed and changed back: `add` may have moved the elements.
  if h == nil or p == nil or h.xs.len < 1: return
  h.xs.add 1
  discard h.xs.pop()
  p[] = 6
  if h.xs[0] == 6: symexTarget("phsp")

proc sutPTabDel(t: var Table[string, int]; p: ptr int) =
  ## A deletion may shift the other entries.
  if p == nil or not t.hasKey("a") or not t.hasKey("b"): return
  t.del("b")
  p[] = 5
  if t["a"] == 5: symexTarget("ptbd")

proc sutPHeapSeq(h: HS4; p: ptr int) =
  if h == nil or p == nil or h.xs.len < 1: return
  h.xs[0] = 1
  p[] = 6
  if h.xs[0] == 6: symexTarget("phs")

suite "S8bn (4): a ptr into an aggregate":

  test "nim":
    var t: tuple[a, b: int]
    sutPTupVar(t, addr t.b)
    check t.b == 7
    var o: PO4
    sutPObjVar(addr o.a, o)
    check o.a == 4
    var a: array[3, int]
    sutPArrVar(a, addr a[1])
    check a[1] == 4
    var s = @[5, 5]
    sutPSeqVar(s, addr s[1])
    check s[1] == 9
    var tb = {"a": 1}.toTable
    sutPTabVar(tb, addr tb["a"])
    check tb["a"] == 5
    let h = HS4(xs: @[0])
    sutPHeapSeq(h, addr h.xs[0])
    check h.xs[0] == 6

  test "a field or element of a by-value aggregate":
    ## RED: sxUnknown, `feUnsupportedOp` "by-value aggregate this model
    ## holds no cell for".
    confirmed(sutPTupVar, "ptv")
    discard clean(sutPTupVar, "ptv_dead", sxUnsat)
    confirmed(sutPObjVar, "pov")
    confirmed(sutPArrVar, "pav")
    discard clean(sutPArrVar, "pav_dead", sxUnsat)

  test "an element of a seq":
    ## RED: sxUnknown, as above.
    confirmed(sutPSeqVar, "psv")
    discard clean(sutPSeqVar, "psv_dead", sxUnsat)

  test "an element of a seq held in the heap":
    ## RED: sxUnknown, `feUnsupportedOp` "held in a heap cell".
    confirmed(sutPHeapSeq, "phs")
    pinDecline(sutPHeapSeqPop, declKey, feUnsupportedOp, tLabel("phsp"), "may dangle")

  test "a seq the path resized still declines":
    pinDecline(sutPSeqGrow, declKey, feUnsupportedOp, tLabel("psg"), "may dangle")

  test "a value of a table, and a set's members":
    ## RED: sxUnknown, `feUnsupportedOp` "by-value aggregate this model
    ## holds no cell for".
    confirmed(sutPTabVar, "ptb")
    pinDecline(sutPTabGrow, declKey, feUnsupportedOp, tLabel("ptbg"), "may dangle")
    pinDecline(sutPTabDel, declKey, feUnsupportedOp, tLabel("ptbd"), "may dangle")
    discard clean(sutPSetVar, "pss", sxSat)
    discard clean(sutPSetVar, "pss_dead", sxUnsat)

# ---- 6b. S8bk's late address on a call through a proc value -----------------
#
# RFC-0005 S8bn item 6 (S8bk's integration note). Nim takes a `var` / `addr`
# actual's address AT THE CALL, after every later argument: `let f = touch;
# f(gB.x, moveB())` compiles to `T1_ = moveB(); f(&(*gB).x, T1_)`, so when
# `moveB` rebinds `gB` the callee reads and writes the new object. S8bh's
# call through a proc value copied the value in (or filled the `addr` cell)
# where the argument stood and wrote it back through the late address. Only
# the address's checks (an index's bound) run where the argument stands; a
# later call that changes what one read declines.

type LBox = ref object
  x: int
