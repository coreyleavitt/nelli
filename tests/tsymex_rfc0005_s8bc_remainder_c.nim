## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part c: Table iteration, leaf-split seq elements, a recursive value object to a
## bounded depth (items 6, 3).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_c2`, `tsymex_rfc0005_s8bc_remainder_c3`,
## `tsymex_rfc0005_s8bc_remainder_c4`. Split so that each part compiles and
## runs in under 60 s on the Windows legs (the whole file took 134 s).
import std/[unittest, strutils, sequtils, tables, sets, hashes]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (6) Table iteration ---------------------------------------------------
#
# RFC-0005 S8bc: `pairs` / `keys` / `values` (and `for k, v in t`) over a
# Table is a bounded unroll over an enumeration of its present keys in a
# FREE order (`isTabKeys`). Nim's order is the hash order, so a table that
# can hold two or more entries taints the path `feTableIterOrder`
# (`dcFreshSymbol`): the candidate is replayed, and one whose label needs an
# order Nim does not produce is refuted to sxUnknown.

proc tiSum(a, b: int) =
  if a < -100 or a > 100 or b < -100 or b > 100: return   # no overflow
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var s = 0
  for k, v in t:
    s += v + k
  if s == 13 and a == 4: symexTarget("ti_sum")
  # Every enumeration sums the same: a + b + 3 over two entries, b + 2 over
  # one (a == b, the second write wins).
  if a != b and s != a + b + 3: symexTarget("ti_sum_dead")
  if a == b and s != b + 2: symexTarget("ti_sum_dead")

proc tiOrder(a, b: int) =
  # Nim 2.2.10 visits the keys 1, 2 of this table as 2 then 1 (probed).
  if a != 1 or b != 2: return
  var t = initTable[int, int]()
  t[a] = 1
  t[b] = 2
  var first = -1
  for k in t.keys:
    if first == -1: first = k
  if first == 2: symexTarget("ti_order_real")
  if first == 1: symexTarget("ti_order_other")

proc tiValues(a: int) =
  var t = initTable[string, int]()
  t["x"] = a
  t["y"] = 3
  var s = 0
  for v in t.values:
    s += v
  if s == 10: symexTarget("ti_values")

suite "S8bc (6): Table iteration":
  test "for k, v in t: an order-independent fold":
    let r = symexFind(tiSum, tLabel("ti_sum"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(tiSum(r.witness[0], r.witness[1]), "ti_sum")
    let d = symexFind(tiSum, tLabel("ti_sum_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an order Nim produces is found; another declines":
    let r = symexFind(tiOrder, tLabel("ti_order_real"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(tiOrder(r.witness[0], r.witness[1]), "ti_order_real")
    let o = symexFind(tiOrder, tLabel("ti_order_other"))
    checkpoint $o.status & " " & show(o.errors)
    check o.status == sxUnknown
    check o.errors.hasKind(feReplayRefuted)
    check o.errors.hasKind(feTableIterOrder)

  test "values, over a string-keyed table":
    let r = symexFind(tiValues, tLabel("ti_values"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
      check reproduces(tiValues(r.witness[0]), "ti_values")


# ---- (3) a seq whose element is a tuple or object ---------------------------
#
# RFC-0005 S8bc: a seq of a tuple, object, array or case object is held
# leaf-split, one `Int -> leaf` array per leaf of the element (as a Table's
# container value is, S8at's `tvTree`). It declined in every position
# (`seNestedSeqUnsupported`). A value object that recurs through a seq is
# unrolled to a bounded depth; a read past it declines
# (`seRecursiveValueDepth`).

type
  LPt = tuple[x: int, y: int]
  LObj = object
    a: int
    s: string
  LHold = object
    ps: seq[LObj]
  LNest = object
    q: seq[int]
    b: bool
  LKind = enum lkA, lkB
  LVar = object
    case k: LKind
    of lkA: i: int
    of lkB: str: string
  LBox = ref object
    ps: seq[LPt]
  RTree = object
    kids: seq[RTree]
    v: int
