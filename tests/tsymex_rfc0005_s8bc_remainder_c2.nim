## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part c: Table iteration, leaf-split seq elements, a recursive value object to a
## bounded depth (items 6, 3).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_c`, `tsymex_rfc0005_s8bc_remainder_c3`,
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

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

proc tiTuple(a: int) =
  # Bounded: `s += k * v` overflows for a huge `a`, a real `OverflowDefect`
  # that wins over the label (seen on Windows, RFC-0005 S8bc).
  if a < -1000 or a > 1000: return
  var t = initTable[int, int]()
  t[1] = a
  t[2] = 5
  var s = 0
  for (k, v) in t.pairs:
    s += k * v
  var u = 0
  for kv in t.pairs:
    u += kv[1]
  if s == 16 and u == a + 5: symexTarget("ti_tuple")

suite "S8bc (6): Table iteration":


  test "for (k, v) in t.pairs, and for kv in t.pairs":
    ## RFC-0005 batch 7 (S8bp on this pin): the label query multiplies a
    ## key by its value, and Nim's overflow checks on that product
    ## (`bvsmul_noovfl` / `noudfl` over two free 64-bit terms) cost 120,971,633
    ## units on Z3 5.1 and 79,811,624 on 4.13.4 in a context of its own, past
    ## a tainted path's 20M: the defaults declined (`beSolverUndef`) and only
    ## a 300M (later 600M) budget found the witness. RFC-0016 S8cg: the keys
    ## are spelled as a choice among the literals stored (`isTabKeys`), and
    ## the product's overflow check splits on them (`mulOverflowSplit`), so
    ## the defaults find Nim's own witness (`a == 6`, replayed natively) on
    ## both pinned Z3s.
    let r = symexFind(tiTuple, tLabel("ti_tuple"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
      check reproduces(tiTuple(r.witness[0]), "ti_tuple")


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
