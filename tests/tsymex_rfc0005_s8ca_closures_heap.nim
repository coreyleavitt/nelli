## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 4b: a
## heap lvalue a closure's body also reaches. Item 4a is
## `tsymex_rfc0005_s8ca_closures` (split by item 9).
##
## A `var` actual that is a heap lvalue (`grb.x`, `pb[].x`) passed to a
## closure or a proc value whose body also reaches that object (a global, a
## capture) declined (S8bh's `touchMeetsOuter`): the body's write through
## the formal and its direct access were two copies.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (4b) such a heap lvalue is passed by reference: the body is
##        specialised to the lvalue (`byRefSub`, as for a direct call).
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.severity == sevHint

from ./s8cu_helpers import nativeHits

const ks = [-3, 0, 1, 2, 3, 5, 7]

type RB = ref object
  x, y: int

var grb: RB

proc sutHeapClosure(k: int) =
  if k < 0 or k > 1000: return
  grb = RB()
  let f = proc (v: var int) =
    v = k
    grb.y = grb.x + 1
  f(grb.x)
  if grb.y == k + 1 and k == 3: symexTarget("hc")
  if grb.y != k + 1: symexTarget("hc_dead")

proc setThenBump(v: var int, k: int) =
  v = k
  grb.y = grb.x + 1

proc sutHeapProcValue(k: int) =
  if k < 0 or k > 1000: return
  grb = RB()
  let g = setThenBump
  g(grb.x, k)
  if grb.y == k + 1 and k == 3: symexTarget("hp")
  if grb.y != k + 1: symexTarget("hp_dead")

type PB = object
  x, y: int

var gpb: ptr PB

proc sutPtrLocal(k: int) =
  ## `pb[].x`, the pointer a captured local.
  if k < 0 or k > 1000: return
  var b = PB()
  let pb = addr b
  let f = proc (v: var int) =
    v = k
    pb[].y = pb[].x + 1
  f(pb[].x)
  if b.y == k + 1 and k == 3: symexTarget("pl")
  if b.y != k + 1: symexTarget("pl_dead")

proc sutPtrGlobal(k: int) =
  ## `gpb[].x`, the pointer a global.
  if k < 0 or k > 1000: return
  var b = PB()
  gpb = addr b
  let f = proc (v: var int) =
    v = k
    gpb[].y = gpb[].x + 1
  f(gpb[].x)
  if b.y == k + 1 and k == 3: symexTarget("pg")
  if b.y != k + 1: symexTarget("pg_dead")

proc sutPtrCapture(k: int) =
  ## The body alone reaches the object, through its capture.
  if k < 0 or k > 1000: return
  var b = PB()
  let pb = addr b
  let f = proc () =
    pb[].x = k
    pb.y = pb[].x + 1
  f()
  if b.y == k + 1 and k == 3: symexTarget("pc")
  if b.y != k + 1: symexTarget("pc_dead")

proc bumpThrough(v: var int, k: int) =
  v = k
  gpb[].y = gpb[].x + 1

proc sutPtrProcValue(k: int) =
  if k < 0 or k > 1000: return
  var b = PB()
  gpb = addr b
  let g = bumpThrough
  g(gpb[].x, k)
  if b.y == k + 1 and k == 3: symexTarget("pv")
  if b.y != k + 1: symexTarget("pv_dead")

suite "S8ca (4b): a heap lvalue a closure's body also reaches":

  test "nim":
    let h = nativeHits(sutHeapClosure, ks) + nativeHits(sutHeapProcValue, ks) +
            nativeHits(sutPtrLocal, ks) + nativeHits(sutPtrGlobal, ks) +
            nativeHits(sutPtrCapture, ks) + nativeHits(sutPtrProcValue, ks)
    for l in ["hc", "hp", "pl", "pg", "pc", "pv"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "passed by reference":
    clean(sutHeapClosure, "hc", sxSat)
    clean(sutHeapClosure, "hc_dead", sxUnsat)
    clean(sutHeapProcValue, "hp", sxSat)
    clean(sutHeapProcValue, "hp_dead", sxUnsat)

  test "`pb[].x`, through a pointer":
    clean(sutPtrLocal, "pl", sxSat)
    clean(sutPtrLocal, "pl_dead", sxUnsat)
    clean(sutPtrGlobal, "pg", sxSat)
    clean(sutPtrGlobal, "pg_dead", sxUnsat)
    clean(sutPtrCapture, "pc", sxSat)
    clean(sutPtrCapture, "pc_dead", sxUnsat)
    clean(sutPtrProcValue, "pv", sxSat)
    clean(sutPtrProcValue, "pv_dead", sxUnsat)

suite "S8ca (4): walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
