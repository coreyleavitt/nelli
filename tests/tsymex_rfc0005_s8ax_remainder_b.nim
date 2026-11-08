## RFC-0005 (soundness channels) slice S8ax -- S8as's remainder.
##
## Each section below names the wrong verdict or the decline it closes.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## the debug build the test binary itself is).
##
## RFC-0005 S8cm: part 4 of 9 of this suite, with
## `tsymex_rfc0005_s8ax_remainder`, `tsymex_rfc0005_s8ax_remainder2`,
## `tsymex_rfc0005_s8ax_remainder3`, `tsymex_rfc0005_s8ax_remainder_c`,
## `tsymex_rfc0005_s8ax_remainder_d`, `tsymex_rfc0005_s8ax_remainder_e`,
## `tsymex_rfc0005_s8ax_remainder_f`, `tsymex_rfc0005_s8ax_remainder_g`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 132 s).

import std/[unittest, strutils, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8ax_remainder_b")

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & show(r.errors)
    check r.status == want
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (5) an opaque routine's raises, heap writes and other writes ------------
#
# WRONG VERDICTS before S8ax, each with `errors` empty: an inert opaque call
# never raised and always returned. `try: s8axBoom(v) except ValueError`
# was a false `sxUnsat`, a target after `s8axAlwaysRaise(v)` a false `sxSat`,
# a target after `s8axSpin(v)` (it never returns for `v == 2`) a false
# `sxSat`, and `tRaisedExn("ValueError")` through `s8axAlwaysRaise` a false
# `sxUnsat`. A nested opaque routine's write through a captured `let` ref
# was dropped (S8as skipped a capture that is not writable): a false
# `sxUnsat`. A `Defect` the body raises, caught around the call: a false
# `sxUnsat`.

type
  S8axNode = ref object
    val: int
  S8axErr = object of ValueError

var gS8axNode: S8axNode
var gS8axCast: int

proc s8axBoom(a: int) {.symexOpaque.} =
  if a == 3: raise newException(ValueError, "boom")

proc s8axAlwaysRaise(a: int) {.symexOpaque.} =
  raise newException(ValueError, "always")

proc s8axSpin(a: int) {.symexOpaque.} =
  var i = 0
  while a == 2: inc i

proc s8axDiv(a: int) {.symexOpaque.} =
  discard 10 div a

proc s8axRaisesBase(a: int) {.symexOpaque, raises: [ValueError].} =
  if a == 4: raise newException(S8axErr, "sub")

proc s8axBump(n: S8axNode) {.symexOpaque.} =
  n.val = 7

proc s8axSetVar(x: var int) {.symexOpaque.} =
  x = 9

proc s8axSetGlobalNode() {.symexOpaque.} =
  gS8axNode = S8axNode(val: 3)

proc s8axCastWrite(a: int) {.symexOpaque.} =
  gS8axCast = cast[int](a)

proc sutOpaqueRaise(v: int) =
  try:
    s8axBoom(v)
  except ValueError:
    if v == 3: symexTarget("or")

proc sutOpaqueAlways(v: int) =
  s8axAlwaysRaise(v)
  if v == 1: symexTarget("oa")

proc sutOpaqueSpin(v: int) =
  s8axSpin(v)
  if v == 2: symexTarget("os")

proc sutOpaqueRaiseBoundary(v: int) =
  s8axAlwaysRaise(v)

proc sutOpaqueDefect(v: int) =
  try:
    s8axDiv(v)
  except DivByZeroDefect:
    symexTarget("od")

proc sutOpaqueSubtype(v: int) =
  try:
    s8axRaisesBase(v)
  except S8axErr:
    symexTarget("osub")

proc sutOpaqueHeap(v: int) =
  let n = S8axNode(val: 1)
  s8axBump(n)
  if n.val == 7 and v == 1: symexTarget("oh")
  if n == nil: symexTarget("oh_dead")

proc sutOpaqueVar(v: int) =
  var x = 0
  var y = 3
  s8axSetVar(x)
  if x == 9 and v == 1: symexTarget("ov")
  if y != 3: symexTarget("ov_dead")

proc sutOpaqueGlobalRef(v: int) =
  gS8axNode = S8axNode(val: 0)
  s8axSetGlobalNode()
  if gS8axNode.val == 3 and v == 1: symexTarget("ogn")

proc sutOpaqueLetCapture(v: int) =
  let c = S8axNode(val: 1)
  proc w8ax() {.symexOpaque.} =
    c.val = 5
  w8ax()
  if c.val == 5 and v == 1: symexTarget("olc")

proc sutOpaqueCast(v: int) =
  gS8axCast = 0
  s8axCastWrite(v)
  if gS8axCast == 5 and v == 5: symexTarget("oc")

suite "RFC-0005 S8ax (5): an opaque routine's effects":
  test "a raise its `raises` list names is forked":
    ## RED before S8ax: sxUnsat, `errors` empty.
    verdict(sutOpaqueRaise, "or", sxSat)
  test "a target past a call that always raises is not reached":
    ## RED before S8ax: sxSat, `errors` empty. The returning path is a
    ## replayed candidate now, and the replay raises.
    let r = symexFind(sutOpaqueAlways, tLabel("oa"))
    checkpoint show(r.errors)
    check r.status != sxSat
    check r.errors.hasKind(feOpaqueEffectHavoc)
  test "a raise reaches the boundary":
    ## RED before S8ax: sxUnsat, `errors` empty.
    let r = symexFind(sutOpaqueRaiseBoundary, tRaisedExn("ValueError"))
    checkpoint show(r.errors)
    check r.status == sxRaised
  test "a routine that may not return declines":
    ## RED before S8ax: sxSat, `errors` empty (and a replay of it would not
    ## end).
    pinDecline(sutOpaqueSpin, declKey, feOpaqueCallUnmodelled, tLabel("os"), "`while` loop")
  test "a Defect caught around the call is raised":
    ## RED before S8ax: sxUnsat, `errors` empty. S8ax declined it; RFC-0005
    ## S8be forks the `DivByZeroDefect` the body raises (`10 div 0`), and
    ## the replay confirms it.
    verdict(sutOpaqueDefect, "od", sxSat)
  test "an arm naming a subtype of a raised type is entered":
    ## RED before S8ax: sxUnsat, `errors` empty. S8ax declined it; RFC-0005
    ## S8be splits the raise into `S8axErr`, a candidate the replay settles:
    ## confirmed on the witness `4`, refuted on any other (the model the
    ## Z3 build picks decides which).
    let r = symexFind(sutOpaqueSubtype, tLabel("osub"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check not r.errors.hasKind(feOpaqueCallUnmodelled)
    check r.status == sxSat or r.errors.hasKind(feReplayRefuted)
  test "a write through a ref argument reaches its cell":
    ## S8as declined the call (a ref argument).
    verdict(sutOpaqueHeap, "oh", sxSat)
    verdict(sutOpaqueHeap, "oh_dead", sxUnsat)
  test "a write through a var argument reaches the variable alone":
    verdict(sutOpaqueVar, "ov", sxSat)
    verdict(sutOpaqueVar, "ov_dead", sxUnsat)
  test "a global that reaches heap cells is rebound":
    ## S8as declined the call (a ref global).
    verdict(sutOpaqueGlobalRef, "ogn", sxSat)
  test "a write through a captured `let` ref reaches its cell":
    ## RED before S8ax: sxUnsat, `errors` empty.
    verdict(sutOpaqueLetCapture, "olc", sxSat)
  test "a cast havocs every global and heap instead of declining":
    verdict(sutOpaqueCast, "oc", sxSat)

type S8axRR = ref object
  a: int

type S8axPair = object
  a, b: int
