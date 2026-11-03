## RFC-0005 (soundness channels) slice S8p -- S8n's precision remainder.
##
## Six places the walker gave up on (or faulted over) code whose behaviour
## is fully determined. S8n reported them. Every expected value was probed
## against the real compiler (Nim 2.2.10, debug build) by the oracle test of
## each suite, which runs the SUT itself.
##   (1) a callee assigning a `distinct` or multi-variant result
##       (was `weInternalWalkerFault`, "retBindEq: kind mismatch");
##   (2) a multi-variant's zero value;
##   (3) the SUT's own frame reading `result` before writing it;
##   (4) field assignment, plain and augmented, on a value tuple / object;
##   (5) `add` of a char to a string;
##   (6) a closure returning a multi-field tuple, a `string` or a `seq`;
##   (7) the walker version floor.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8p_precision`, `tsymex_rfc0005_s8p_precision_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 75 s).

import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

type
  S8pK = enum pkA, pkB
  S8pMV = object
    ## Two `case` sections: a multi-variant.
    case k: S8pK
    of pkA: a: int
    of pkB: b: int
    case j: S8pK
    of pkA: c: int
    of pkB: d: int
  S8pD = distinct int
  S8pObj = object
    a: int
    b: int
  S8pNest = object
    inner: S8pObj
    tag: bool

# ---- (3) the SUT's own frame reading result -------------------------------------
#
# Real Nim: sutResult(7) reaches "ten" (0 + 3 + 7); `result < 3` never holds.
# Before S8p the read was `feGlobalReadUnmodelled`: the IR carried no return
# type for the SUT, so there was no type to take the zero of.

proc sutResult(x: int): int =
  result += 3
  if x > 0 and x < 1000: result += x
  if result == 10: symexTarget("s8p_sut_ten")
  if result < 3: symexTarget("s8p_sut_dead")

proc sutResultBool(b: bool): bool =
  if not result and b: symexTarget("s8p_sutb")
  if result: symexTarget("s8p_sutb_dead")

proc sutResultTuple(x: int): tuple[a, b: int] =
  if x > 0 and x < 1000: result.a += x
  if result.a == 4 and result.b == 0: symexTarget("s8p_sutt")
  if result.b != 0: symexTarget("s8p_sutt_dead")

suite "S8p (3) the SUT's own frame reading result":
  test "oracle":
    symexCaptureBegin()
    discard sutResult(7); discard sutResultBool(true); discard sutResultTuple(4)
    let hits = symexCaptureEnd()
    check "s8p_sut_ten" in hits
    check "s8p_sutb" in hits
    check "s8p_sutt" in hits

  test "an int result reads zero (was feGlobalReadUnmodelled)":
    let r = symexFind(sutResult, tLabel("s8p_sut_ten"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
    let d = symexFind(sutResult, tLabel("s8p_sut_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a bool result reads false":
    let r = symexFind(sutResultBool, tLabel("s8p_sutb"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == true
    let d = symexFind(sutResultBool, tLabel("s8p_sutb_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a tuple result reads zero fields":
    let r = symexFind(sutResultTuple, tLabel("s8p_sutt"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(sutResultTuple, tLabel("s8p_sutt_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (4) field assignment on a value tuple / object -----------------------------
#
# Real Nim: tupAug(5) is (a: 6, b: 2); objSet(6) reaches its label; nested
# writes change only their own field. Before S8p a plain field write was
# `feUnsupportedStmtKind` ("unsupported nnkAsgn shape") and an augmented one
# `feUnsupportedStmtKind` ("LHS ... is not a simple variable").

proc tupAug(x: int): tuple[a, b: int] =
  result = (a: 1, b: 2)
  if x > 0 and x < 1000: result.a += x

proc callTupAug(x: int) =
  let t = tupAug(x)
  if t.a == 6 and t.b == 2: symexTarget("s8p_taug")
  if t.b != 2: symexTarget("s8p_taug_dead")

proc objSet(x: int) =
  var o = S8pObj(a: 1, b: 2)
  o.a = x
  if o.a == 6 and o.b == 2: symexTarget("s8p_oset")
  if o.b != 2: symexTarget("s8p_oset_dead")

proc objAugOps(x: int) =
  var o = S8pObj(a: 10, b: 3)
  if x > -1000 and x < 1000:
    o.a -= x
    o.b *= 2
  if o.a == 4 and o.b == 6: symexTarget("s8p_oaug")
  if o.b == 3 and x == 0: symexTarget("s8p_oaug_dead")

proc nestedSet(x: int) =
  var n = S8pNest(inner: S8pObj(a: 1, b: 2), tag: false)
  n.inner.b = x
  n.tag = true
  if n.inner.b == 11 and n.inner.a == 1 and n.tag: symexTarget("s8p_nest")
  if n.inner.a != 1: symexTarget("s8p_nest_dead")

proc fieldOverflow(x: int) =
  var o = S8pObj(a: high(int), b: 0)
  try:
    o.a += x
    symexTarget("s8p_fov_ok")
  except OverflowDefect:
    symexTarget("s8p_fov_raised")

suite "S8p (4) field assignment on a value tuple or object":
  test "oracle":
    let t = tupAug(5)
    check t.a == 6 and t.b == 2
    symexCaptureBegin()
    callTupAug(5); objSet(6); objAugOps(6); nestedSet(11)
    fieldOverflow(1); fieldOverflow(0)
    let hits = symexCaptureEnd()
    check "s8p_taug" in hits
    check "s8p_oset" in hits
    check "s8p_oaug" in hits
    check "s8p_nest" in hits
    check "s8p_fov_ok" in hits
    check "s8p_fov_raised" in hits

  test "result.a += x (was feUnsupportedStmtKind)":
    let r = symexFind(callTupAug, tLabel("s8p_taug"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(callTupAug, tLabel("s8p_taug_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "o.a = x on a local object (was feUnsupportedStmtKind)":
    let r = symexFind(objSet, tLabel("s8p_oset"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
    let d = symexFind(objSet, tLabel("s8p_oset_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "-= and *= on fields":
    let r = symexFind(objAugOps, tLabel("s8p_oaug"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
    let d = symexFind(objAugOps, tLabel("s8p_oaug_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a nested field write changes only its own field":
    let r = symexFind(nestedSet, tLabel("s8p_nest"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 11
    let d = symexFind(nestedSet, tLabel("s8p_nest_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an augmented field write keeps the overflow check":
    let r = symexFind(fieldOverflow, tLabel("s8p_fov_raised"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] > 0
    let o = symexFind(fieldOverflow, tLabel("s8p_fov_ok"))
    checkpoint($o.status & " " & show(o.errors))
    check o.status == sxSat
    if o.status == sxSat:
      check o.witness[0] <= 0
