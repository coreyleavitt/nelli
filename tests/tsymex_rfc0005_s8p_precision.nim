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
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template reproduces(call: untyped; label: string): bool =
  ## Runs the SUT on the witness in a capture frame: the witness of a
  ## `sxSat` must drive the real code onto its label.
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

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

# ---- (1) a callee assigning a distinct or multi-variant result -----------------
#
# Real Nim: mkD(9) is D(9), mkD(-2) is D(4); mkMV(1) is (k: pkB, b: 3, j: pkA,
# c: 1), mkMV(0) is (k: pkA, a: 5, j: pkB, d: 2). Before S8p both callers were
# `weInternalWalkerFault`: `D(3)` is the identity pass-through (a plain int)
# and the multi-variant constructor's parse-time stand-in was an int too,
# which `retBindEq` met against the distinct / multi-variant `retSym`.

proc mkD(x: int): S8pD =
  if x > 0: result = S8pD(x)
  else: result = S8pD(4)

proc callD(x: int) =
  let d = mkD(x)
  if int(d) == 9: symexTarget("s8p_d_nine")
  if int(d) == 4 and x > 4: symexTarget("s8p_d_dead")

proc idD(d: S8pD): S8pD = d

proc callDPass(x: int) =
  let d = idD(S8pD(x))
  if int(d) == 7: symexTarget("s8p_dpass")

proc mkMV(x: int): S8pMV =
  if x > 0: result = S8pMV(k: pkB, b: 3, j: pkA, c: 1)
  else: result = S8pMV(k: pkA, a: 5, j: pkB, d: 2)

proc callMV(x: int) =
  let v = mkMV(x)
  if v.k == pkB and v.b == 3 and v.j == pkA and v.c == 1:
    symexTarget("s8p_mv_b")
  if v.k == pkA and v.a == 5 and v.j == pkB and v.d == 2:
    symexTarget("s8p_mv_a")
  if v.k == pkA and x > 0: symexTarget("s8p_mv_dead")

proc idMV(m: S8pMV): S8pMV = m

proc callMVPass(m: S8pMV) =
  let r = idMV(m)
  if r.k == pkB and r.b == 5 and r.j == pkB and r.d == 6:
    symexTarget("s8p_mvpass")

suite "S8p (1) a callee assigning a distinct or multi-variant result":
  test "oracle":
    check int(mkD(9)) == 9
    check int(mkD(-2)) == 4
    let m1 = mkMV(1)
    check m1.k == pkB and m1.b == 3 and m1.j == pkA and m1.c == 1
    symexCaptureBegin()
    callD(9); callDPass(7); callMV(1); callMV(0)
    callMVPass(S8pMV(k: pkB, b: 5, j: pkB, d: 6))
    let hits = symexCaptureEnd()
    check "s8p_d_nine" in hits
    check "s8p_dpass" in hits
    check "s8p_mv_b" in hits
    check "s8p_mv_a" in hits
    check "s8p_mvpass" in hits

  test "a distinct result binds its base value (was weInternalWalkerFault)":
    let r = symexFind(callD, tLabel("s8p_d_nine"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
      check reproduces(callD(r.witness[0]), "s8p_d_nine")
    let d = symexFind(callD, tLabel("s8p_d_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let p = symexFind(callDPass, tLabel("s8p_dpass"))
    checkpoint($p.status & " " & show(p.errors))
    check p.status == sxSat
    if p.status == sxSat:
      check p.witness[0] == 7

  test "a multi-variant result binds per axis (was weInternalWalkerFault)":
    let r = symexFind(callMV, tLabel("s8p_mv_b"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] > 0
      check reproduces(callMV(r.witness[0]), "s8p_mv_b")
    let a = symexFind(callMV, tLabel("s8p_mv_a"))
    checkpoint($a.status & " " & show(a.errors))
    check a.status == sxSat
    if a.status == sxSat:
      check a.witness[0] <= 0
    let d = symexFind(callMV, tLabel("s8p_mv_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a multi-variant passed through a callee":
    let r = symexFind(callMVPass, tLabel("s8p_mvpass"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat

# ---- (2) a multi-variant's zero value ------------------------------------------
#
# Real Nim zero-initialises `result`: every discriminator ordinal 0 (pkA) and
# every field 0. Before S8p the untouched result was `feUnsupportedOpHavoc`.

proc mvMaybe(x: int): S8pMV =
  if x > 0: result = S8pMV(k: pkB, b: x, j: pkB, d: 1)

proc mvBare(x: int): S8pMV =
  if x > 0: return
  result = S8pMV(k: pkB, b: 2, j: pkB, d: 2)

proc callMVZero(x: int) =
  let v = mvMaybe(x)
  if x <= 0 and v.k == pkA and v.a == 0 and v.j == pkA and v.c == 0:
    symexTarget("s8p_mvz")
  if x <= 0 and (v.k != pkA or v.j != pkA): symexTarget("s8p_mvz_dead")

proc callMVBare(x: int) =
  let v = mvBare(x)
  if x > 0 and v.k == pkA and v.j == pkA and v.c == 0: symexTarget("s8p_mvbare")
  if x > 0 and v.k == pkB: symexTarget("s8p_mvbare_dead")

suite "S8p (2) a multi-variant's zero value":
  test "oracle":
    let z = mvMaybe(0)
    check z.k == pkA and z.a == 0 and z.j == pkA and z.c == 0
    symexCaptureBegin()
    callMVZero(0); callMVBare(1)
    let hits = symexCaptureEnd()
    check "s8p_mvz" in hits
    check "s8p_mvbare" in hits

  test "an untouched multi-variant result is its zero value (was feUnsupportedOpHavoc)":
    let r = symexFind(callMVZero, tLabel("s8p_mvz"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.errors.len == 0
    let d = symexFind(callMVZero, tLabel("s8p_mvz_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a bare return of a multi-variant is its zero value":
    let r = symexFind(callMVBare, tLabel("s8p_mvbare"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    let d = symexFind(callMVBare, tLabel("s8p_mvbare_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

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

# ---- (5) add of a char to a string ---------------------------------------------
#
# Real Nim: addZ("ab") == "abz". Before S8p `s.add c` was
# `seUnsupportedStringOp` ("string add (non-string arg)").

proc addZ(s: string): string =
  result = s
  result.add 'z'

proc callAddZ(s: string) =
  let r = addZ(s)
  if r == "abz": symexTarget("s8p_addz")
  if r.len == 0: symexTarget("s8p_addz_dead")

proc addCharParam(s: string; c: char) =
  var t = s
  t.add c
  if t == "q!" : symexTarget("s8p_addc")
  if t.len != s.len + 1: symexTarget("s8p_addc_dead")

suite "S8p (5) add of a char to a string":
  test "oracle":
    check addZ("ab") == "abz"
    symexCaptureBegin()
    callAddZ("ab"); addCharParam("q", '!')
    let hits = symexCaptureEnd()
    check "s8p_addz" in hits
    check "s8p_addc" in hits

  test "result.add 'z' (was seUnsupportedStringOp)":
    let r = symexFind(callAddZ, tLabel("s8p_addz"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == "ab"
    let d = symexFind(callAddZ, tLabel("s8p_addz_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a symbolic char appended":
    let r = symexFind(addCharParam, tLabel("s8p_addc"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == "q"
      check r.witness[1] == uint8(ord('!'))   # a char witness renders as its byte
    let d = symexFind(addCharParam, tLabel("s8p_addc_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (6) a closure returning a tuple, a string or a seq -------------------------
#
# Real Nim: f(5) is (a: 5, b: 2); g(1) is "pos", g(-1) "neg"; h(5) is @[5, 2].
# Before S8p each declined (`feUnsupportedOp`: the funcSym has no sort for a
# multi-leaf or non-scalar range).

proc closTup(x: int) =
  let f = proc (y: int): tuple[a, b: int] = (a: y, b: 2)
  let t = f(x)
  if t.a == 5 and t.b == 2: symexTarget("s8p_ctup")
  if t.b != 2: symexTarget("s8p_ctup_dead")

proc closStr(x: int) =
  let g = proc (y: int): string =
    if y > 0: "pos" else: "neg"
  let s = g(x)
  if s == "pos": symexTarget("s8p_cstr")
  if s == "pos" and x <= 0: symexTarget("s8p_cstr_dead")

proc closSeq(x: int) =
  let h = proc (y: int): seq[int] = @[y, 2]
  let s = h(x)
  if s.len == 2 and s[0] == 5: symexTarget("s8p_cseq")
  if s.len != 2: symexTarget("s8p_cseq_dead")

proc closSeqIdx(x: int) =
  ## The index read straight off the call: its container is not a variable.
  let h = proc (y: int): seq[int] = @[y, 2]
  if h(x)[0] == 5: symexTarget("s8p_cseqix")
  if h(x)[1] != 2: symexTarget("s8p_cseqix_dead")

suite "S8p (6) a closure returning a tuple, a string or a seq":
  test "oracle":
    symexCaptureBegin()
    closTup(5); closStr(1); closSeq(5); closSeqIdx(5)
    let hits = symexCaptureEnd()
    check "s8p_ctup" in hits
    check "s8p_cstr" in hits
    check "s8p_cseq" in hits
    check "s8p_cseqix" in hits

  test "a two-field tuple result (was feUnsupportedOp)":
    let r = symexFind(closTup, tLabel("s8p_ctup"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(closTup, tLabel("s8p_ctup_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a string result (was feUnsupportedOp)":
    let r = symexFind(closStr, tLabel("s8p_cstr"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] > 0
    let d = symexFind(closStr, tLabel("s8p_cstr_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a seq result (was feUnsupportedOp)":
    let r = symexFind(closSeq, tLabel("s8p_cseq"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(closSeq, tLabel("s8p_cseq_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an index on the call itself (was weInternalWalkerFault)":
    ## `h(x)[0]`: the index statement asserted its container was a variable
    ## or a field (`lowerLeafInExpr`); the call is now bound to a `let`.
    let r = symexFind(closSeqIdx, tLabel("s8p_cseqix"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(closSeqIdx, tLabel("s8p_cseqix_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (6b) field-write edges -----------------------------------------------------
#
# Real Nim: setField(o, 9) leaves o == (a: 2, b: 9); catS(x) with x == "bc"
# makes o.s == "abc"; a variant arm field write keeps its decline (the
# discriminant check is not modelled on this route).

type
  S8pSV = object
    k: int
    s: string
  S8pV = object
    case kind: S8pK
    of pkA: va: int
    of pkB: vb: int

proc setField(o: var S8pObj; x: int) =
  o.b = x
  o.a += 1

proc varParamField(x: int) =
  var o = S8pObj(a: 1, b: 2)
  setField(o, x)
  if o.a == 2 and o.b == 9: symexTarget("s8p_vpf")
  if o.a != 2: symexTarget("s8p_vpf_dead")

proc catS(x: string) =
  var o = S8pSV(k: 1, s: "a")
  o.s &= x
  if o.s == "abc" and o.k == 1: symexTarget("s8p_cats")

proc variantArmWrite(x: int) =
  var v = S8pV(kind: pkA, va: 1)
  v.va = x
  if v.va == 6: symexTarget("s8p_varm")

suite "S8p (6b) field-write edges":
  test "oracle":
    symexCaptureBegin()
    varParamField(9); catS("bc"); variantArmWrite(6)
    let hits = symexCaptureEnd()
    check "s8p_vpf" in hits
    check "s8p_cats" in hits
    check "s8p_varm" in hits

  test "a var parameter's field writes reach the caller":
    let r = symexFind(varParamField, tLabel("s8p_vpf"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
    let d = symexFind(varParamField, tLabel("s8p_vpf_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "&= on a string field":
    let r = symexFind(catS, tLabel("s8p_cats"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == "bc"

  test "a variant arm field write is modelled (re-pinned by RFC-0005 S8s; declined here)":
    ## Real Nim: `v.va == x` after the write (the oracle above reaches the
    ## label with x == 6).
    let r = symexFind(variantArmWrite, tLabel("s8p_varm"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.errors.len == 0
    if r.status == sxSat:
      check r.witness[0] == 6

# ---- (7) walker version floor ---------------------------------------------------

suite "S8p (7) walker version":
  test "walker version is at least 164":
    check parseInt(symexWalkerVersion) >= 164
