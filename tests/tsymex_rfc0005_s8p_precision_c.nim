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
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8p_precision`, `tsymex_rfc0005_s8p_precision_b`. Split so
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
      ## RFC-0005 S8am: a char witness renders Nim's own `char` (was
      ## `uint8`, per the comment here when this test was first written --
      ## see `IRType.isChar`'s own doc comment).
      check r.witness[1] == '!'
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
