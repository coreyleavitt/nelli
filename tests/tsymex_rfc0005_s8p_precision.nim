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
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8p_precision_b`, `tsymex_rfc0005_s8p_precision_c`. Split so
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
