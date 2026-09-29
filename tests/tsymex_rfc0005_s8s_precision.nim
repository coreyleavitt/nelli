## RFC-0005 (soundness channels) slice S8s -- S8p's precision remainder.
##
## Four places the walker gave up on (or faulted over) code whose behaviour
## is fully determined, and one cpp compile failure. S8p reported them.
## Every expected value was probed against the real compiler (Nim 2.2.10,
## debug build) by the oracle test of each suite, which runs the SUT itself.
##   (1) a `seq[uint8]` element compared against a literal
##       (was `weInternalWalkerFault`, "field 'bv8' ... kind = svBV64");
##   (2) the zero value of a multi-variant whose ordinal 0 falls in an
##       `else` arm (was `feUnsupportedOpHavoc`);
##   (3) a callee returning an `array` (was `feUnsupportedOpHavoc`);
##   (4) a write to a variant arm field and a positional tuple-element
##       write (was `feUnsupportedStmtKind`);
##   (5) the walker version floor.
## The cpp compile failure of `tsymex_r6_n43_parity` (a deleted
## `std::atomic::operator=`) is pinned by that suite compiling on cpp.
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

# ---- (1) a seq[uint8] element against a literal -----------------------------------
#
# Real Nim: byteLit(7) reaches "s8s_bl"; v[1] is always 1. Before S8s the
# comparison was `weInternalWalkerFault`: the literal's element was built as a
# 64-bit value and the comparison read its `bv8` field.

proc byteLit(x: uint8) =
  let v = @[x, 1'u8]
  if v[0] == 7: symexTarget("s8s_bl")
  if v[1] != 1: symexTarget("s8s_bl_dead")

proc byteLitConst(x: int) =
  ## No input in the literal at all: the local literal alone faulted.
  let v = @[3'u8, 250'u8]
  if v[0] == 3 and x == 4: symexTarget("s8s_blc")
  if v[1] != 250: symexTarget("s8s_blc_dead")

proc byteLitSigned(x: int8) =
  let v = @[x, -1'i8]
  if v[0] == -5 and v[1] < 0: symexTarget("s8s_bls")
  if v[1] >= 0: symexTarget("s8s_bls_dead")

suite "S8s (1) a seq[uint8] element against a literal":
  test "oracle":
    symexCaptureBegin()
    byteLit(7); byteLitConst(4); byteLitSigned(-5)
    let hits = symexCaptureEnd()
    check "s8s_bl" in hits
    check "s8s_blc" in hits
    check "s8s_bls" in hits

  test "an input byte in the literal (was weInternalWalkerFault)":
    let r = symexFind(byteLit, tLabel("s8s_bl"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7'u8
      check reproduces(byteLit(r.witness[0]), "s8s_bl")
    let d = symexFind(byteLit, tLabel("s8s_bl_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a constant byte literal":
    let r = symexFind(byteLitConst, tLabel("s8s_blc"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(byteLitConst, tLabel("s8s_blc_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a signed 8-bit literal":
    let r = symexFind(byteLitSigned, tLabel("s8s_bls"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == -5'i8
    let d = symexFind(byteLitSigned, tLabel("s8s_bls_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (2) a multi-variant whose ordinal 0 is in an else arm ------------------------
#
# Real Nim zero-initialises `result`: both discriminators s3A (ordinal 0, which
# each axis's `else` arm covers) and every field 0, the else arms' too. Before
# S8s the untouched result was `feUnsupportedOpHavoc`.

type
  S8sK = enum s3A, s3B, s3C
  S8sMVE = object
    case k: S8sK
    of s3B: b: int
    else: e: int
    case j: S8sK
    of s3C: c: int
    else: f: int
  S8sVE = object
    ## A single `case` whose ordinal 0 is in its `else` arm.
    case vk: S8sK
    of s3C: vc: int
    else: ve: int

proc mveMaybe(x: int): S8sMVE =
  if x > 0: result = S8sMVE(k: s3B, b: x, j: s3C, c: 1)

proc mveBare(x: int): S8sMVE =
  if x > 0: return
  result = S8sMVE(k: s3B, b: 2, j: s3C, c: 2)

proc callMVE(x: int) =
  let v = mveMaybe(x)
  if x <= 0 and v.k == s3A and v.e == 0 and v.j == s3A and v.f == 0:
    symexTarget("s8s_mve")
  if x <= 0 and (v.k != s3A or v.j != s3A): symexTarget("s8s_mve_dead")
  # The else arms' fields are bound too: `retBindEq` guarded each arm's
  # fields by `disc == <arm key>`, and an else arm's key is -1.
  if x <= 0 and (v.e != 0 or v.f != 0): symexTarget("s8s_mve_edead")
  if x > 0 and v.b == 5: symexTarget("s8s_mve_b")

proc callMVEBare(x: int) =
  let v = mveBare(x)
  if x > 0 and v.k == s3A and v.f == 0: symexTarget("s8s_mvebare")
  if x > 0 and v.k != s3A: symexTarget("s8s_mvebare_dead")

proc veMaybe(x: int): S8sVE =
  if x > 0: result = S8sVE(vk: s3C, vc: x)

proc callVE(x: int) =
  let v = veMaybe(x)
  if x <= 0 and v.vk == s3A and v.ve == 0: symexTarget("s8s_ve")
  if x <= 0 and v.vk != s3A: symexTarget("s8s_ve_dead")
  if x <= 0 and v.ve != 0: symexTarget("s8s_ve_edead")

proc mveParam(m: S8sMVE) =
  ## An input multi-variant: every ordinal an `else` arm covers is a legal
  ## discriminator value (s3A and s3C on `k`, s3A and s3B on `j`).
  if m.k == s3A and m.e == 4: symexTarget("s8s_mvpe")
  if m.j == s3B and m.f == 2 and m.k == s3C: symexTarget("s8s_mvpf")

type
  S8sR = range[0..5]
  S8sK2 = enum s2A, s2B
  S8sMVR = object
    ## A multi-variant with a `range` discriminator and an `else` arm: no
    ## enum tags, so the else arm covers 1..5 of `r`'s declared range.
    case r: S8sR
    of 0: z: int
    else: w: int
    case q: S8sK2
    of s2A: nf: int
    of s2B: nt: int

proc mvrParam(m: S8sMVR) =
  if m.r == 3 and m.w == 7 and m.q == s2B: symexTarget("s8s_mvr")

suite "S8s (2) a multi-variant whose ordinal 0 is in an else arm":
  test "oracle":
    let z = mveMaybe(0)
    check z.k == s3A and z.e == 0 and z.j == s3A and z.f == 0
    let y = veMaybe(0)
    check y.vk == s3A and y.ve == 0
    symexCaptureBegin()
    callMVE(0); callMVE(5); callMVEBare(1); callVE(0)
    mveParam(S8sMVE(k: s3A, e: 4, j: s3C, c: 0))
    mveParam(S8sMVE(k: s3C, e: 0, j: s3B, f: 2))
    mvrParam(S8sMVR(r: 3, w: 7, q: s2B, nt: 0))
    let hits = symexCaptureEnd()
    check "s8s_mvpe" in hits
    check "s8s_mvpf" in hits
    check "s8s_mvr" in hits
    check "s8s_mve" in hits
    check "s8s_mve_b" in hits
    check "s8s_mvebare" in hits
    check "s8s_ve" in hits

  test "an untouched result is its zero value (was feUnsupportedOpHavoc)":
    let r = symexFind(callMVE, tLabel("s8s_mve"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.errors.len == 0
    let d = symexFind(callMVE, tLabel("s8s_mve_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let e = symexFind(callMVE, tLabel("s8s_mve_edead"))
    checkpoint($e.status & " " & show(e.errors))
    check e.status == sxUnsat
    let b = symexFind(callMVE, tLabel("s8s_mve_b"))
    checkpoint($b.status & " " & show(b.errors))
    check b.status == sxSat
    if b.status == sxSat:
      check b.witness[0] == 5

  test "a bare return is its zero value":
    let r = symexFind(callMVEBare, tLabel("s8s_mvebare"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    let d = symexFind(callMVEBare, tLabel("s8s_mvebare_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an input's discriminator ranges over its else arms (was a false sxUnsat)":
    ## `allocateSym` constrained each axis's discriminator to its explicit
    ## tags plus the else arm's sentinel ordinal (-1), never to an ordinal
    ## the `else` arm covers: both labels were `sxUnsat`.
    let r = symexFind(mveParam, tLabel("s8s_mvpe"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].k == s3A
      check reproduces(mveParam(r.witness[0]), "s8s_mvpe")
    let f = symexFind(mveParam, tLabel("s8s_mvpf"))
    checkpoint($f.status & " " & show(f.errors))
    check f.status == sxSat
    if f.status == sxSat:
      check reproduces(mveParam(f.witness[0]), "s8s_mvpf")

  test "a range discriminator's else values render in the witness":
    ## The else arm's values (1..5) became reachable with the domain fix;
    ## the multi-variant witness emitter rendered no branch for them (the
    ## `default` fallback: `r: 0`), so the witness would not reach the label.
    let r = symexFind(mvrParam, tLabel("s8s_mvr"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].r == 3
      check r.witness[0].w == 7
      check reproduces(mvrParam(r.witness[0]), "s8s_mvr")

  test "a single-case variant with ordinal 0 in its else arm":
    let r = symexFind(callVE, tLabel("s8s_ve"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    check r.errors.len == 0
    let d = symexFind(callVE, tLabel("s8s_ve_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let e = symexFind(callVE, tLabel("s8s_ve_edead"))
    checkpoint($e.status & " " & show(e.errors))
    check e.status == sxUnsat

# ---- (3) a callee returning an array ----------------------------------------------
#
# Real Nim: mkArr(5) is [5, 2, 3]; arrMaybe(4) is [0, 4], arrMaybe(0) is
# [0, 0]. Before S8s the caller's result was `feUnsupportedOpHavoc`
# (`retBindEq` had no array arm).

proc mkArr(x: int): array[3, int] =
  result = [x, 2, 3]

proc callArr(x: int) =
  let a = mkArr(x)
  if a[0] == 5 and a[1] == 2: symexTarget("s8s_arr")
  if a[2] != 3: symexTarget("s8s_arr_dead")

proc arrMaybe(x: int): array[2, int] =
  if x > 0: result = [0, x]

proc callArrZero(x: int) =
  let a = arrMaybe(x)
  if x > 0 and a[1] == 4 and a[0] == 0: symexTarget("s8s_arrz")
  if x <= 0 and a[1] != 0: symexTarget("s8s_arrz_dead")

proc idArr(a: array[2, int]): array[2, int] = a

proc callArrPass(x: int) =
  let a = idArr([x, 9])
  if a[0] == 3 and a[1] == 9: symexTarget("s8s_arrp")
  if a[1] != 9: symexTarget("s8s_arrp_dead")

proc closArr(x: int) =
  let f = proc (y: int): array[2, int] = [y, 2]
  let a = f(x)
  if a[0] == 4 and a[1] == 2: symexTarget("s8s_carr")
  if a[1] != 2: symexTarget("s8s_carr_dead")

suite "S8s (3) a callee returning an array":
  test "oracle":
    check mkArr(5) == [5, 2, 3]
    check arrMaybe(4) == [0, 4]
    check arrMaybe(0) == [0, 0]
    symexCaptureBegin()
    callArr(5); callArrZero(4); callArrPass(3); closArr(4)
    let hits = symexCaptureEnd()
    check "s8s_carr" in hits
    check "s8s_arr" in hits
    check "s8s_arrz" in hits
    check "s8s_arrp" in hits

  test "an array result binds its elements (was feUnsupportedOpHavoc)":
    let r = symexFind(callArr, tLabel("s8s_arr"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 5
    let d = symexFind(callArr, tLabel("s8s_arr_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an untouched array result is zero":
    let r = symexFind(callArrZero, tLabel("s8s_arrz"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(callArrZero, tLabel("s8s_arrz_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an array passed through a callee":
    let r = symexFind(callArrPass, tLabel("s8s_arrp"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
    let d = symexFind(callArrPass, tLabel("s8s_arrp_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a closure returning an array (was feUnsupportedOp)":
    let r = symexFind(closArr, tLabel("s8s_carr"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(closArr, tLabel("s8s_carr_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (4) variant arm field writes and positional tuple-element writes -------------
#
# Real Nim: a write to an arm field whose arm is not the active one raises
# `FieldDefect` ("field 'vb' is not accessible for type 'S8sV' using
# 'kind = s4A'"), and leaves the object unchanged. Before S8s every form here
# was `feUnsupportedStmtKind`.

type
  S8sK4 = enum s4A, s4B
  S8sV = object
    tag: int
    case kind: S8sK4
    of s4A: va: int
    of s4B: vb: int
  S8sMV = object
    case k: S8sK4
    of s4A: a: int
    of s4B: b: int
    case j: S8sK4
    of s4A: c: int
    of s4B: d: int

proc armWrite(x: int) =
  var v = S8sV(tag: 1, kind: s4A, va: 1)
  v.va = x
  if v.va == 6 and v.tag == 1: symexTarget("s8s_aw")
  if v.kind != s4A: symexTarget("s8s_aw_dead")

proc armAug(x: int) =
  var v = S8sV(tag: 1, kind: s4B, vb: 10)
  if x > -1000 and x < 1000:
    v.vb += x
  if v.vb == 13: symexTarget("s8s_aa")
  if v.vb == 10 and x == 3: symexTarget("s8s_aa_dead")

proc armWrongArm(x: int) =
  var v = S8sV(tag: 1, kind: s4A, va: 1)
  try:
    if x > 0: v.vb = x
    symexTarget("s8s_ww_ok")
  except FieldDefect:
    symexTarget("s8s_ww_raised")
  if x > 0 and v.va != 1: symexTarget("s8s_ww_dead")

proc armParam(v: S8sV; x: int) =
  ## The discriminator is an input: the write is in-arm only when it is s4A.
  var w = v
  try:
    w.va = x
    if w.va == 6: symexTarget("s8s_ap")
  except FieldDefect:
    symexTarget("s8s_ap_raised")

proc armOrder(x: int) =
  ## Nim checks the field (computing its address) before it evaluates the
  ## value: out of the arm, `v.vb = 100 div x` raises `FieldDefect` even
  ## when `x == 0`.
  var v = S8sV(tag: 1, kind: s4A, va: 1)
  try:
    v.vb = 100 div x
    symexTarget("s8s_ord_ok")
  except FieldDefect:
    symexTarget("s8s_ord_field")
  except DivByZeroDefect:
    symexTarget("s8s_ord_div")

proc mvArmWrite(x: int) =
  var m = S8sMV(k: s4A, a: 1, j: s4B, d: 2)
  m.d = x
  m.a += 1
  if m.d == 8 and m.a == 2: symexTarget("s8s_mvw")
  if m.a != 2: symexTarget("s8s_mvw_dead")

type
  S8sHolder = object
    v: S8sV
    n: int
  S8sArmTup = object
    case kind: S8sK4
    of s4A: t: tuple[p, q: int]
    of s4B: z: int

proc elseArmWrite(v0: S8sVE; x: int) =
  ## An `else` arm's field: in the arm while `vk` is s3A or s3B. The value
  ## is an input: a constructor naming an `else`-covered tag
  ## (`S8sVE(vk: s3B, ve: 1)`) still declines (reported, not fixed here).
  if v0.vk == s3C: return
  var v = v0
  try:
    v.ve = x
    if v.ve == 5: symexTarget("s8s_ew")
    v.vc = 1        # vc is s3C's field: FieldDefect
    symexTarget("s8s_ew_dead")
  except FieldDefect:
    symexTarget("s8s_ew_raised")

proc plainWrite(x: int) =
  var v = S8sV(tag: 1, kind: s4B, vb: 2)
  v.tag = x
  if v.tag == 7 and v.vb == 2: symexTarget("s8s_pw")
  if v.vb != 2: symexTarget("s8s_pw_dead")

proc nestedVariant(x: int) =
  ## A variant held in an object, and a tuple held in a variant arm.
  var h = S8sHolder(v: S8sV(tag: 0, kind: s4A, va: 1), n: 3)
  h.v.va = x
  var a = S8sArmTup(kind: s4A, t: (p: 1, q: 2))
  a.t.q = x
  if h.v.va == 4 and h.n == 3 and a.t.q == 4 and a.t.p == 1:
    symexTarget("s8s_nv")
  if h.n != 3 or a.t.p != 1: symexTarget("s8s_nv_dead")

proc setVa(v: var S8sV; x: int) =
  v.va = x

proc varParamVariant(x: int) =
  var v = S8sV(tag: 2, kind: s4A, va: 0)
  setVa(v, x)
  if v.va == 9 and v.tag == 2: symexTarget("s8s_vpv")
  if v.tag != 2: symexTarget("s8s_vpv_dead")

proc tupPos(x, y: int) =
  var q = (a: 1, b: 2)
  q[0] = x
  if y > -1000 and y < 1000: q[1] += y
  if q[0] == 4 and q[1] == 7: symexTarget("s8s_tp")
  if y == 0 and q[1] != 2: symexTarget("s8s_tp_dead")

proc tupPosNested(x: int) =
  var q = (a: (b: 1, c: 2), d: 3)
  q[0][1] = x
  q.a[0] += 1
  if q.a.b == 2 and q.a.c == 9 and q.d == 3: symexTarget("s8s_tpn")
  if q.d != 3: symexTarget("s8s_tpn_dead")

suite "S8s (4) variant arm field writes and positional tuple writes":
  test "oracle":
    symexCaptureBegin()
    armWrite(6); armAug(3); armWrongArm(1); armWrongArm(0)
    armParam(S8sV(tag: 0, kind: s4A, va: 0), 6)
    armParam(S8sV(tag: 0, kind: s4B, vb: 0), 6)
    mvArmWrite(8); tupPos(4, 5); tupPosNested(9)
    elseArmWrite(S8sVE(vk: s3A, ve: 0), 5); plainWrite(7); nestedVariant(4); varParamVariant(9)
    let hits = symexCaptureEnd()
    check "s8s_ew" in hits
    check "s8s_ew_raised" in hits
    check "s8s_ew_dead" notin hits
    check "s8s_pw" in hits
    check "s8s_nv" in hits
    check "s8s_vpv" in hits
    symexCaptureBegin()
    armOrder(0)
    let ord0 = symexCaptureEnd()
    check "s8s_ord_field" in ord0
    check "s8s_ord_div" notin ord0
    check "s8s_aw" in hits
    check "s8s_aa" in hits
    check "s8s_ww_raised" in hits
    check "s8s_ww_ok" in hits
    check "s8s_ww_dead" notin hits
    check "s8s_ap" in hits
    check "s8s_ap_raised" in hits
    check "s8s_mvw" in hits
    check "s8s_tp" in hits
    check "s8s_tpn" in hits

  test "an in-arm field write (was feUnsupportedStmtKind)":
    let r = symexFind(armWrite, tLabel("s8s_aw"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
    let d = symexFind(armWrite, tLabel("s8s_aw_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an augmented in-arm field write":
    let r = symexFind(armAug, tLabel("s8s_aa"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
    let d = symexFind(armAug, tLabel("s8s_aa_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an out-of-arm field write raises FieldDefect":
    let r = symexFind(armWrongArm, tLabel("s8s_ww_raised"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] > 0
      check reproduces(armWrongArm(r.witness[0]), "s8s_ww_raised")
    let o = symexFind(armWrongArm, tLabel("s8s_ww_ok"))
    checkpoint($o.status & " " & show(o.errors))
    check o.status == sxSat
    if o.status == sxSat:
      check o.witness[0] <= 0
    let d = symexFind(armWrongArm, tLabel("s8s_ww_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a symbolic discriminator decides the arm":
    let r = symexFind(armParam, tLabel("s8s_ap"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].kind == s4A
      check r.witness[1] == 6
      check reproduces(armParam(r.witness[0], r.witness[1]), "s8s_ap")
    let e = symexFind(armParam, tLabel("s8s_ap_raised"))
    checkpoint($e.status & " " & show(e.errors))
    check e.status == sxSat
    if e.status == sxSat:
      check e.witness[0].kind == s4B
      check reproduces(armParam(e.witness[0], e.witness[1]), "s8s_ap_raised")

  test "the field check comes before the value":
    let r = symexFind(armOrder, tLabel("s8s_ord_field"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    let d = symexFind(armOrder, tLabel("s8s_ord_div"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat
    let o = symexFind(armOrder, tLabel("s8s_ord_ok"))
    checkpoint($o.status & " " & show(o.errors))
    check o.status == sxUnsat

  test "an else arm's field write, and the other arm's raising":
    let r = symexFind(elseArmWrite, tLabel("s8s_ew"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].vk != s3C
      check r.witness[1] == 5
      check reproduces(elseArmWrite(r.witness[0], r.witness[1]), "s8s_ew")
    let e = symexFind(elseArmWrite, tLabel("s8s_ew_raised"))
    checkpoint($e.status & " " & show(e.errors))
    check e.status == sxSat
    if e.status == sxSat:
      check reproduces(elseArmWrite(e.witness[0], e.witness[1]),
                       "s8s_ew_raised")
    let d = symexFind(elseArmWrite, tLabel("s8s_ew_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a plain variant field write":
    let r = symexFind(plainWrite, tLabel("s8s_pw"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 7
    let d = symexFind(plainWrite, tLabel("s8s_pw_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "a variant in an object, and a tuple in a variant arm":
    let r = symexFind(nestedVariant, tLabel("s8s_nv"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
    let d = symexFind(nestedVariant, tLabel("s8s_nv_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "an arm field written through a var parameter":
    let r = symexFind(varParamVariant, tLabel("s8s_vpv"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
    let d = symexFind(varParamVariant, tLabel("s8s_vpv_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "arm field writes on a multi-variant":
    let r = symexFind(mvArmWrite, tLabel("s8s_mvw"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 8
    let d = symexFind(mvArmWrite, tLabel("s8s_mvw_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "positional tuple-element writes (was feUnsupportedStmtKind)":
    let r = symexFind(tupPos, tLabel("s8s_tp"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check r.witness[1] == 5
    let d = symexFind(tupPos, tLabel("s8s_tp_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

  test "nested positional and named tuple writes":
    let r = symexFind(tupPosNested, tLabel("s8s_tpn"))
    checkpoint($r.status & " " & show(r.errors))
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 9
    let d = symexFind(tupPosNested, tLabel("s8s_tpn_dead"))
    checkpoint($d.status & " " & show(d.errors))
    check d.status == sxUnsat

# ---- (5) walker version floor -----------------------------------------------------

suite "S8s (5) walker version":
  test "walker version is at least 167":
    check parseInt(symexWalkerVersion) >= 167
