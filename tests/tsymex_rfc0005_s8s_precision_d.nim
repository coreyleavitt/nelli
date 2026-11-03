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
##
## RFC-0005 S8cm: part 5 of 8 of this suite, with
## `tsymex_rfc0005_s8s_precision`, `tsymex_rfc0005_s8s_precision_b`,
## `tsymex_rfc0005_s8s_precision_h`, `tsymex_rfc0005_s8s_precision_c`,
## `tsymex_rfc0005_s8s_precision_e`, `tsymex_rfc0005_s8s_precision_f`,
## `tsymex_rfc0005_s8s_precision_g`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 134 s).

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
