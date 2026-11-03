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
## RFC-0005 S8cm: part 5 of 7 of this suite, with
## `tsymex_rfc0005_s8s_precision`, `tsymex_rfc0005_s8s_precision_b`,
## `tsymex_rfc0005_s8s_precision_c`, `tsymex_rfc0005_s8s_precision_d`,
## `tsymex_rfc0005_s8s_precision_f`, `tsymex_rfc0005_s8s_precision_g`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 134 s).

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

suite "S8s (4) variant arm field writes and positional tuple writes":
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
