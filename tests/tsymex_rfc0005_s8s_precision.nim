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
## RFC-0005 S8cm: part 1 of 8 of this suite, with
## `tsymex_rfc0005_s8s_precision_b`, `tsymex_rfc0005_s8s_precision_h`,
## `tsymex_rfc0005_s8s_precision_c`, `tsymex_rfc0005_s8s_precision_d`,
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
