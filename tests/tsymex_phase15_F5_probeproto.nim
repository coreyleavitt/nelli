import std/unittest
import nelli/symex

# Phase 15 — F5-probeproto regression: `probeProto` stale svInt proto for
# `iekConvFloatToInt` reopens the F5 hang and causes a doAssert crash.
#
# ROOT CAUSE (commit 6c983e4 vs probeProto staleness):
#   `lower()` was updated so that `iekConvFloatToInt` returns `svBV64` for
#   int64 and `svBV32` for int32. But `probeProto`'s `iekConvFloatToInt` arm
#   was NOT updated — it still returned `some(SymVal(kind: svInt, zi: mkInt(0)))`.
#
#   When `int(f)` appears in a comparison/arithmetic with an INTEGER LITERAL:
#   - The reconciliation code calls `probeProto(env, lhs)` on the `int(f)` node
#     to determine how to lower the literal operand.
#   - `probeProto` returned `svInt` → literal lowered as `svInt`.
#   - `lower()` of `int(f)` returns `svBV64`.
#   - Mixed svBV64 vs svInt: the reconciliation promotes BOTH to svInt via
#     `bv2int`, producing `cmpInt(bv2int(fp.to.sbv 64 RTZ f), 5)`.
#     This reintroduces the F5 bv2int-over-FP pathology (hang) on ordering goals.
#   - For arithmetic (`int(f) + 5`): `binBV`'s `doAssert a.kind == b.kind` fires
#     → CRASH (one side svBV64, other svInt).
#
# VARIABLE operand case (e.g. `int(f) > n` with n:int) was already fine because
# both sides are lowered as svBV64 (no literal proto involved).
#
# RFC-0005 S8g (walker 155): `int(f)` never raises in Nim (probed: `int(1e30)`,
# `int(NaN)` give `low(int)`; `int32(1e30)` gives 0), so the R16-2 RangeDefect
# fork these tests used to pin is gone. Each unconstrained SUT now reaches its
# label as a clean `sxSat` whose witness reproduces on the real SUT; a prompt
# verdict (not exit 137, not a crash) still proves the BV encoding (no
# bv2int-over-FP, no doAssert crash).
# RED STATE (before probeProto fix):
#   - `int(f) > 5` ordering vs literal: hangs (exit 137) or produces bv2int wrap
#   - `int(f) + 5 == K` arithmetic vs literal: CRASH (doAssert a.kind==b.kind)
#   - `int32(f) + 5 == K` arithmetic vs literal: CRASH (same, svBV32 vs svInt)
# GREEN STATE (after fix):
#   probeProto returns svBV64/svBV32 proto for iekConvFloatToInt, matching lower().

# --- Test shape 1: int(f) > 5 — ordering vs literal --------------------------
proc f64GtLit(f: float) =
  if int(f) > 5:
    symexTarget("f64GtLit")

# --- Test shape 2: int(f) == 42 — equality vs literal ------------------------
proc f64EqLit(f: float) =
  if int(f) == 42:
    symexTarget("f64EqLit")

# --- Test shape 3: int(f) + 5 == K — arithmetic vs literal → doAssert crash --
proc f64ArithLit(f: float, k: int) =
  if int(f) + 5 == k:
    symexTarget("f64ArithLit")

# --- Test shape 4: int32(f) + 5 == K — same crash for svBV32 branch ----------
proc f32ArithLit(f: float32, k: int) =
  if int32(f) + 5 == k:
    symexTarget("f32ArithLit")

# --- Test shape 5: int32(f) == 10 — equality vs literal (svBV32 branch) ------
proc f32EqLit(f: float32) =
  if int32(f) == 10:
    symexTarget("f32EqLit")

# --- Constrained-path SUTs for witness round-trips ---------------------------
# The outer if pre-constrains f to the int64 range, so the conversion is exact
# on every path and the witness round-trips.
proc f64GtLitConstr(f: float) =
  ## f pre-constrained to (5.0, 1e15): the conversion is exact.
  if f > 5.0 and f < 1.0e15:
    if int(f) > 5:
      symexTarget("f64GtLitConstr")

proc f64ArithLitConstr(f: float, k: int) =
  ## f pre-constrained to reasonable int64 range: BV arithmetic witness valid.
  if f >= 0.0 and f < 1.0e15:
    if int(f) + 5 == k:
      symexTarget("f64ArithLitConstr")

suite "symex Phase 15 — F5-probeproto regression: int(f) vs literal":

  test "F5-pp-1: int(f) > 5 ordering vs literal — no hang (S8g: clean sxSat)":
    let r = symexFind(f64GtLit, tLabel("f64GtLit"))
    checkpoint($r.status)
    check r.status == sxSat
    if r.status == sxSat:
      symexCaptureBegin()
      f64GtLit(r.witness[0])
      check "f64GtLit" in symexCaptureEnd()

  test "F5-pp-2: int(f) == 42 equality vs literal — no hang (S8g: clean sxSat)":
    let r = symexFind(f64EqLit, tLabel("f64EqLit"))
    checkpoint($r.status)
    check r.status == sxSat
    if r.status == sxSat:
      symexCaptureBegin()
      f64EqLit(r.witness[0])
      check "f64EqLit" in symexCaptureEnd()

  test "F5-pp-3: int(f) + 5 == k arithmetic vs literal — no crash (S8g: clean sxSat)":
    let r = symexFind(f64ArithLit, tLabel("f64ArithLit"))
    checkpoint($r.status)
    check r.status == sxSat
    if r.status == sxSat:
      symexCaptureBegin()
      f64ArithLit(r.witness[0], r.witness[1])
      check "f64ArithLit" in symexCaptureEnd()

  test "F5-pp-4: int32(f) + 5 == k arithmetic vs literal — no crash (S8g: clean sxSat)":
    let r = symexFind(f32ArithLit, tLabel("f32ArithLit"))
    checkpoint($r.status)
    check r.status == sxSat
    if r.status == sxSat:
      symexCaptureBegin()
      f32ArithLit(r.witness[0], r.witness[1])
      check "f32ArithLit" in symexCaptureEnd()

  test "F5-pp-5: int32(f) == 10 equality vs literal (svBV32 branch) — no hang (S8g: clean sxSat)":
    let r = symexFind(f32EqLit, tLabel("f32EqLit"))
    checkpoint($r.status)
    check r.status == sxSat
    if r.status == sxSat:
      symexCaptureBegin()
      f32EqLit(r.witness[0])
      check "f32EqLit" in symexCaptureEnd()

  test "F5-pp-6: constrained int(f) > 5 witness round-trip (pre-bound → sxSat)":
    ## With f pre-constrained to (5.0, 1e15), the conversion is exact → sxSat.
    ## Verifies the in-range sat path AND the witness validity.
    let r = symexFind(f64GtLitConstr, tLabel("f64GtLitConstr"))
    check r.status == sxSat
    let f = r.witness[0]
    check int(f) > 5

  test "F5-pp-7: constrained int(f) + 5 == k arithmetic witness round-trip":
    ## With f pre-constrained to [0, 1e15), the conversion is exact → sxSat.
    let r = symexFind(f64ArithLitConstr, tLabel("f64ArithLitConstr"))
    check r.status == sxSat
    let f = r.witness[0]
    let k = r.witness[1]
    check int(f) + 5 == k
