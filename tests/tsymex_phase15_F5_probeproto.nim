import std/unittest
import proptest/symex

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
# RED STATE (before fix):
#   - `int(f) > 5` ordering vs literal: hangs (exit 137) or produces bv2int wrap
#   - `int(f) + 5 == K` arithmetic vs literal: CRASH (doAssert a.kind==b.kind)
#   - `int32(f) + 5 == K` arithmetic vs literal: CRASH (same, svBV32 vs svInt)
# GREEN STATE (after fix):
#   probeProto returns svBV64/svBV32 proto for iekConvFloatToInt, matching lower().

# --- Test shape 1: int(f) > 5 — ordering vs literal --------------------------
# Before fix: hangs (bv2int-over-FP pathology) or gives wrong encoding.
# After fix: sxSat, promptly, with a valid witness (int(f) > 5 i.e. f >= 6.0).
proc f64GtLit(f: float) =
  if int(f) > 5:
    symexTarget("f64GtLit")     # satisfiable: e.g. f=6.0 → int(6.0)=6 > 5

# --- Test shape 2: int(f) == 42 — equality vs literal ------------------------
# Before fix: also routes through bv2int wrap (hang-prone), or wrong encoding.
# After fix: sxSat promptly, witness must have int(f)==42.
proc f64EqLit(f: float) =
  if int(f) == 42:
    symexTarget("f64EqLit")     # satisfiable: e.g. f=42.0 → int(42.0)=42

# --- Test shape 3: int(f) + 5 == K — arithmetic vs literal → doAssert crash --
# Before fix: `binBV` doAssert fires (svBV64 vs svInt → crash).
# After fix: sxSat, witness has int(f) + 5 == k.
proc f64ArithLit(f: float, k: int) =
  if int(f) + 5 == k:
    symexTarget("f64ArithLit")  # satisfiable: e.g. f=2.0, k=7

# --- Test shape 4: int32(f) + 5 == K — same crash for svBV32 branch ----------
# Before fix: `binBV` doAssert fires (svBV32 vs svInt → crash).
# After fix: sxSat, witness has int32(f) + 5 == k (int32 arithmetic).
proc f32ArithLit(f: float32, k: int) =
  if int32(f) + 5 == k:
    symexTarget("f32ArithLit")  # satisfiable: e.g. f=2.0, k=7

# --- Test shape 5: int32(f) == 10 — equality vs literal (svBV32 branch) ------
proc f32EqLit(f: float32) =
  if int32(f) == 10:
    symexTarget("f32EqLit")     # satisfiable: e.g. f=10.0'f32 → int32=10

suite "symex Phase 15 — F5-probeproto regression: int(f) vs literal":

  test "F5-pp-1: int(f) > 5 ordering vs literal — sxSat promptly (RED: hang/bv2int before fix)":
    ## Before fix: probeProto returns svInt proto → literal lowered as svInt →
    ## reconciliation does bv2int(fp.to.sbv 64 RTZ f) → Z3 ordering goal over
    ## FP+BV+Int round-trip → potential hang. After fix: both sides svBV64,
    ## pure QF_BVFP ordering goal, terminates fast.
    let r = symexFind(f64GtLit, tLabel("f64GtLit"))
    check r.status == sxSat
    let f = r.witness[0]
    check int(f) > 5

  test "F5-pp-2: int(f) == 42 equality vs literal — sxSat with correct witness":
    let r = symexFind(f64EqLit, tLabel("f64EqLit"))
    check r.status == sxSat
    let f = r.witness[0]
    check int(f) == 42

  test "F5-pp-3: int(f) + 5 == k arithmetic vs literal — sxSat (RED: doAssert crash before fix)":
    ## Before fix: binBV's `doAssert a.kind == b.kind` fires because `int(f)`
    ## lowers to svBV64 but the literal `5` was lowered as svInt (stale proto).
    ## After fix: both svBV64; BV addition; terminates with witness.
    let r = symexFind(f64ArithLit, tLabel("f64ArithLit"))
    check r.status == sxSat
    let f = r.witness[0]
    let k = r.witness[1]
    check int(f) + 5 == k

  test "F5-pp-4: int32(f) + 5 == k arithmetic vs literal — sxSat (RED: doAssert crash before fix)":
    ## Same but svBV32 branch: int32(f) lowers to svBV32, literal `5` was
    ## lowered as svInt → binBV doAssert fires. After fix: both svBV32.
    let r = symexFind(f32ArithLit, tLabel("f32ArithLit"))
    check r.status == sxSat
    let f = r.witness[0]
    let k = r.witness[1]
    check int32(f) + 5 == k

  test "F5-pp-5: int32(f) == 10 equality vs literal (svBV32 branch) — sxSat":
    let r = symexFind(f32EqLit, tLabel("f32EqLit"))
    check r.status == sxSat
    let f = r.witness[0]
    check int32(f) == 10
