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
# R16-2 UPDATE: `drainConvFloatToIntRaises` now fires at each isIf site for
# unconstrained int(f) conditions. The raise fork (RangeDefect for out-of-range
# values) is discovered BEFORE the in-range sat path for unconstrained f.
# Primary finding is sxRaised (not sxSat) for all unconstrained-f SUTs.
# The probeProto fix is still verified: a prompt sxRaised (not exit 137/crash)
# proves the BV encoding is correct (no bv2int-over-FP, no doAssert crash).
# Witness round-trips use pre-constrained SUTs where the raise is UNSAT.
#
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
# R16-2: outer if pre-constrains f to int64 range → inner int(f) raise is UNSAT
# → sxSat is primary finding → witness round-trip is valid.
proc f64GtLitConstr(f: float) =
  ## f pre-constrained to (5.0, 1e15): inner int(f) > 5 raise UNSAT under bound.
  if f > 5.0 and f < 1.0e15:
    if int(f) > 5:
      symexTarget("f64GtLitConstr")

proc f64ArithLitConstr(f: float, k: int) =
  ## f pre-constrained to reasonable int64 range: BV arithmetic witness valid.
  if f >= 0.0 and f < 1.0e15:
    if int(f) + 5 == k:
      symexTarget("f64ArithLitConstr")

suite "symex Phase 15 — F5-probeproto regression: int(f) vs literal":

  test "F5-pp-1: int(f) > 5 ordering vs literal — no hang (R16-2: sxRaised promptly)":
    ## Before probeProto fix: hangs (bv2int-over-FP pathology) or crashes.
    ## After fix + R16-2: sxRaised returned PROMPTLY (defect for unconstrained f).
    ## Prompt sxRaised proves: (a) no bv2int hang, (b) no doAssert crash.
    let r = symexFind(f64GtLit, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "F5-pp-2: int(f) == 42 equality vs literal — no hang (R16-2: sxRaised promptly)":
    let r = symexFind(f64EqLit, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "F5-pp-3: int(f) + 5 == k arithmetic vs literal — no crash (R16-2: sxRaised promptly)":
    ## Before fix: `binBV` doAssert fires (svBV64 vs svInt → crash).
    ## After fix + R16-2: sxRaised promptly (no crash, no bv2int).
    let r = symexFind(f64ArithLit, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "F5-pp-4: int32(f) + 5 == k arithmetic vs literal — no crash (R16-2: sxRaised promptly)":
    ## Same but svBV32 branch. Prompt sxRaised proves no doAssert on BV32.
    let r = symexFind(f32ArithLit, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "F5-pp-5: int32(f) == 10 equality vs literal (svBV32 branch) — no hang (R16-2: sxRaised)":
    let r = symexFind(f32EqLit, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "F5-pp-6: constrained int(f) > 5 witness round-trip (R16-2: pre-bound → sxSat)":
    ## With f pre-constrained to (5.0, 1e15), the raise path is UNSAT → sxSat.
    ## Verifies the in-range sat path AND the witness validity.
    let r = symexFind(f64GtLitConstr, tLabel("f64GtLitConstr"))
    check r.status == sxSat
    let f = r.witness[0]
    check int(f) > 5

  test "F5-pp-7: constrained int(f) + 5 == k arithmetic witness round-trip":
    ## With f pre-constrained to [0, 1e15), the raise path is UNSAT → sxSat.
    let r = symexFind(f64ArithLitConstr, tLabel("f64ArithLitConstr"))
    check r.status == sxSat
    let f = r.witness[0]
    let k = r.witness[1]
    check int(f) + 5 == k
