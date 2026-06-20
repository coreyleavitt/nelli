import std/unittest
import std/math
import std/sequtils
import proptest/symex

# Phase 15 — CR-3, CR-4, CR-6 float soundness fixes.
#
# CR-3 (MEDIUM): float→int out-of-range: no domain guard → silent unsound witness.
#   Fix: add `f ∈ [float(low(T)), float(high(T))]` path constraint + emit
#   feConvDomainExcluded (sevHint) so the result is honest-incomplete, never
#   silently unsound.  RangeDefect modeling remains Phase-16.
#
# CR-4 (MEDIUM): convWidth never read; int32(f) modeled as 64-bit truncation.
#   Fix: use toSbv[...,32] for convWidth==32 + domain-bound to int32 range.
#
# CR-6 (MEDIUM): cmpFloat doAssert a.kind==b.kind crashes for float32 vs float64.
#   Fix: widen float32 to float64 via toFp(rmRNE()) before the comparison (mirrors
#   Nim semantics).
#
# RED phase: these tests FAIL before the fixes.  Each test is annotated with
# WHY it fails (what property is missing pre-fix).

# ---------------------------------------------------------------------------
# CR-3 SUTs
# ---------------------------------------------------------------------------

proc f2i_unbound(x: float) =
  ## Unbounded float-to-int: int(x) == 3.
  ## Before fix: no domain guard → Z3 free to witness NaN/Inf/huge float.
  ## After fix: domain bound [low(int64)..high(int64)] added to pc.
  if int(x) == 3: symexTarget("f2i_unbound")

proc f2i_nan(x: float) =
  ## Only satisfiable if x is NaN.
  ## Before fix: might return sxSat with NaN (bogus witness, int(NaN) ≠ 3 in Nim).
  ## After fix: domain bound excludes NaN → sxUnsat (NaN is not in [lo64, hi64]).
  if isNaN(x) and int(x) == 3: symexTarget("f2i_nan")

proc f2i_inf(x: float) =
  ## Only satisfiable if x is +Inf.
  ## Before fix: might return sxSat with Inf witness (int(Inf) raises RangeDefect).
  ## After fix: domain bound excludes Inf → sxUnsat.
  ## Note: use `x == Inf` since std/math has no `isInf` in Nim 2.2.x.
  if x == Inf and int(x) == 3: symexTarget("f2i_inf")

# ---------------------------------------------------------------------------
# CR-4 SUTs
# ---------------------------------------------------------------------------

proc i32conv(x: float) =
  ## int32(x) == 5: should produce a witness that round-trips through int32().
  ## Before fix: modeled as 64-bit; any float with trunc64==5 is a witness,
  ##   but Z3 will still find x=5.0 — hint check is the clean RED signal.
  ## After fix: modeled as 32-bit + domain-bounded; witness IS in int32 range.
  if int32(x) == 5: symexTarget("i32conv")

# ---------------------------------------------------------------------------
# CR-6 SUTs
# ---------------------------------------------------------------------------

proc mixedCmp(a: float32, b: float64) =
  ## Nim auto-widens a: float32 to float64 for `a == b`, but nnkHiddenStdConv
  ## is stripped by the parser — cmpFloat gets svFloat32 vs svFloat64.
  ## Before fix: doAssert a.kind == b.kind fires → CRASH (AssertionDefect).
  ## After fix: svFloat32 widened to svFloat64 → comparison succeeds.
  if a == b: symexTarget("mixedCmp")

proc mixedCmpOrd(a: float32, b: float64) =
  ## Same but with an ordering comparison (<).
  ## Before fix: same doAssert crash.
  ## After fix: widening + IEEE comparison.
  if a < b: symexTarget("mixedCmpOrd")

# ---------------------------------------------------------------------------
# Suites
# ---------------------------------------------------------------------------

suite "symex Phase 15 — CR-3 float→int domain bounding":

  test "CR-3: unbounded int(x)==3 emits feConvDomainExcluded hint (RED: no hint before fix)":
    ## The key soundness check: the engine MUST emit a hint recording that
    ## the out-of-range domain was excluded.  Before fix: no such hint exists.
    let r = symexFind(f2i_unbound, tLabel("f2i_unbound"))
    check r.status == sxSat
    # Soundness: the hint must be present to signal honest-incompleteness.
    check r.errors.anyIt(it.kind == feConvDomainExcluded and it.severity == sevHint)

  test "CR-3: witness for int(x)==3 round-trips (int(witness)==3 at runtime)":
    ## Secondary property: the witness produced IS in int64 range.
    let r = symexFind(f2i_unbound, tLabel("f2i_unbound"))
    check r.status == sxSat
    let w = r.witness[0]   # the concrete float witness
    check int(w) == 3      # must round-trip through Nim's int()

  test "CR-3: NaN-only predicate excluded → sxUnsat (RED: sxSat+NaN before fix)":
    ## isNaN(x) and int(x)==3 is ONLY satisfiable if x is NaN — but NaN is
    ## outside the domain bound [low(int64)..high(int64)].  After fix: sxUnsat.
    ## Before fix: Z3 could return sxSat with x=NaN (silent unsound witness).
    let r = symexFind(f2i_nan, tLabel("f2i_nan"))
    check r.status == sxUnsat

  test "CR-3: Inf-only predicate excluded → sxUnsat (RED: sxSat+Inf before fix)":
    ## isInf(x) and int(x)==3 is ONLY satisfiable if x is Inf — Inf is
    ## excluded by the finite-float domain bound.  After fix: sxUnsat.
    let r = symexFind(f2i_inf, tLabel("f2i_inf"))
    check r.status == sxUnsat

suite "symex Phase 15 — CR-4 int32(float) 32-bit conversion":

  test "CR-4: int32(x)==5 emits feConvDomainExcluded hint (RED: no hint before fix)":
    ## int32(x) must be modeled as a 32-bit bounded conversion.
    ## Before fix: no domain hint → width and range are both wrong (64-bit).
    let r = symexFind(i32conv, tLabel("i32conv"))
    check r.status == sxSat
    check r.errors.anyIt(it.kind == feConvDomainExcluded and it.severity == sevHint)

  test "CR-4: int32(x)==5 witness round-trips through int32() at runtime":
    ## The witness float must be in int32 range and satisfy int32(witness)==5.
    let r = symexFind(i32conv, tLabel("i32conv"))
    check r.status == sxSat
    let w = r.witness[0]
    check int32(w) == 5

suite "symex Phase 15 — CR-6 float32 vs float64 comparison":

  test "CR-6: float32==float64 comparison does not crash (RED: AssertionDefect before fix)":
    ## Before fix: cmpFloat doAssert fires when a.kind != b.kind.
    ## After fix: float32 widened to float64 → returns correct verdict.
    let r = symexFind(mixedCmp, tLabel("mixedCmp"))
    # Must not crash; result must be sat (there exist equal float32/float64 pairs).
    check r.status == sxSat

  test "CR-6: float32 < float64 ordering comparison does not crash":
    let r = symexFind(mixedCmpOrd, tLabel("mixedCmpOrd"))
    check r.status == sxSat

  test "CR-6: mixed float32==float64 witness round-trips":
    ## The witness (a: float32, b: float64) must actually satisfy a == b at runtime.
    let r = symexFind(mixedCmp, tLabel("mixedCmp"))
    check r.status == sxSat
    let a = r.witness[0]   # float32
    let b = r.witness[1]   # float64
    # At runtime, Nim widens a to float64 for the comparison.
    check float64(a) == b
