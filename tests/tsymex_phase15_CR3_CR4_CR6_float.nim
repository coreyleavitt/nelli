import std/unittest
import std/math
import std/sequtils
import nelli/symex

# Phase 15 — CR-3, CR-4, CR-6 float soundness fixes.
#
# CR-3 (MEDIUM): float→int out-of-range: no domain guard → silent unsound witness.
#   Fix: add `f ∈ [float(low(T)), float(high(T))]` path constraint so the result
#   is honest-incomplete, never silently unsound.
#   RFC-0005 S8g (walker 155): Nim's int(f) never raises (probed: int(1e30),
#   int(NaN), int(Inf) all give low(int); int32(1e30) gives 0), so the R16-2
#   RangeDefect fork is gone. In range the value is exact; out of range it is
#   a fresh value (feConvFloatToIntUndefined) that replay confirms or refutes.
#
# CR-4 (MEDIUM): convWidth never read; int32(f) modeled as 64-bit truncation.
#   Fix: use toSbv[...,32] for convWidth==32 + domain-bound to int32 range.
#   S8g: int32(f) is exact at width 32 in range and never raises.
#
# CR-6 (MEDIUM): cmpFloat doAssert a.kind==b.kind crashes for float32 vs float64.
#   Fix: widen float32 to float64 via toFp(rmRNE()) before the comparison (mirrors
#   Nim semantics).

# ---------------------------------------------------------------------------
# CR-3 SUTs
# ---------------------------------------------------------------------------

proc f2i_unbound(x: float) =
  ## Unbounded float-to-int: int(x) == 3.
  ## Reachable in range (x = 3.0); never raises.
  if int(x) == 3: symexTarget("f2i_unbound")

proc f2i_nan(x: float) =
  ## Unreachable in Nim: int(NaN) == low(int).
  if isNaN(x) and int(x) == 3: symexTarget("f2i_nan")

proc f2i_inf(x: float) =
  ## Unreachable in Nim: int(Inf) == low(int).
  ## Note: use `x == Inf` since std/math has no `isInf` in Nim 2.2.x.
  if x == Inf and int(x) == 3: symexTarget("f2i_inf")

# ---------------------------------------------------------------------------
# CR-4 SUTs
# ---------------------------------------------------------------------------

proc i32conv(x: float) =
  ## int32(x) == 5: should produce a witness that round-trips through int32().
  ## Never raises (S8g).
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

  test "CR-3: unbounded int(x) never raises; int(x)==3 is a clean sxSat (S8g)":
    check symexFind(f2i_unbound, tRaisedExn("RangeDefect")).status == sxUnsat
    let r = symexFind(f2i_unbound, tLabel("f2i_unbound"))
    check r.status == sxSat
    if r.status == sxSat: check int(r.witness[0]) == 3

  test "CR-3: NaN input → never a claim (S8g: fresh value, replay refutes)":
    ## Real Nim: int(NaN) == low(int), so the label is unreachable. The model's
    ## out-of-range value is fresh; its candidate is replayed and refuted.
    check symexFind(f2i_nan, tRaisedExn("RangeDefect")).status == sxUnsat
    let r = symexFind(f2i_nan, tLabel("f2i_nan"))
    check r.status == sxUnknown

  test "CR-3: Inf input → never a claim (S8g: fresh value, replay refutes)":
    check symexFind(f2i_inf, tRaisedExn("RangeDefect")).status == sxUnsat
    let r = symexFind(f2i_inf, tLabel("f2i_inf"))
    check r.status == sxUnknown

suite "symex Phase 15 — CR-4 int32(float) 32-bit conversion":

  test "CR-4: int32(x) never raises; int32(x)==5 is a clean sxSat (S8g)":
    check symexFind(i32conv, tRaisedExn("RangeDefect")).status == sxUnsat
    let r = symexFind(i32conv, tLabel("i32conv"))
    check r.status == sxSat
    if r.status == sxSat: check int32(r.witness[0]) == 5

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
