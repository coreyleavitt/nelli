import std/unittest
import std/math
import std/sequtils
import proptest/symex

# Phase 15 — CR-3, CR-4, CR-6 float soundness fixes.
#
# CR-3 (MEDIUM): float→int out-of-range: no domain guard → silent unsound witness.
#   Fix: add `f ∈ [float(low(T)), float(high(T))]` path constraint so the result
#   is honest-incomplete, never silently unsound.
#   R16-2 follow-up: additionally forks a RangeDefect raise for the out-of-range
#   path. For unconstrained SUTs the raise is the PRIMARY finding.
#
# CR-4 (MEDIUM): convWidth never read; int32(f) modeled as 64-bit truncation.
#   Fix: use toSbv[...,32] for convWidth==32 + domain-bound to int32 range.
#   R16-2: raise fork fires for int32(f) too.
#
# CR-6 (MEDIUM): cmpFloat doAssert a.kind==b.kind crashes for float32 vs float64.
#   Fix: widen float32 to float64 via toFp(rmRNE()) before the comparison (mirrors
#   Nim semantics).

# ---------------------------------------------------------------------------
# CR-3 SUTs
# ---------------------------------------------------------------------------

proc f2i_unbound(x: float) =
  ## Unbounded float-to-int: int(x) == 3.
  ## After CR-3 fix: domain bound [low(int64)..high(int64)] added to pc.
  ## After R16-2: unconstrained int(x) also forks a RangeDefect raise.
  if int(x) == 3: symexTarget("f2i_unbound")

proc f2i_nan(x: float) =
  ## Only satisfiable if x is NaN.
  ## After CR-3 fix: domain bound excludes NaN.
  ## After R16-2: the raise path (not(domainCond)) captures NaN → sxRaised.
  if isNaN(x) and int(x) == 3: symexTarget("f2i_nan")

proc f2i_inf(x: float) =
  ## Only satisfiable if x is +Inf.
  ## After CR-3 fix: domain bound excludes Inf.
  ## After R16-2: the raise path (not(domainCond)) captures Inf → sxRaised.
  ## Note: use `x == Inf` since std/math has no `isInf` in Nim 2.2.x.
  if x == Inf and int(x) == 3: symexTarget("f2i_inf")

# ---------------------------------------------------------------------------
# CR-4 SUTs
# ---------------------------------------------------------------------------

proc i32conv(x: float) =
  ## int32(x) == 5: should produce a witness that round-trips through int32().
  ## After R16-2: unconstrained int32(x) forks a RangeDefect raise (primary).
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

  test "CR-3: unbounded int(x)==3 → sxRaised (R16-2: out-of-range raise is primary finding)":
    ## R16-2: an unconstrained int(x) forks a RangeDefect raise-path that is
    ## discovered before the sat path (defect surfacing). The raise is the primary
    ## w.found[0] entry even for tLabel searches.
    ## In-range sat reachability is verified by R16-2-3 (rd_inRange test).
    let r = symexFind(f2i_unbound, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "CR-3: NaN input → sxRaised (R16-2: NaN satisfies not(domainCond))":
    ## Before R16-2: isNaN(x) and int(x)==3 was sxUnsat (NaN excluded by domain bound).
    ## After R16-2: the raise path `not(domainCond)` captures NaN → sxRaised.
    ## The raise path `not(x ∈ int64 range)` is satisfiable for NaN → defect found.
    let r = symexFind(f2i_nan, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "CR-3: Inf input → sxRaised (R16-2: Inf satisfies not(domainCond))":
    ## Before R16-2: x==Inf and int(x)==3 was sxUnsat (Inf excluded by domain bound).
    ## After R16-2: the raise path `not(domainCond)` captures Inf → sxRaised.
    let r = symexFind(f2i_inf, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

suite "symex Phase 15 — CR-4 int32(float) 32-bit conversion":

  test "CR-4: int32(x)==5 → sxRaised (R16-2: out-of-range raise is primary finding)":
    ## R16-2: unconstrained int32(x) forks a RangeDefect raise (primary finding).
    ## The in-range sat path (x=5.0) is also reachable but discovered second.
    let r = symexFind(i32conv, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

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
