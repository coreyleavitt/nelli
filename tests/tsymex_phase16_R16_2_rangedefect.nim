import std/unittest
import proptest/symex

# Phase 16 R16-2 — float→int RangeDefect raise fork.
#
# The engine now forks a `RangeDefect` raise-path when `int(f)` / `int32(f)` is
# applied to a float value that may be outside the target integer range (NaN,
# ±Inf, or out-of-range finite). This is the "honest-RAISES" model promised by
# CR-3's "RangeDefect modeling is Phase-16" comment.
#
# Design: a parallel sink `convFloatToIntDomainConds` carries the SAME domainCond
# as `convFloatToIntBoundConds`, but is drained by `drainConvFloatToIntRaises`
# (a fork drain) rather than `drainConvFloatToIntBounds` (a narrowing drain).
# The fork branches off the PRE-narrowing path so the raise constraint
# `not(domainCond)` does not land on an already-narrowed path (which would be
# UNSAT by construction and silently drop the finding).
#
# RED state for each test: before R16-2, tRaisedExn("RangeDefect") yields
# sxUnsat because no raise fork is opened.

# ---------------------------------------------------------------------------
# Behavior 1: Tracer — int(f) with unconstrained f → sxRaised(RangeDefect)
# ---------------------------------------------------------------------------

proc rd_raiseOnly(f: float) =
  ## No explicit unreachable label — we drive via tRaisedExn.
  ## int(f) on an unconstrained f triggers RangeDefect for out-of-range values.
  let i = int(f)
  symexTarget("rdRaiseOnlyHit")
  discard i

suite "symex Phase 16 R16-2 — float→int RangeDefect raise fork":

  test "R16-2-1: unconstrained int(f) → sxRaised(RangeDefect)":
    ## Before R16-2: tRaisedExn("RangeDefect") yields sxUnsat.
    ## After R16-2: the raise fork is opened → sxRaised.
    let r = symexFind(rd_raiseOnly, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

# ---------------------------------------------------------------------------
# Behavior 2: Caught — RangeDefect inside try/except is catchable
# ---------------------------------------------------------------------------

proc rd_caught(f: float) =
  ## int(f) wrapped in try/except RangeDefect: the defect is caught.
  try:
    let i = int(f)
    discard i
  except RangeDefect:
    symexTarget("rdCaughtHit")

suite "symex Phase 16 R16-2 — RangeDefect catchability":

  test "R16-2-2: int(f) in try/except RangeDefect is caught → sxSat":
    ## The raise-fork enters the except handler; handler body reaches the target.
    ## Proves routeRaise correctly threads into the except block.
    let r = symexFind(rd_caught, tLabel("rdCaughtHit"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# Behavior 3: In-range stays clean — no false positive RangeDefect
# ---------------------------------------------------------------------------

proc rd_inRange(f: float) =
  ## f is constrained to [0.0, 10.0) before int(f): no RangeDefect.
  if f >= 0.0 and f < 10.0:
    let i = int(f)
    if i == 5: symexTarget("rdInRangeHit")

suite "symex Phase 16 R16-2 — in-range no false positive":

  test "R16-2-3: in-range constrained int(f) yields sxSat with no spurious RangeDefect":
    ## f ∈ [0,10) is inside int64 range. `not(domainCond)` is UNSAT under the
    ## existing path constraint, so no raise fork surfaces.
    let r = symexFind(rd_inRange, tLabel("rdInRangeHit"))
    check r.status == sxSat

  test "R16-2-3b: in-range constrained → tRaisedExn(RangeDefect) is sxUnsat":
    ## No RangeDefect should be reachable when f is bounded in [0,10).
    let r = symexFind(rd_inRange, tRaisedExn("RangeDefect"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Behavior 4: acRange-off — no RangeDefect when acRange excluded from arithChecks
# ---------------------------------------------------------------------------

proc rd_acRangeOff(f: float) =
  ## Same SUT as rd_raiseOnly, but tested with acRange excluded.
  discard int(f)
  symexTarget("rdAcRangeOffHit")

proc noAcRangeSettings(): SymexSettings =
  ## Settings with acRange excluded from arithChecks — disables RangeDefect forks.
  result = defaultSymexSettings()
  result.arithChecks = {acOverflow, acDivByZero}

suite "symex Phase 16 R16-2 — acRange gate":

  test "R16-2-4: acRange off → no RangeDefect raise (honest-incomplete only)":
    ## When acRange is excluded from arithChecks, the raise fork is suppressed.
    let r = symexFind(rd_acRangeOff, tRaisedExn("RangeDefect"), noAcRangeSettings())
    check r.status == sxUnsat   ## no RangeDefect path raised

# ---------------------------------------------------------------------------
# Behavior 5: int32 width — RangeDefect for int32(f) with out-of-int32 value
# ---------------------------------------------------------------------------

proc rd_int32width(f: float) =
  ## int32(f) on an unconstrained f: the 32-bit domain is narrower than int64.
  ## A value in (2^31, 2^63) is valid int64 range but out-of-range for int32.
  let i = int32(f)
  discard i
  symexTarget("rdInt32Hit")

suite "symex Phase 16 R16-2 — int32(float) RangeDefect":

  test "R16-2-5: int32(f) unconstrained → sxRaised(RangeDefect)":
    ## The 32-bit branch of iekConvFloatToInt must fork a RangeDefect raise.
    let r = symexFind(rd_int32width, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"
