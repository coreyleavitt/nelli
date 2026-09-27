import std/unittest
import nelli/symex

# Phase 16 R16-2 — float→int RangeDefect.
#
# R16-2 forked a `RangeDefect` raise-path whenever `int(f)` / `int32(f)` could
# see a float outside the target range. RFC-0005 S8g (walker 155) reversed it
# (ADR-0011, "Reversed (RFC-0005 S8g)"): Nim 2.2.10 casts first and checks the
# CAST value, so an int-family target never raises. Probed, c and cpp:
#   int(1e30) = int(NaN) = int(Inf) = low(int); int32(1e30) = 0;
#   int8(300.0) = 44; none raise RangeDefect.
# Only a `range` target checks the cast value against its subrange:
#   Natural(-5.0) raises RangeDefect.
# These pins keep R16-2's shapes and assert the Nim behaviour: `int(f)` has
# no RangeDefect path, `Natural(f)` does, and `acRange` gates the latter.

# ---------------------------------------------------------------------------
# Behavior 1: unconstrained int(f) never raises; Natural(f) does
# ---------------------------------------------------------------------------

proc rd_raiseOnly(f: float) =
  let i = int(f)
  symexTarget("rdRaiseOnlyHit")
  discard i

proc rd_natural(f: float) =
  let i = Natural(f)
  symexTarget("rdNaturalHit")
  discard i

suite "symex Phase 16 R16-2 — float→int RangeDefect (S8g: range targets only)":

  test "R16-2-1: unconstrained int(f) → no RangeDefect (sxUnsat)":
    let r = symexFind(rd_raiseOnly, tRaisedExn("RangeDefect"))
    check r.status == sxUnsat

  test "R16-2-1b: unconstrained Natural(f) → sxRaised(RangeDefect)":
    let r = symexFind(rd_natural, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

# ---------------------------------------------------------------------------
# Behavior 2: catchability — the handler around int(f) is dead; around
# Natural(f) it is live
# ---------------------------------------------------------------------------

proc rd_caught(f: float) =
  try:
    let i = int(f)
    discard i
  except RangeDefect:
    symexTarget("rdCaughtHit")

proc rd_caughtNatural(f: float) =
  try:
    let i = Natural(f)
    discard i
  except RangeDefect:
    symexTarget("rdCaughtNaturalHit")

suite "symex Phase 16 R16-2 — RangeDefect catchability":

  test "R16-2-2: int(f) in try/except RangeDefect: the handler is dead → sxUnsat":
    let r = symexFind(rd_caught, tLabel("rdCaughtHit"))
    check r.status == sxUnsat

  test "R16-2-2b: Natural(f) in try/except RangeDefect is caught → sxSat":
    let r = symexFind(rd_caughtNatural, tLabel("rdCaughtNaturalHit"))
    check r.status == sxSat
    if r.status == sxSat:
      var caught = false
      try:
        discard Natural(r.witness[0])
      except RangeDefect:
        caught = true
      check caught

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
    let r = symexFind(rd_inRange, tLabel("rdInRangeHit"))
    check r.status == sxSat

  test "R16-2-3b: in-range constrained → tRaisedExn(RangeDefect) is sxUnsat":
    let r = symexFind(rd_inRange, tRaisedExn("RangeDefect"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# Behavior 4: acRange-off — no RangeDefect when acRange excluded from arithChecks
# ---------------------------------------------------------------------------

proc rd_acRangeOff(f: float) =
  discard Natural(f)
  symexTarget("rdAcRangeOffHit")

proc noAcRangeSettings(): SymexSettings =
  ## Settings with acRange excluded from arithChecks — disables RangeDefect forks.
  result = defaultSymexSettings()
  result.arithChecks = {acOverflow, acDivByZero}

suite "symex Phase 16 R16-2 — acRange gate":

  test "R16-2-4: acRange on → Natural(f) raises RangeDefect":
    let r = symexFind(rd_acRangeOff, tRaisedExn("RangeDefect"))
    check r.status == sxRaised

  test "R16-2-4b: acRange off → no RangeDefect raise":
    let r = symexFind(rd_acRangeOff, tRaisedExn("RangeDefect"), noAcRangeSettings())
    check r.status == sxUnsat   ## no RangeDefect path raised

# ---------------------------------------------------------------------------
# Behavior 5: int32 width — never raises; exact at width 32 in range
# ---------------------------------------------------------------------------

proc rd_int32width(f: float) =
  let i = int32(f)
  discard i
  symexTarget("rdInt32Hit")

proc rd_int32exact(f: float) =
  if f > 7.0 and f < 8.0:
    if int32(f) == 7: symexTarget("rdInt32Exact")

suite "symex Phase 16 R16-2 — int32(float)":

  test "R16-2-5: int32(f) unconstrained → no RangeDefect (sxUnsat)":
    let r = symexFind(rd_int32width, tRaisedExn("RangeDefect"))
    check r.status == sxUnsat

  test "R16-2-5b: int32(f) in range is exact":
    let r = symexFind(rd_int32exact, tLabel("rdInt32Exact"))
    check r.status == sxSat
    if r.status == sxSat: check int32(r.witness[0]) == 7
