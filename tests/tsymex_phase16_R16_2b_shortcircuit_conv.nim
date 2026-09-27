import std/unittest
import nelli/symex

# Phase 16 R16-2b — short-circuit guard for inline float→int conversions.
#
# R16-2 made float→int raise RangeDefect, but missed the case where the
# conversion is in a SHORT-CIRCUITED operand of `and`/`or`. The D1c fast path
# (rhsPreamble.len == 0) bypassed the guard because float→int is lowered INLINE
# (iekConvFloatToInt in the expr tree), not into the preamble. Fix: detect
# iekConvFloatToInt in rhsIR and force the guarded path even when the preamble
# is empty (R16-2b, walker v23).
#
# RFC-0005 S8g (walker 155): Nim's `int(f)` never raises (it casts, then checks
# the cast value, which is always in range for a full-width target), so these
# SUTs now convert to `Natural`, whose subrange check on the cast value does
# raise (probed: `Natural(-5.0)` raises RangeDefect, `Natural(3.5)` is 3). The
# short-circuit guard is unchanged: the Natural fork is an inline defect fork.

# ---------------------------------------------------------------------------
# Behavior 1: repro — `and` short-circuit with Natural(x) on RHS (primary gate)
# ---------------------------------------------------------------------------

proc r2b_andConv(x: float) =
  ## x ∈ (3,4) is enforced by the LHS guard; Natural(x) == 3 is the RHS.
  ## Natural(x) is only evaluated when x > 3.0 and x < 4.0, so Natural(x) ∈ [3,3],
  ## which is well within int64 range. RangeDefect is unreachable.
  if x > 3.0 and x < 4.0 and Natural(x) == 3: symexTarget("r2bAndConvHit")

suite "symex Phase 16 R16-2b — short-circuit float→int guard (and)":

  test "R16-2b-1a: and-guarded Natural(x) with x∈(3,4) does NOT raise RangeDefect":
    ## FALSE POSITIVE before fix: engine reports sxRaised(RangeDefect) because
    ## the inline iekConvFloatToInt bypasses the D1c guard (fast path).
    ## After fix: the guarded path carries the LHS constraint (x∈(3,4)) into
    ## the drain, making not(domainCond) UNSAT → no raise → sxUnsat.
    let r = symexFind(r2b_andConv, tRaisedExn("RangeDefect"))
    check r.status != sxRaised  ## must not raise RangeDefect

  test "R16-2b-1b: and-guarded Natural(x) target is reachable → sxSat":
    ## x=3.5 satisfies x>3.0 and x<4.0 and Natural(x)==3. Target must be found.
    let r = symexFind(r2b_andConv, tLabel("r2bAndConvHit"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# Behavior 2: or short-circuit with Natural(x) on RHS
# ---------------------------------------------------------------------------

proc r2b_orConv(x: float) =
  ## or-chain: `not (x > 3.0 and x < 4.0)` guards ALL out-of-range floats
  ## INCLUDING NaN (NaN makes both comparisons false → and=false → not=true
  ## → short-circuit). Natural(x)==3 is only evaluated when x∈(3,4).
  if not (x > 3.0 and x < 4.0) or Natural(x) == 3: symexTarget("r2bOrConvHit")

suite "symex Phase 16 R16-2b — short-circuit float→int guard (or)":

  test "R16-2b-2: or-guarded Natural(x) does NOT raise RangeDefect":
    ## Natural(x)==3 is the RHS of the outer `or`. The LHS `not (x>3.0 and x<4.0)`
    ## is true for all x∉(3,4) including NaN (NaN comparisons are all false).
    ## So Natural(x) is only evaluated when x∈(3,4), where it cannot raise.
    let r = symexFind(r2b_orConv, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

# ---------------------------------------------------------------------------
# Behavior 3: LHS conv still raises (no over-guard)
# ---------------------------------------------------------------------------

proc r2b_lhsConv(x: float) =
  ## Natural(x) is on the LHS — evaluated unconditionally. For x <= -1.0 it raises.
  if Natural(x) == 3 and x > 3.0: symexTarget("r2bLhsConvHit")

suite "symex Phase 16 R16-2b — LHS conv unguarded (regression)":

  test "R16-2b-3: LHS Natural(x) still raises RangeDefect (unconditional path)":
    ## The fix must NOT over-guard. LHS conv is always evaluated; for out-of-range
    ## x it genuinely raises. This test fails if the fix incorrectly guards lhsIR.
    let r = symexFind(r2b_lhsConv, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

# ---------------------------------------------------------------------------
# Behavior 4: Unguarded conv still raises (R16-2 intact)
# ---------------------------------------------------------------------------

proc r2b_unguarded(f: float) =
  ## Plain unconstrained Natural(f) — no short-circuit context.
  let i = Natural(f)
  symexTarget("r2bUnguardedHit")
  discard i

proc r2b_intNever(f: float) =
  let i = int(f)
  discard i

suite "symex Phase 16 R16-2b — unguarded float→Natural":

  test "R16-2b-4: unconstrained Natural(f) raises RangeDefect":
    ## The guard only changes a guarded RHS; an unguarded Natural(f) must
    ## continue to fork a RangeDefect raise.
    let r = symexFind(r2b_unguarded, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"

suite "symex Phase 16 R16-2b — int(f) itself never raises (S8g)":

  test "R16-2b-5: unconstrained int(f) has no RangeDefect path":
    let r = symexFind(r2b_intNever, tRaisedExn("RangeDefect"))
    check r.status == sxUnsat
