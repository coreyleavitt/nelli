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

# ---------------------------------------------------------------------------
# Behavior 1: repro — `and` short-circuit with int(x) on RHS (primary gate)
# ---------------------------------------------------------------------------

proc r2b_andConv(x: float) =
  ## x ∈ (3,4) is enforced by the LHS guard; int(x) == 3 is the RHS.
  ## int(x) is only evaluated when x > 3.0 and x < 4.0, so int(x) ∈ [3,3],
  ## which is well within int64 range. RangeDefect is unreachable.
  if x > 3.0 and x < 4.0 and int(x) == 3: symexTarget("r2bAndConvHit")

suite "symex Phase 16 R16-2b — short-circuit float→int guard (and)":

  test "R16-2b-1a: and-guarded int(x) with x∈(3,4) does NOT raise RangeDefect":
    ## FALSE POSITIVE before fix: engine reports sxRaised(RangeDefect) because
    ## the inline iekConvFloatToInt bypasses the D1c guard (fast path).
    ## After fix: the guarded path carries the LHS constraint (x∈(3,4)) into
    ## the drain, making not(domainCond) UNSAT → no raise → sxUnsat.
    let r = symexFind(r2b_andConv, tRaisedExn("RangeDefect"))
    check r.status != sxRaised  ## must not raise RangeDefect

  test "R16-2b-1b: and-guarded int(x) target is reachable → sxSat":
    ## x=3.5 satisfies x>3.0 and x<4.0 and int(x)==3. Target must be found.
    let r = symexFind(r2b_andConv, tLabel("r2bAndConvHit"))
    check r.status == sxSat

# ---------------------------------------------------------------------------
# Behavior 2: or short-circuit with int(x) on RHS
# ---------------------------------------------------------------------------

proc r2b_orConv(x: float) =
  ## or-chain: `not (x > 3.0 and x < 4.0)` guards ALL out-of-range floats
  ## INCLUDING NaN (NaN makes both comparisons false → and=false → not=true
  ## → short-circuit). int(x)==3 is only evaluated when x∈(3,4).
  if not (x > 3.0 and x < 4.0) or int(x) == 3: symexTarget("r2bOrConvHit")

suite "symex Phase 16 R16-2b — short-circuit float→int guard (or)":

  test "R16-2b-2: or-guarded int(x) does NOT raise RangeDefect":
    ## int(x)==3 is the RHS of the outer `or`. The LHS `not (x>3.0 and x<4.0)`
    ## is true for all x∉(3,4) including NaN (NaN comparisons are all false).
    ## So int(x) is only evaluated when x∈(3,4), where it cannot raise.
    let r = symexFind(r2b_orConv, tRaisedExn("RangeDefect"))
    check r.status != sxRaised

# ---------------------------------------------------------------------------
# Behavior 3: LHS conv still raises (no over-guard)
# ---------------------------------------------------------------------------

proc r2b_lhsConv(x: float) =
  ## int(x) is on the LHS — evaluated unconditionally. For huge x it raises.
  if int(x) == 3 and x > 3.0: symexTarget("r2bLhsConvHit")

suite "symex Phase 16 R16-2b — LHS conv unguarded (regression)":

  test "R16-2b-3: LHS int(x) still raises RangeDefect (unconditional path)":
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
  ## Plain unconstrained int(f) — no short-circuit context. R16-2 core finding.
  let i = int(f)
  symexTarget("r2bUnguardedHit")
  discard i

suite "symex Phase 16 R16-2b — unguarded float→int (R16-2 intact)":

  test "R16-2b-4: unconstrained int(f) still raises RangeDefect (R16-2 intact)":
    ## Confirms R16-2's core finding is preserved. The fix only changes guarded RHS;
    ## unguarded int(f) must continue to fork a RangeDefect raise.
    let r = symexFind(r2b_unguarded, tRaisedExn("RangeDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "RangeDefect"
