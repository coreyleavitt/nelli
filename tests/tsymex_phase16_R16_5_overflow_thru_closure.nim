## Phase 16 R16-5 — proc-as-value / closure call returns a SOUND witness under
## arithChecks=all-on (ADR-0012 caller-local defect-survivor threading).
##
## REGRESSION GUARD for the C3 unsound-witness bug. Before the fix, a label
## search through a proc-as-value call (`let g = dbl; if g(n) == 10`) returned a
## witness n = 4611686018427387904 (2^62) that does NOT satisfy the gate
## `n*2 == 10`: the closure body's `not overflow` survivor constraint was
## demoted into the closure return-axiom's implication GUARD
## (`implies(not overflow, funcApp == n*2)`), so Z3 discharged the value binding
## by choosing the overflow branch, leaving n free while funcApp == 10.
##
## The fix (defectSurvivorPc split + closure exit-pc channel) threads that
## feasibility constraint onto the CALLER path instead, so the value axiom is
## unconditional and the gate binds: witness n = 5, and 5*2 == 10 holds.
##
## ANTI-MASKING: the same `*` overflow, when the arithmetic is in the SUT body
## directly (not behind a call), still surfaces as sxRaised(OverflowDefect) —
## i.e. moving the survivor negations out of `pc` into `defectSurvivorPc` did NOT
## suppress defect surfacing on the normal path. (trySolve asserts pc ++
## defectSurvivorPc together; the in-body raise path keeps overflow_pred=true in
## its own pc and is never weakened.)
##
## KNOWN PRE-EXISTING LIMITATION (NOT introduced by this slice, reported
## separately): a Defect raised INSIDE a CALLED proc body does not surface
## through the call — `discard dbl(n)` targeted at OverflowDefect is sxUnsat for
## BOTH a named call and a proc-as-value call (verified empirically). That gap is
## orthogonal to the caller-local-threading fix and to closures specifically.

import std/unittest
import nelli/symex

proc dbl(x: int): int = x * 2
proc applyOnce(f: proc(x: int): int, v: int): int = f(v)

# Proc-as-value: `dbl` stored in a value and called. The gate `g(n) == 10`
# forces n*2 == 10; the only sound BV64 witness in range is n == 5.
proc soundLabelValue(n: int) =
  let g = dbl
  if g(n) == 10:
    symexTarget("hit")

# Proc-as-arg: `dbl` passed as a proc-valued argument and applied.
proc soundLabelArg(n: int) =
  if applyOnce(dbl, n) == 10:
    symexTarget("hit")

# Anti-masking control: the SAME multiply, but in the SUT body directly, so the
# OverflowDefect surfaces without going through a call boundary.
proc directOverflow(a, b: int) =
  let c = a * b
  symexTarget("t")
  discard c

suite "symex Phase 16 R16-5 — sound witness through proc-as-value (ADR-0012)":

  test "R16-5-1: proc-as-value label search → SOUND witness (n=5, 5*2==10)":
    let r = symexFind(soundLabelValue, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 5
    check r.witness[0] * 2 == 10     ## the witness ACTUALLY satisfies the gate

  test "R16-5-2: proc-as-arg label search → SOUND witness (n=5, 5*2==10)":
    let r = symexFind(soundLabelArg, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 5
    check r.witness[0] * 2 == 10

  test "R16-5-3: anti-masking — direct SUT-body overflow still sxRaised":
    let r = symexFind(directOverflow, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"
