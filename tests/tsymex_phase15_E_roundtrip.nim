## Phase 15 — Cluster E: exception-witness runtime replay (CR-8 Part B).
##
## The E-cluster tests (E1–E7) verify that `raisedWitness[i]` satisfies a
## NUMERIC constraint (e.g. `r.raisedWitness[0] > 0`), but never execute the
## actual SUT at runtime with the produced witness to confirm it REALLY raises
## the expected exception. This file closes that gap: the same round-trip
## discipline that F8/S7b use for the sat path (`symexFind` → plug witness back
## into the runtime predicate → assert it triggers the same behavior) is now
## applied to the RAISED path:
##
##   1. Run `symexFind` with a `tRaisedExn` target → assert `sxRaised`.
##   2. Call the actual Nim proc at runtime with `r.raisedWitness[...]` inside
##      a `try/except` and assert the expected exception IS raised.
##   3. Assert that a contrasting (non-witness) input does NOT raise the same
##      exception.
##
## SUTs are drawn from existing E-cluster shapes (E2b condRaise, E5
## finallyReplaces, E6 assertDefect) so the replay is a faithful round-trip of
## the engine's output — if the witness DOESN'T reproduce, that is a real
## engine bug, not a test weakness.
##
## This file is also the canonical target for the Part-A parity-check.sh gate
## (CR-8), which runs it under BOTH `c` and `cpp` backends via dt-bounded.sh.
import std/unittest
import nelli/symex

# =============================================================================
# SUT definitions — textually identical to the original E-cluster SUTs so the
# replay is a faithful round-trip of the SUT body, not a distinct predicate.
# =============================================================================

# --- E2b shape: conditional raise on x > 0 -----------------------------------
proc condRaise(x: int) =
  if x > 0:
    raise newException(ValueError, "pos")

# --- E5 shape: finallyReplaces — finally raises IOError when x > 100 ---------
proc finallyReplaces(x: int): int =
  try:
    raise newException(ValueError, "original")
  finally:
    if x > 100: raise newException(IOError, "overrides")

# --- E6 shape: assert-false lowers to AssertionDefect (x <= 0 → assert fails)
proc assertDefect(x: int) =
  assert x > 0, "must be positive"

# =============================================================================
# Runtime replay helpers.
# Convention (mirrors F8/S7b): `raisesSUT_<Exn>(...)` calls the actual proc and
# returns true iff the expected exception is raised; false otherwise.
# =============================================================================

proc raisesValueError_condRaise(x: int): bool =
  try:
    condRaise(x)
    false
  except ValueError:
    true

proc raisesIOError_finallyReplaces(x: int): bool =
  # finallyReplaces ALWAYS raises (either IOError or ValueError — it never
  # returns normally). Catch both so neither leaks as an unhandled exception.
  try:
    discard finallyReplaces(x)
    false
  except IOError:
    true
  except ValueError:
    false

proc raisesValueError_finallyReplaces(x: int): bool =
  # Same reasoning: catch both, return true only for ValueError.
  try:
    discard finallyReplaces(x)
    false
  except ValueError:
    true
  except IOError:
    false

proc raisesAssertionDefect_assertDefect(x: int): bool =
  try:
    assertDefect(x)
    false
  except AssertionDefect:
    true

# =============================================================================
# Suite
# =============================================================================
suite "symex Phase 15 E-cluster — exception-witness runtime replay (CR-8 Part B)":

  # ---------------------------------------------------------------------------
  # E2b shape: condRaise — ValueError witness replay
  # The engine reports sxRaised{ValueError} with raisedWitness[0] > 0.
  # REPLAY: call condRaise(raisedWitness[0]) at runtime; it MUST raise ValueError.
  # CONTRAST: condRaise(0) must NOT raise (x==0 does not trigger the condition).
  # ---------------------------------------------------------------------------
  test "E-roundtrip: condRaise ValueError witness reproduces raise at runtime":
    let r = symexFind(condRaise, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    # Numeric constraint established by E2b — witness must be on the raise path.
    check r.raisedWitness[0] > 0
    # === RUNTIME REPLAY ===
    check raisesValueError_condRaise(r.raisedWitness[0])

  test "E-roundtrip: condRaise contrast input (x=0) does NOT raise ValueError":
    # Non-witness: x == 0 does not trigger `if x > 0:`, so no raise.
    check not raisesValueError_condRaise(0)

  # ---------------------------------------------------------------------------
  # E5 shape: finallyReplaces — IOError witness replay (x > 100 path)
  # The engine reports sxRaised{IOError} with raisedWitness[0] > 100.
  # REPLAY: call finallyReplaces(raisedWitness[0]) at runtime; it MUST raise IOError.
  # CONTRAST: finallyReplaces(0) raises ValueError (not IOError).
  # ---------------------------------------------------------------------------
  test "E-roundtrip: finallyReplaces IOError witness reproduces raise at runtime":
    let r = symexFind(finallyReplaces, tRaisedExn("IOError"))
    check r.status == sxRaised
    check r.raisedTypeId == "IOError"
    check r.raisedWitness[0] > 100
    # === RUNTIME REPLAY ===
    check raisesIOError_finallyReplaces(r.raisedWitness[0])

  test "E-roundtrip: finallyReplaces contrast input (x=0) raises ValueError not IOError":
    # x == 0 → finally falls through → original ValueError propagates.
    check not raisesIOError_finallyReplaces(0)
    check raisesValueError_finallyReplaces(0)

  # ---------------------------------------------------------------------------
  # E5 shape: finallyReplaces — ValueError witness replay (x <= 100 path)
  # The engine reports sxRaised{ValueError} with raisedWitness[0] <= 100.
  # REPLAY: call finallyReplaces(raisedWitness[0]); it MUST raise ValueError.
  # ---------------------------------------------------------------------------
  test "E-roundtrip: finallyReplaces ValueError witness reproduces raise at runtime":
    let r = symexFind(finallyReplaces, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] <= 100
    # === RUNTIME REPLAY ===
    check raisesValueError_finallyReplaces(r.raisedWitness[0])

  # ---------------------------------------------------------------------------
  # E6 shape: assertDefect — AssertionDefect witness replay (x <= 0 path)
  # The engine reports sxRaised{AssertionDefect} with raisedWitness[0] <= 0.
  # REPLAY: call assertDefect(raisedWitness[0]); it MUST raise AssertionDefect.
  # CONTRAST: assertDefect(1) must NOT raise (x > 0 satisfies the assert).
  # ---------------------------------------------------------------------------
  test "E-roundtrip: assertDefect AssertionDefect witness reproduces raise at runtime":
    let r = symexFind(assertDefect, tRaisedExn("AssertionDefect"))
    check r.status == sxRaised
    check r.raisedTypeId == "AssertionDefect"
    check r.raisedWitness[0] <= 0
    # === RUNTIME REPLAY ===
    check raisesAssertionDefect_assertDefect(r.raisedWitness[0])

  test "E-roundtrip: assertDefect contrast input (x=1) does NOT raise AssertionDefect":
    # x == 1 satisfies `assert x > 0`; no Defect raised.
    check not raisesAssertionDefect_assertDefect(1)
