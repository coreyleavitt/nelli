## Phase 15 — Cluster E, cycle E2b: REAL `walk(isRaise)` semantics +
## `InternalVerdict` boundary. E2a wired `sxRaised` structurally (no witness, no
## msg, no Z3); E2b makes the raise-path real: the walker solves the raise path
## for a concrete witness, evaluates `raiseMsg` into `raisedMsg`, and routes the
## finding through a PRIVATE `InternalVerdict` union mapped to public `sxRaised`
## exactly once at the `runSymex` boundary (`toPublic`, Invariant 9).
import std/unittest
import nelli/symex
import nelli/smt/[dsl, runtime]

# --- unconditional raise ----------------------------------------------------
proc uncondRaise(x: int) =
  raise newException(ValueError, "always")

# --- conditional raise: only on x > 0 ---------------------------------------
proc condRaise(x: int) =
  if x > 0:
    raise newException(ValueError, "pos")

suite "symex Phase 15 E2b — real raise semantics + InternalVerdict boundary":
  test "E2b: unconditional raise yields sxRaised with raisedTypeId (isExact)":
    let r = symexFind(uncondRaise, tAssertionViolation())
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"

  test "E2b: unconditional raise yields sxRaised (isOptimised)":
    let r = symexFind(uncondRaise, tAssertionViolation(), optimisedSymexSettings())
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"

  test "E2b: conditional raise — non-existent label is sxUnsat":
    let r = symexFind(condRaise, tLabel("unreachable"))
    check r.status == sxUnsat

  test "E2b: conditional raise — stkRaisedExn finds witness with x > 0 (isExact)":
    let r = symexFind(condRaise, tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    # The witness must satisfy the raise path condition x > 0.
    check r.raisedWitness[0] > 0

  test "E2b: conditional raise — stkRaisedExn finds witness with x > 0 (isOptimised)":
    let r = symexFind(condRaise, tRaisedExn("ValueError"), optimisedSymexSettings())
    check r.status == sxRaised
    check r.raisedTypeId == "ValueError"
    check r.raisedWitness[0] > 0
