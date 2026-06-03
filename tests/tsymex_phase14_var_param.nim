## Phase 14 cycle A7a — `var T` parameter support at parser +
## `symexFind` level.
##
## Per RFC §A7 (corrected): `classifyType` already silently
## unwraps `nnkVarTy` (dsl_typebridge.nim:48-49), and `parseProc`
## accepts the param. The remaining gap: `parseProc` doesn't set
## `isVar = true` on top-level SUT params (only `parseCalleeImpl`
## does). The witness contract for a `var T` SUT param is the
## **initial value** — pre-mutation — sourced via the walker's
## `initialEnv` path (runtime.nim:1319-1322).
##
## A7a RED test: a SUT mutates its `var int` param and gates a
## target on the post-mutation value. The witness must be the
## INITIAL value (one less than the target), confirming that
## (a) `var T` parses without error, (b) `symexFind` returns
## sxSat, (c) the witness reflects pre-mutation state.
import std/unittest
import proptest/symex

proc incThenCheck(x: var int) =
  x = x + 1
  if x == 42:
    symexTarget("incremented-to-42")

suite "symex Phase 14 cycle A7a — var T parameter support":
  test "var int SUT: witness is the INITIAL value (pre-mutation)":
    let r = symexFind(incThenCheck, tLabel("incremented-to-42"))
    check r.status == sxSat
    # The walker reaches the target only when x+1 == 42, so the
    # initial-value witness must be x == 41.
    check r.witness[0] == 41
