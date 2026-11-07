## RFC-0016 W1-d2 (W-07), the checks-off build half of
## `tsymex_phase2_overflow`. Built with `--overflowChecks:off` (its
## `.nim.cfg`). RFC-0016 WA-B (P1): an int8 `x + 1 < x` is `(NI8)(x + 1)`,
## computed in `int` and narrowed back, a defined wrap, so x = 127 is an exact
## trusted witness in every integer mode (only 32 and 64 bit signed overflow
## is undefined, a `ubSignedOverflow` halt; see `tsymex_0016_checksoff`).
import std/unittest
import nelli/symex
import ./s8cu_helpers

proc wrapNeeded(x: int8) =
  if x + 1 < x:
    symexTarget("wrap-needed")

suite "symex Phase 2 -- ADR-0001, checks-off build (signed overflow is undefined)":
  test "the default settings follow the build":
    check not arithChecksDisagree(defaultSymexSettings())

  test "isExact (rule a): the int8 wrap is an exact witness (RFC-0016 WA-B, P1)":
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"),
                      SymexSettings(integerSemantics: isExact))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 127'i8
    check not r.errors.named(ubSignedOverflow)

  test "isOptimised (rule a): the same":
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), SymexSettings(integerSemantics: isOptimised))
    check r.status == sxSat
    check r.trusted
    check r.witness[0] == 127'i8
    check not r.errors.named(ubSignedOverflow)
