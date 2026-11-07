## RFC-0016 W1-d2 (W-07), the checks-off build half of
## `tsymex_phase2_overflow`. Built with `--overflowChecks:off` (its
## `.nim.cfg`): signed `x + 1 < x` for an int8 is not a modelled wrap. The
## overflow side (x = 127) is undefined behaviour, a `ubSignedOverflow` halt,
## in every integer mode; the old trusted sxSat witness x = 127 is gone.
import std/unittest
import nelli/symex
import ./s8cu_helpers

proc wrapNeeded(x: int8) =
  if x + 1 < x:
    symexTarget("wrap-needed")

suite "symex Phase 2 -- ADR-0001, checks-off build (signed overflow is undefined)":
  test "the default settings follow the build":
    check not arithChecksDisagree(defaultSymexSettings())

  test "isExact (rule a): the overflow side halts, no trusted wrap witness":
    var s = defaultSymexSettings()
    s.integerSemantics = isExact
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), s)
    check not r.trusted
    check r.errors.named(ubSignedOverflow)

  test "isOptimised (rule a): the same":
    let r = symexFind(wrapNeeded, tLabel("wrap-needed"), optimisedSymexSettings())
    check not r.trusted
    check r.errors.named(ubSignedOverflow)
