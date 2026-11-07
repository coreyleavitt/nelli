## RFC-0016 W1-d2 (W-07), the checks-off build half of R16-4-8 in
## `tsymex_phase16_R16_4_overflow`. Built with `--overflowChecks:off` (its
## `.nim.cfg`): no OverflowDefect fork is emitted because the build does not
## check, and the signed overflow itself is undefined, a `ubSignedOverflow`
## halt rather than the old trusted sxUnsat.
import std/unittest
import nelli/symex
import ./s8cu_helpers

proc sa_off(a, b: int) =
  let c = a + b
  symexTarget("toff")
  discard c

suite "symex Phase 16 R16-4 -- acOverflow gate, checks-off build":
  test "R16-4-8 (rule a): checks off -> no OverflowDefect raise; the overflow halts":
    check acOverflow notin defaultSymexSettings().arithChecks
    let r = symexFind(sa_off, tRaisedExn("OverflowDefect"))
    check r.status != sxRaised
    check not r.trusted
    check r.errors.named(ubSignedOverflow)
    check not r.errors.named(feCheckOption)
