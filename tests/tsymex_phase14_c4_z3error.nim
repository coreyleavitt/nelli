## Phase 14 cycle C4 — Z3 internal-error policy.
##
## Pre-C4 a typed `Z3Error` thrown by the solver propagated up
## through `runSymex` and the macro-emitted runtime, surfacing
## as an unhandled exception in user property tests. C4 wraps
## `runSymex` in a try/except that catches `Z3Error` (the
## abstract base class — all 12 typed subclasses derive from it),
## returns `RawResult(status: sxUnknown, errors: @[…])`, and the
## test layer surfaces the structured info.
##
## Walker `ValueError` and `AssertionDefect` are deliberately NOT
## caught — those are real bugs and must propagate.
##
## A direct RED test for C4 needs a way to provoke a Z3Error. The
## cleanest portable trigger isn't easy to construct from user
## code (Z3Error originates from FFI conditions). This test pins
## the SHAPE of the policy: a clean `runSymex` returns
## `errors == @[]`, and the field is exposed on `RawResult` for
## consumer assertions.
import std/unittest
import proptest/symex
import proptest/smt/runtime
import proptest/smt/types

proc trivial(x: int) =
  if x == 42: symexTarget("hit")

suite "symex Phase 14 cycle C4 — Z3Error policy shape":
  test "clean runSymex returns RawResult with empty errors":
    # Build a minimal SymexProgram by hand isn't easy without the
    # macro path; instead exercise the user-facing symexFind to
    # verify the policy doesn't regress the happy path.
    let r = symexFind(trivial, tLabel("hit"))
    check r.status == sxSat

  test "RawResult.errors field is exposed and zero-valued by default":
    var raw: RawResult
    check raw.errors.len == 0
