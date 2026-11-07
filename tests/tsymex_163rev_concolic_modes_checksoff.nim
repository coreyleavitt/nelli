## RFC-0016 W1-d2 (W-07), the checks-off build half of
## `tsymex_163rev_concolic_modes` D2. This file builds with
## `--overflowChecks:off` (its `.nim.cfg`), where signed `+` of two int8 that
## overflows is undefined behaviour in the walker's model, not a wrap: the
## old trusted `sxSat` at a=100, b=100 was a witness the binary need not reach.
## The overflowing pair is therefore a `ubSignedOverflow` halt (not trusted).
## The width/sign binding property itself is pinned, trusted, in the checked
## file through an in-window sum.
import std/unittest
import nelli/smt/canonicalize
import nelli/symex
import ./s8cu_helpers

proc addI8UncheckedGate(a, b: int8) =
  if a + b < a:
    symexTarget("i8_wrapped")

proc addI8UncheckedGateAt100_100(a, b: int8) =
  if a == 100'i8 and b == 100'i8 and a + b < a:
    symexTarget("i8_wrapped_100_100")

suite "#163 review R16 D2 -- signed narrow width, checks-off build":
  test "D2 oracle: under unchecked arithmetic, 100'i8 + 100'i8 wraps to -56":
    {.push overflowChecks: off.}
    proc rt(a, b: int8): int8 = a + b
    {.pop.}
    let c = rt(100'i8, 100'i8)
    check c == -56'i8
    check c < 100'i8

  test "the build is checks-off and the default settings agree":
    check buildWraps()
    check not arithChecksDisagree(defaultSymexSettings())

  test "D2 wmExplore (rule a): the overflow at a=100, b=100 halts, not a trusted sat":
    let r = symexFind(addI8UncheckedGateAt100_100, tLabel("i8_wrapped_100_100"))
    check not r.trusted
    check r.errors.named(ubSignedOverflow)

  test "D2 wmFollowConcrete (rule a): the overflowing pair no longer satisfies the path":
    ## The concrete inputs reach the undefined overflow side, which is halted,
    ## not followed.
    let trace = @[integerChoice(100, -128, 127, 0), integerChoice(100, -128, 127, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(addI8UncheckedGate, trace, bindings)
    check not r.pcSatByConcreteInputs

  test "D2 wmFollowConcrete (control): an in-window pair still follows the narrow width":
    let trace = @[integerChoice(0, -128, 127, 0), integerChoice(-5, -128, 127, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(addI8UncheckedGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == 0
