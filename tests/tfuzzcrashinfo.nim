## RFC-fuzzer-nextgen E1 stage 1, C1: typed `CrashInfo` on `Observation`.
## Crash identity moves from a stringly-typed `message` to a `case kind`
## variant (`ckException`/`ckSignal`/`ckExitCode`/`ckWinException`) so
## dedup/oracle logic can match on `kind` instead of grepping prose out of
## `message`. This file pins the in-process wiring (`inProcessTarget`,
## `fuzz.nim`): a property `Defect` or `CatchableError` populates
## `Observation.crash` with `kind == ckException` and the raising type's
## name; `Observation.message` is unchanged in shape/content, now DERIVED
## from `crash.get.message` when a crash is present. See `tfuzzdedup.nim`
## for the dedup-side pin (same message, different kind, no collision).

import std/[unittest, options]
import nelli

proc failsAssert(x: int) {.cover.} =
  doAssert x != 0, "x must be nonzero"

proc raisesValueError(x: int) {.cover.} =
  raise newException(ValueError, "bad value")

proc neverCrashes(x: int) {.cover.} =
  discard x

suite "fuzz: typed CrashInfo (RFC-fuzzer-nextgen E1 C1)":
  test "a failed doAssert populates Observation.crash with kind ckException":
    let target = inProcessTarget(failsAssert)
    let obs = target.run(0)
    check obs.verdict == vInteresting
    check obs.crash.isSome
    check obs.crash.get.kind == ckException
    check obs.crash.get.defect == "AssertionDefect"
    # message stays a human rendering, now DERIVED from crash.get.message
    check obs.message == obs.crash.get.message

  test "a raised CatchableError also populates Observation.crash with kind ckException":
    let target = inProcessTarget(raisesValueError)
    let obs = target.run(1)
    check obs.verdict == vInteresting
    check obs.crash.isSome
    check obs.crash.get.kind == ckException
    check obs.crash.get.defect == "ValueError"
    check obs.message == obs.crash.get.message

  test "a passing run leaves Observation.crash empty":
    let target = inProcessTarget(neverCrashes)
    let obs = target.run(5)
    check obs.verdict == vOk
    check obs.crash.isNone
