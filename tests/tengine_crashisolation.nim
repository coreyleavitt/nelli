## RFC-fuzzer-nextgen U0: forAll gains the same in-process crash-isolation
## boundary Track E's Worker/`inProcessTarget` formalized for `fuzz` —
## a property `Defect` (failed `doAssert`, `IndexDefect`, etc.) is caught,
## treated as an ordinary falsification, shrunk to a minimal example, and
## reported with typed `CrashInfo` (the same `CrashKind`/`CrashInfo` shape
## `fuzz.nim`'s `Observation.crash` uses — moved to `nelli/crashinfo.nim` so
## both front doors share one type). A non-Defect falsification (`ensure`)
## is unaffected: no `crash` info, identical shrink as before.

import std/[unittest, options]
import nelli

suite "engine: forAll crash isolation (RFC-fuzzer-nextgen U0)":
  test "a failed doAssert is caught, shrunk to the minimal failing example, not an abort":
    proc crashesAtBoundary(x: int) =
      doAssert x < 500, "must stay below 500"
    let r = forAll(integers(0, 1000), crashesAtBoundary,
                   Settings(maxExamples: 300, seed: 42))
    check r.outcome == otFalsified
    check r.counterexample.isSome
    check r.counterexample.get == 500      # minimal still-failing x
    check r.crash.isSome
    check r.crash.get.kind == ckException
    check r.crash.get.defect == "AssertionDefect"

  test "an IndexDefect is caught, shrunk to the minimal failing example":
    proc crashesOnIndex(x: int) =
      let arr = [10, 20, 30]
      discard arr[x]
    let r = forAll(integers(0, 10), crashesOnIndex,
                   Settings(maxExamples: 100, seed: 7))
    check r.outcome == otFalsified
    check r.counterexample.isSome
    check r.counterexample.get == 3         # smallest out-of-bounds index
    check r.crash.isSome
    check r.crash.get.kind == ckException
    check r.crash.get.defect == "IndexDefect"

  test "determinism: same seed reproduces the same crash falsification and shrink":
    proc crashesAtBoundary(x: int) =
      doAssert x < 500, "must stay below 500"
    let r1 = forAll(integers(0, 1000), crashesAtBoundary,
                    Settings(maxExamples: 300, seed: 42))
    let r2 = forAll(integers(0, 1000), crashesAtBoundary,
                    Settings(maxExamples: 300, seed: 42))
    check r1.outcome == r2.outcome
    check r1.counterexample.get == r2.counterexample.get
    check r1.choices == r2.choices
    check r1.crash.get.kind == r2.crash.get.kind
    check r1.crash.get.defect == r2.crash.get.defect

  test "a normal (non-Defect) falsification via ensure is unaffected: no crash info":
    proc smallerThan50(x: int) = ensure x < 50
    let r = forAll(integers(0, 100), smallerThan50,
                   Settings(maxExamples: 100, seed: 5))
    check r.outcome == otFalsified
    check r.counterexample.get >= 50
    check r.crash.isNone

  test "a passing property is unaffected: no crash info, no overhead change to outcome":
    let r = forAll(integers(0, 100), proc(x: int) = ensure x + 0 == x)
    check r.outcome == otPassed
    check r.examples == 100
    check r.crash.isNone
