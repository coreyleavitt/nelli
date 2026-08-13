## Phase 12 cycle 2 — `Phase[T].run` accepts closure procs.
##
## Cycle 14's `symexSeedPhase(seeds): Phase[T]` constructs a Phase
## that closes over `seeds: seq[seq[ChoiceNode]]`. The pre-Phase-12
## `Phase[T].run` was `{.nimcall.}` — captures forbidden.
##
## This test constructs a Phase whose `run` closes over an outer
## variable, then invokes it. With `.nimcall` the assignment is a
## compile error; with `.closure` it works.
import std/unittest
import nelli/engine/pipeline
import nelli/engine/types

proc makePhase(captured: int): Phase[int] =
  # A phase constructor that closes over a runtime argument. This is
  # the exact pattern symexSeedPhase(seeds) will use. With `{.nimcall.}`
  # the inner proc literal cannot capture `captured` and the proc
  # fails to compile. With `{.closure.}` it works.
  Phase[int](
    name: "test-closure",
    run: proc(state: var EngineState[int]): PhaseAction =
      result = (if captured == 42: pcTerminate else: pcContinue))

suite "symex Phase 12 cycle 2 — Phase[T].run accepts closures":
  test "a phase constructor can return a closure-capturing phase":
    let p42 = makePhase(42)
    let p99 = makePhase(99)
    var dummy: EngineState[int]
    check p42.run(dummy) == pcTerminate
    check p99.run(dummy) == pcContinue
