## Phase 12 cycle 13 — `runForAllPipelineWithPhases` extraction.
##
## Layer 2's symex-seed pipeline (cycle 15) needs to swap the default
## phase list out for a custom one. Cycle 13 extracts the runner so
## the phase list becomes an injectable seam without duplicating any
## of the preamble (deadline wrap, autoLabel sink, coverage init,
## derandomize-seed derivation).
##
## Test: passing `defaultPhases[T]()` to the new helper must produce
## a Report with the same outcome as the existing entry point on a
## falsifying property.
import std/unittest
import nelli
import nelli/engine/phases
import nelli/engine

suite "symex Phase 12 cycle 13 — runForAllPipelineWithPhases":
  test "with defaultPhases the helper reports the same falsification as forAll":
    let s = integers(0, 100)
    proc prop(x: int) =
      # Falsifies on every value > 50.
      doAssert x <= 50

    let viaForAll = forAll(s, prop)
    let viaHelper = runForAllPipelineWithPhases(
      inMemoryDatabase(), dbEnabled = false,
      s, prop, defaultSettings(), toExamples[int](@[]),
      defaultPhases[int]())

    # Both paths must reach the same terminal verdict.
    check viaForAll.outcome == otFalsified
    check viaHelper.outcome == otFalsified
