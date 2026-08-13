## Phase 12 cycle 15 — `forAllWithSymexSeeds` (Layer 2 entry).
##
## Public engine entry that runs the canonical PBT pipeline with
## `symexSeedPhase` slotted in between `explicit` and `random`. A
## hand-crafted falsifying seed flows through the same shrink +
## finalize machinery as a random falsification; the resulting
## Report is otFalsified with a shrunk counterexample.
import std/[unittest, options]
import nelli
import nelli/choice
import nelli/int128
import nelli/symex
import nelli/engine/types

suite "symex Phase 12 cycle 15 — forAllWithSymexSeeds":
  test "falsifying seed produces a shrunk otFalsified report":
    let s = integers(0, 1000)
    proc prop(x: int) =
      doAssert x < 100

    let seed = @[integerChoice(200'i64, 0'i64, 1000'i64, 0'i64)]
    let report = forAllWithSymexSeeds(@[seed], s, prop)

    check report.outcome == otFalsified
    check report.counterexample.isSome
    # The shrinker found the minimal boundary value 100.
    check report.counterexample.get == 100
