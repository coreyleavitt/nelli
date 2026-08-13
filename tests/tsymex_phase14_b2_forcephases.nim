## Phase 14 cycle B2 — `Settings.forcePhases: set[PhaseId]`.
##
## Phase 13 baseline: `symexSeedPhase` self-gated on
## `rawFalsification.isSome`, so a prior phase's counterexample
## skipped the seed-replay. B2 adds an explicit per-phase escape
## hatch: `phSymexSeed in settings.forcePhases` forces the phase
## to run regardless, with the contract that any pre-existing
## `rawFalsification` is preserved (not overwritten).
##
## Default behaviour (empty `forcePhases`) is unchanged.
import std/unittest
import nelli/engine/types

suite "symex Phase 14 cycle B2 — Settings.forcePhases":
  test "PhaseId enum exposes phSymexSeed":
    var s: set[PhaseId]
    s.incl phSymexSeed
    check phSymexSeed in s

  test "Settings.forcePhases defaults to empty":
    var settings: Settings
    check settings.forcePhases.len == 0

  test "forcePhases is a regular set member that round-trips":
    var settings: Settings
    settings.forcePhases.incl phSymexSeed
    settings.forcePhases.incl phShrink
    check phSymexSeed in settings.forcePhases
    check phShrink in settings.forcePhases
    check phRandom notin settings.forcePhases
