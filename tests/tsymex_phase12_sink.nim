## Phase 12 cycle 1 — symex finding sink lives in `engine/types.nim`.
##
## Pre-requisite for Layer 1: `engine/phases.nim` will need to
## record findings from the symex seed phase without importing
## `proptest/symex` (which pulls in the entire z3 + SMT stack).
## The sink (threadvar + record + consume) belongs alongside the
## `SymexFinding` / `SymexFindingStatus` types that already live in
## `engine/types.nim`.
##
## This test imports the sink from the engine module ONLY — no
## `proptest/symex` import. If the sink is still in `symex.nim`,
## the imports fail.

import std/unittest
import proptest/engine/types

suite "symex Phase 12 cycle 1 — sink accessible from engine/types":
  test "recordSymexFinding + consumeSymexFindings importable":
    # Cycle 1's contract: these symbols live in engine/types now.
    discard consumeSymexFindings()  # clear any prior state

    recordSymexFinding(SymexFinding(
      targetDesc: "test", status: sfSat, covered: true,
      z3Version: "test"))

    let drained = consumeSymexFindings()
    check drained.len == 1
    check drained[0].targetDesc == "test"
    check drained[0].status == sfSat

    # Second drain returns empty (the first drain cleared the
    # threadvar atomically).
    check consumeSymexFindings().len == 0
