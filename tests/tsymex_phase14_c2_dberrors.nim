## Phase 14 cycle C2 — Layer 1's `dbErrors` wired into the
## engine sink + `Report.dbErrors`.
##
## Pre-C2 the local `dbErrors` accumulator inside
## `symexFindAllWitnesses`'s emitted runtime absorbed DB save/load
## failures into a dead-end local; the engine's `Report.dbErrors`
## (a user-visible surface) never saw them.
##
## Post-C2: a thread-local `engineSymexDbErrors` is the bridge.
## Layer 1 drains its local accumulator into the threadvar at the
## end of its emitted block; `finalizePhase` consumes the threadvar
## and concatenates onto `state.acc.dbErrors` when building the
## terminal Report.
import std/unittest
import proptest/engine/types

suite "symex Phase 14 cycle C2 — engineSymexDbErrors sink":
  test "recordSymexDbError appends and consumeSymexDbErrors drains":
    discard consumeSymexDbErrors()  # baseline clear
    recordSymexDbError("io-error: disk full")
    recordSymexDbError("permission-denied: /tmp/db")
    let drained = consumeSymexDbErrors()
    check drained.len == 2
    check drained[0] == "io-error: disk full"
    check drained[1] == "permission-denied: /tmp/db"
    # After draining, the sink is empty.
    check consumeSymexDbErrors().len == 0
