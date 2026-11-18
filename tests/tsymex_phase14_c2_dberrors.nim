## Phase 14 cycle C2 — Layer 1's `dbErrors` wired into the
## engine sink + `Report.dbErrors`.
##
## Pre-C2 the local `dbErrors` accumulator inside
## `symexFindAllWitnesses`'s emitted runtime absorbed DB save/load
## failures into a dead-end local; the engine's `Report.dbErrors`
## (a user-visible surface) never saw them.
##
## Post-C2: Layer 1 records each error with `recordSymexDbError`. RFC-0016
## INT-34: inside a run it is that run's (its frame's, then its report's);
## outside any run it is held for the caller, who reads it with
## `consumeSymexDbErrors` (this suite; `tsymex_0016_int34_dberrors` has the
## run-owned side).
import std/unittest
import nelli/engine/frame

suite "symex Phase 14 cycle C2 — DB errors made outside any run":
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
