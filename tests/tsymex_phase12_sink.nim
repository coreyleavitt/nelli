## Phase 12 cycle 1 put a thread-local `SymexFinding` sink in
## `engine/types.nim` (`recordSymexFinding` / `consumeSymexFindings`) so
## phase modules could record findings without importing `nelli/symex`.
##
## Review R1-10 removed it: only `symexForAll` drained it, so findings from
## an earlier call on the thread leaked into a later report. A finding now
## rides a value: the engine's phases record on the run's own state
## (`EngineAccumulators.symexFindings`), and every symex entry point returns
## its findings. This test pins that the sink is gone, from `engine/types`
## and from `nelli/symex` alike, while the types stay importable without the
## z3 stack.

import std/unittest
import nelli/engine/types

suite "review R1-10 -- no thread-local finding sink":
  test "the finding types are importable from engine/types alone":
    let f = SymexFinding(targetDesc: "test", status: sfSat, covered: true,
                         z3Version: "test")
    var r: Report[int]
    r.symexFindings.add f
    check r.symexFindings.len == 1

  test "recordSymexFinding and consumeSymexFindings no longer exist":
    check not compiles(recordSymexFinding(SymexFinding()))
    check not compiles(consumeSymexFindings())
