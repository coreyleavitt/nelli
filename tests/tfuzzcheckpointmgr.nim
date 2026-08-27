## RFC-fuzzer-nextgen R27: `CheckpointManager` (fuzzcheckpoint.nim) exercised
## directly — no `fuzz()` campaign, no `ExampleDatabase`, no filesystem. Proves
## the seam extracted from `fuzz[T]` is real: the collaborator is
## constructible and testable with nothing but a couple of closures over a
## local `var seq[byte]`.

import std/unittest
import nelli/[fuzzcheckpoint, coverage, bandit, fuzzir]

suite "CheckpointManager — gating (`active`)":

  test "inactive when cadence is 0, even with both closures set":
    var store: seq[byte]
    let m = newCheckpointManager(0,
      loadImpl = (proc(): seq[byte] = store),
      saveImpl = (proc(data: seq[byte]) = store = data))
    check not active(m)

  test "inactive when loadImpl is nil":
    let m = newCheckpointManager(5, loadImpl = nil,
      saveImpl = (proc(data: seq[byte]) = discard))
    check not active(m)

  test "inactive when saveImpl is nil":
    let m = newCheckpointManager(5,
      loadImpl = (proc(): seq[byte] = @[]), saveImpl = nil)
    check not active(m)

  test "active when cadence > 0 and both closures are set":
    let m = newCheckpointManager(5,
      loadImpl = (proc(): seq[byte] = @[]),
      saveImpl = (proc(data: seq[byte]) = discard))
    check active(m)

suite "CheckpointManager — save/resume round trip":

  test "an inactive manager's save is a no-op (the backing closure is never called)":
    var calls = 0
    var m = newCheckpointManager(0,
      loadImpl = (proc(): seq[byte] = @[]),
      saveImpl = (proc(data: seq[byte]) = inc calls))
    save(m, FrontierStats(), newOperatorBandit(3), Dictionary())
    check calls == 0

  test "save then tryResume on a fresh manager over the same store round-trips":
    var store: seq[byte]
    var writer = newCheckpointManager(5,
      loadImpl = (proc(): seq[byte] = store),
      saveImpl = (proc(data: seq[byte]) = store = data))
    var bandit = newOperatorBandit(3)
    credit(bandit, 1, 2.5)
    var dict: Dictionary
    harvestDictionary(dict, @[CmpLogEntry(kind: clkInt, op: coEq, width: 8,
                                          lhsInt: 7'u64, rhsInt: 0xDEADBEEF'u64)])
    let stats = restoreFrontierStats(@[3, 0, 1], @[2, 0, 1], 5, 2)
    save(writer, stats, bandit, dict)
    check store.len > 0

    var reader = newCheckpointManager(5,
      loadImpl = (proc(): seq[byte] = store),
      saveImpl = (proc(data: seq[byte]) = discard))
    check not resumed(reader)          # nothing loaded yet
    tryResume(reader)
    check resumed(reader)
    let s = resumedState(reader)
    check s.frontierHitCounts == @[3, 0, 1]
    check s.frontierLastImprovedSeq == @[2, 0, 1]
    check s.frontierTotalAdmitted == 5
    check s.frontierLastGlobalImprovedSeq == 2
    check s.banditPulls.len == 3
    check s.dictionary.entries.len == 2   # harvestDictionary records both operands

  test "tryResume on an empty store (nothing saved yet) leaves `resumed` false":
    var store: seq[byte]
    var m = newCheckpointManager(5,
      loadImpl = (proc(): seq[byte] = store),
      saveImpl = (proc(data: seq[byte]) = store = data))
    tryResume(m)
    check not resumed(m)

  test "tryResume on a corrupt/undecodable blob leaves `resumed` false (cold-start)":
    var m = newCheckpointManager(5,
      loadImpl = (proc(): seq[byte] = @[1'u8, 2, 3]),
      saveImpl = (proc(data: seq[byte]) = discard))
    tryResume(m)
    check not resumed(m)

  test "an inactive manager's tryResume never calls loadImpl":
    var calls = 0
    var m = newCheckpointManager(0,
      loadImpl = (proc(): seq[byte] = (inc calls; @[])),
      saveImpl = (proc(data: seq[byte]) = discard))
    tryResume(m)
    check calls == 0
    check not resumed(m)

suite "CheckpointManager — dueAt":

  test "due exactly on cadence multiples":
    let m = newCheckpointManager(5,
      loadImpl = (proc(): seq[byte] = @[]),
      saveImpl = (proc(data: seq[byte]) = discard))
    check not dueAt(m, 1)
    check not dueAt(m, 4)
    check dueAt(m, 5)
    check not dueAt(m, 6)
    check dueAt(m, 10)

  test "an inactive manager (cadence 0) is never due, for any iter":
    let m = newCheckpointManager(0,
      loadImpl = (proc(): seq[byte] = @[]),
      saveImpl = (proc(data: seq[byte]) = discard))
    check not dueAt(m, 0)
    check not dueAt(m, 100)
