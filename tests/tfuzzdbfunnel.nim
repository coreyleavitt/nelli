## RFC-fuzzer-nextgen E3b C4: the `.bin` single-writer funnel + the F-1
## invariant (E0-findings item F-1).
##
## E0's spike found that `directoryBasedDatabase(path)`'s constructor sweeps
## stray `.tmp.*` files on startup, so two CONCURRENT constructions against
## the same directory race on that sweep — one construction's in-flight tmp
## file can be deleted by the other's startup sweep (`OSError` on
## `moveFile`). The centralized `Orchestrator` already implies a single
## long-lived handle; this suite pins that as a stated invariant: the
## orchestrator is constructed with exactly ONE `ExampleDatabase`
## (`newOrchestrator(..., db = ...)`), and `requestSave`/`requestRemove`/
## `requestSaveSecondary` (fuzz.nim) are the ONLY way a shrink job's `.bin`
## write reaches disk — there is no code path, here or anywhere in fuzz.nim,
## that constructs a second `directoryBasedDatabase` on the orchestrator's
## directory. `saveCorpus`/`loadCorpus` are NOT part of this funnel — the
## corpus delta log (db.nim, E3b C1-C3) is already single-writer via its own
## append-only transport, a different file from `.bin` entirely.

import std/[unittest, os, tables]
import nelli
import nelli/[choice]

suite "E3b C4: .bin single-writer funnel (F-1 invariant)":
  test "no db configured: requestSave/requestRemove/requestSaveSecondary are silent no-ops":
    # The zero-value default (`newOrchestrator` with no `db` arg) must leave
    # every existing caller byte-for-byte unchanged — the funnel is opt-in.
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(5), target, frontier)
    check not o.hasDb()
    o.requestSave("k", @[integerChoice(1, 0, 100, 0)])
    o.requestRemove("k", @[integerChoice(1, 0, 100, 0)])
    var noLabels: Table[string, float]
    o.requestSaveSecondary("k", @[(choices: @[integerChoice(1, 0, 100, 0)],
                                   score: 1.0, scores: noLabels)])
    # No exception is the whole assertion — there is nowhere for these to
    # have gone.

  test "requestSave funnels through the orchestrator's one db handle (visible via db.loadPrimary)":
    let db = inMemoryDatabase()
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(5), target, frontier, db = db)
    check o.hasDb()
    o.requestSave("shrink-witness", @[integerChoice(42, 0, 100, 0)])
    check db.loadPrimary("shrink-witness") == @[@[integerChoice(42, 0, 100, 0)]]

  test "requestRemove funnels through and drops exactly the targeted entry":
    let db = inMemoryDatabase()
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(5), target, frontier, db = db)
    o.requestSave("k", @[integerChoice(1, 0, 100, 0)])
    o.requestSave("k", @[integerChoice(2, 0, 100, 0)])
    o.requestRemove("k", @[integerChoice(1, 0, 100, 0)])
    check db.loadPrimary("k") == @[@[integerChoice(2, 0, 100, 0)]]

  test "requestSaveSecondary funnels through, highest-score-first on read":
    let db = inMemoryDatabase()
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(5), target, frontier, db = db)
    var noLabels: Table[string, float]
    o.requestSaveSecondary("k", @[
      (choices: @[integerChoice(1, 0, 100, 0)], score: 10.0, scores: noLabels),
      (choices: @[integerChoice(2, 0, 100, 0)], score: 20.0, scores: noLabels),
    ])
    let all = db.loadSecondary("k")
    check all.len == 2
    check all[0].score == 20.0

  test "F-1: two 'shrink jobs' issuing requestSave through the SAME orchestrator share one state":
    # A structural, non-timing-dependent proof of single-writer-ness: two
    # separate requestSave calls (standing in for two independent shrink
    # jobs) for the SAME testId+choices dedup to exactly one entry — which
    # could only happen if both calls landed in the same underlying store,
    # not two private handles a worker slot might have constructed itself.
    let dbPath = getTempDir() / "nelli_test_dbfunnel_f1"
    removeDir(dbPath)
    let db = directoryBasedDatabase(dbPath)
    var frontier = newCoverageFrontier()
    let target = Target[int](run: proc(x: int): Observation[int] =
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let o = newOrchestrator(just(5), target, frontier, db = db)
    let witness = @[integerChoice(7, 0, 100, 0)]
    o.requestSave("shared", witness)    # "shrink job A"
    o.requestSave("shared", witness)    # "shrink job B" — same testId+choices
    check db.loadPrimary("shared").len == 1   # deduped, not duplicated
    removeDir(dbPath)
