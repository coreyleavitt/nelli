import std/[unittest, os, tables, strutils]
import nelli
import nelli/[choice]
import zerofill  # RFC-0010 A1 pin; removed by A3

# New pluggable backends + error surfacing for the ExampleDatabase
# closure-record interface.

suite "inMemoryDatabase":
  test "primary save/load round-trips a single sequence":
    let db = inMemoryDatabase()
    let cs = @[integerChoice(7, 0, 100, 0)]
    db.save("t1", cs)
    let loaded = db.loadPrimary("t1")
    check loaded == @[cs]

  test "no cross-test contamination":
    let db = inMemoryDatabase()
    db.save("a", @[integerChoice(1, 0, 100, 0)])
    db.save("b", @[integerChoice(2, 0, 100, 0)])
    check db.loadPrimary("a").len == 1
    check db.loadPrimary("b").len == 1
    check db.loadPrimary("a")[0] != db.loadPrimary("b")[0]

suite "multiplexedDatabase":
  test "reads union both; writes go to primary only":
    let localDb = inMemoryDatabase()
    let sharedDb = inMemoryDatabase()
    # Pre-populate shared with a known entry (the "reference corpus").
    let refCs = @[integerChoice(42, 0, 100, 0)]
    sharedDb.save("k", refCs)
    let multiplexed = multiplexedDatabase(localDb, sharedDb)
    # The load sees the shared entry even though local is empty.
    let initial = multiplexed.loadPrimary("k")
    check refCs in initial

    # Write goes to local only.
    let localCs = @[integerChoice(7, 0, 100, 0)]
    multiplexed.save("k", localCs)
    check localCs in localDb.loadPrimary("k")
    check localCs notin sharedDb.loadPrimary("k")

    # Load now sees both.
    let combined = multiplexed.loadPrimary("k")
    check refCs in combined
    check localCs in combined

suite "readOnlyDatabase":
  test "save raises DbError; loads succeed":
    let inner = inMemoryDatabase()
    inner.save("k", @[integerChoice(1, 0, 100, 0)])
    let ro = readOnlyDatabase(inner)
    # Read paths still work.
    check ro.loadPrimary("k").len == 1
    # Write paths raise.
    expect DbError:
      ro.save("k", @[integerChoice(2, 0, 100, 0)])
    expect DbError:
      ro.remove("k", @[integerChoice(1, 0, 100, 0)])

# A backend that always fails — exercises the engine's error-surfacing path.
proc failingDatabase(): ExampleDatabase =
  result.saveImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    raise newException(DbError, "boom on save")
  result.loadPrimaryImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    raise newException(DbError, "boom on loadPrimary")
  result.removeImpl = proc(testId: string, choices: seq[ChoiceNode]) =
    raise newException(DbError, "boom on remove")
  result.removeManyImpl = proc(testId: string, stale: seq[seq[ChoiceNode]]) =
    raise newException(DbError, "boom on removeMany")
  result.saveSecondaryImpl = proc(testId: string, entries: seq[ScoredEntry], maxEntries: int) =
    raise newException(DbError, "boom on saveSecondary")
  result.loadSecondaryImpl = proc(testId: string): seq[ScoredEntry] =
    raise newException(DbError, "boom on loadSecondary")
  result.loadCorpusImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    # RFC-fuzzer-nextgen U2: `corpusReplayPhase` now reads the corpus
    # section on every `dbEnabled` run, so this fixture — like the other
    # sections above — must implement it rather than leave the closure
    # nil (a nil closure call is a crash, not a `DbError`).
    raise newException(DbError, "boom on loadCorpus")

suite "Report.dbErrors":
  test "default mode: DB errors are recorded, run continues":
    let r = forAllUsing(failingDatabase(),
                       integers(0, 9),
                       proc(x: int) = (ensure true),
                       zeroFilled(Settings(maxExamples: 5, seed: 1,
                                           flakyRetries: 0, maxShrinks: 5,
                                           maxRejections: 20,
                                           testId: "with-failing-db")))
    # Run completes (no DB → otPassed), but the error surfaces.
    check r.outcome == otPassed
    check r.dbErrors.len > 0
    check "boom" in r.dbErrors[0]

  test "strictDb = true: a DB error is a fatal outcome":
    let r = forAllUsing(failingDatabase(),
                       integers(0, 9),
                       proc(x: int) = (ensure true),
                       zeroFilled(Settings(maxExamples: 5, seed: 1,
                                           flakyRetries: 0, maxShrinks: 5,
                                           maxRejections: 20,
                                           testId: "with-failing-db",
                                           strictDb: true)))
    check r.outcome == otFalsified
    check "DB" in r.message or "db" in r.message
