## F1 (docs/RFC-chapulin-hardening.md ~line 630): a non-pruned "coverage corpus"
## channel, separate from the regression-replay primary that `dbReusePhase`
## (`engine/phases.nim:65-84`) replays and prunes on pass/reject.
##
## `dbReusePhase`'s prune-on-pass contract is correct for regression witnesses
## (a saved failure that no longer falsifies is stale — discard it) but wrong
## for a coverage-guided fuzzer's corpus: a seed that currently passes still
## exercised a useful path and should survive to seed the next campaign. This
## suite pins the new `saveCorpus`/`loadCorpus` DB section (`db.nim`) and its
## wiring into `fuzz.nim`'s corpus persistence (previously `db.nim`'s
## `primary` section, migrated by F1 — see `tfuzzpersist.nim`).

import std/[unittest, os, tables]
import proptest
import proptest/[choice]

suite "F1: coverage-corpus channel — retention vs. primary's pruning":
  setup:
    let dbPath = getTempDir() / "proptest_test_covcorpus_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "a passing entry is pruned from primary but retained in corpus (same testId)":
    let db = newExampleDB(dbPath)
    let choices = @[integerChoice(5, 0, 100, 0)]
    db.save("mix", choices)          # regression-replay primary
    db.saveCorpus("mix", choices)    # F1 coverage corpus
    check db.loadPrimary("mix").len == 1
    check db.loadCorpus("mix").len == 1

    proc prop(x: int) = ensure x >= 0   # always holds — nothing to falsify
    let s = Settings(maxExamples: 10, maxRejections: 100, seed: 1,
                     testId: "mix", dbPath: dbPath)
    let r = forAll(integers(0, 100), prop, s)
    check r.outcome == otPassed
    # Existing behavior unchanged: a stale (now-passing) primary entry is pruned.
    check newExampleDB(dbPath).loadPrimary("mix").len == 0
    # F1: the corpus entry is untouched by dbReusePhase.
    check newExampleDB(dbPath).loadCorpus("mix").len == 1
    check newExampleDB(dbPath).loadCorpus("mix")[0] == choices

  test "a rejected entry is pruned from primary but retained in corpus":
    let db = newExampleDB(dbPath)
    let choices = @[integerChoice(5, 0, 100, 0)]
    db.save("mix-reject", choices)
    db.saveCorpus("mix-reject", choices)

    proc prop(x: int) =
      if x >= 0: assume false   # unconditionally rejects
      ensure false
    let s = Settings(maxExamples: 10, maxRejections: 1000, seed: 1,
                     testId: "mix-reject", dbPath: dbPath)
    let r = forAll(integers(0, 100), prop, s)
    check r.outcome != otFalsified
    check newExampleDB(dbPath).loadPrimary("mix-reject").len == 0
    check newExampleDB(dbPath).loadCorpus("mix-reject").len == 1

  test "dbReusePhase never replays the corpus channel: no dbReplays credit, no pruning on falsify":
    let db = newExampleDB(dbPath)
    # Primary holds the real regression witness (falsifies x < 50).
    db.save("multi2", @[integerChoice(80, 0, 100, 0)])
    # Corpus holds an unrelated coverage seed that would ALSO falsify if it
    # were ever replayed — proving dbReusePhase doesn't even look at it.
    db.saveCorpus("multi2", @[integerChoice(90, 0, 100, 0)])

    proc prop(x: int) = ensure x < 50
    let s = Settings(maxExamples: 1, maxRejections: 100, seed: 1,
                     testId: "multi2", dbPath: dbPath)
    let r = forAll(integers(0, 100), prop, s)
    check r.outcome == otFalsified
    check r.dbReplays == 1   # only the primary entry was replayed
    check newExampleDB(dbPath).loadCorpus("multi2").len == 1
    check newExampleDB(dbPath).loadCorpus("multi2")[0] == @[integerChoice(90, 0, 100, 0)]

  test "the two channels are independent: corpus growth doesn't touch primary and vice versa":
    let db = newExampleDB(dbPath)
    db.save("indep", @[integerChoice(1, 0, 100, 0)])
    db.saveCorpus("indep", @[integerChoice(2, 0, 100, 0)])
    check db.loadPrimary("indep").len == 1
    check db.loadCorpus("indep").len == 1

    # Growing / evicting the corpus leaves primary alone.
    for i in 10 ..< 20:
      db.saveCorpus("indep", @[integerChoice(i, 0, 100, 0)], maxEntries = 5)
    check db.loadCorpus("indep").len == 5
    check db.loadPrimary("indep").len == 1
    check db.loadPrimary("indep")[0] == @[integerChoice(1, 0, 100, 0)]

    # Removing from primary leaves corpus alone.
    db.remove("indep", @[integerChoice(1, 0, 100, 0)])
    check db.loadPrimary("indep").len == 0
    check db.loadCorpus("indep").len == 5

  test "corpus save dedups content and caps to maxEntries (most-recent first)":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 20:
      db.saveCorpus("cap", @[integerChoice(i, 0, 100, 0)], maxEntries = 5)
    let all = db.loadCorpus("cap")
    check all.len == 5
    check toInt64(all[0][0].intVal) == 19
    check toInt64(all[4][0].intVal) == 15

    # Re-saving identical content doesn't grow the corpus, just reorders it.
    db.saveCorpus("cap", @[integerChoice(15, 0, 100, 0)], maxEntries = 5)
    check db.loadCorpus("cap").len == 5
    check toInt64(db.loadCorpus("cap")[0][0].intVal) == 15

  test "corpus persists across fresh ExampleDB instances on the same path":
    block:
      let db1 = newExampleDB(dbPath)
      db1.saveCorpus("p", @[integerChoice(1, 0, 100, 0)])
      db1.saveCorpus("p", @[integerChoice(2, 0, 100, 0)])
      db1.save("p", @[integerChoice(3, 0, 100, 0)])          # primary, sanity
    block:
      let db2 = newExampleDB(dbPath)
      let cp = db2.loadCorpus("p")
      check cp.len == 2
      check cp[0] == @[integerChoice(2, 0, 100, 0)]  # most-recent first
      check cp[1] == @[integerChoice(1, 0, 100, 0)]
      check db2.loadPrimary("p").len == 1

  test "a legacy (pre-F1) on-disk DB file with no corpus section loads with an empty corpus":
    # Hand-construct a version-2 file (no corpus section) matching the format
    # documented before F1, and confirm the F1 reader degrades cleanly.
    createDir(dbPath)
    let db = newExampleDB(dbPath)
    db.save("legacy", @[integerChoice(7, 0, 100, 0)])
    let p = dbPath / "legacy.bin"
    var raw = readFile(p)
    # First byte is the version tag; force it down to 2 (pre-corpus) — the
    # remaining bytes (nPrimary/nSecondary/entries) are unaffected by the
    # version bump since the corpus section is strictly appended.
    raw[0] = char(2)
    writeFile(p, raw)
    let reloaded = newExampleDB(dbPath)
    check reloaded.loadPrimary("legacy").len == 1
    check reloaded.loadCorpus("legacy").len == 0

  test "fuzz() persists corpus growth to loadCorpus, never to loadPrimary":
    proc coverageByValue(): Target[int] =
      Target[int](run: proc(x: int): Observation[int] =
        var c = newSeq[byte](8)
        c[(x mod 8 + 8) mod 8] = 1'u8
        Observation[int](verdict: vOk, coverage: Coverage(counters: c)))
    let db = newExampleDB(dbPath)
    var fr = newCoverageFrontier("bin1")
    let fs = FuzzSettings(maxIterations: 300, seed: 1, database: db,
                          persistKey: "camp")
    discard fuzz(integers(0, 1000), coverageByValue(), fr, fs)
    let testId = fuzzCorpusKey("camp", "bin1")
    check db.loadCorpus(testId).len >= 3
    check db.loadPrimary(testId).len == 0

suite "F1: coverage-corpus channel — backend parity":
  test "inMemoryDatabase: corpus round-trips and is independent of primary":
    let db = inMemoryDatabase()
    db.save("t1", @[integerChoice(1, 0, 100, 0)])
    db.saveCorpus("t1", @[integerChoice(2, 0, 100, 0)])
    check db.loadPrimary("t1") == @[@[integerChoice(1, 0, 100, 0)]]
    check db.loadCorpus("t1") == @[@[integerChoice(2, 0, 100, 0)]]

  test "multiplexedDatabase: corpus reads union both; writes go to primary backend only":
    let localDb = inMemoryDatabase()
    let sharedDb = inMemoryDatabase()
    let refCs = @[integerChoice(42, 0, 100, 0)]
    sharedDb.saveCorpus("k", refCs)
    let multiplexed = multiplexedDatabase(localDb, sharedDb)
    check refCs in multiplexed.loadCorpus("k")

    let localCs = @[integerChoice(7, 0, 100, 0)]
    multiplexed.saveCorpus("k", localCs)
    check localCs in localDb.loadCorpus("k")
    check localCs notin sharedDb.loadCorpus("k")

    let combined = multiplexed.loadCorpus("k")
    check refCs in combined
    check localCs in combined

  test "readOnlyDatabase: saveCorpus raises DbError; loadCorpus succeeds":
    let inner = inMemoryDatabase()
    inner.saveCorpus("k", @[integerChoice(1, 0, 100, 0)])
    let ro = readOnlyDatabase(inner)
    check ro.loadCorpus("k").len == 1
    expect DbError:
      ro.saveCorpus("k", @[integerChoice(2, 0, 100, 0)])
