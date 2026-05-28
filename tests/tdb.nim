import std/[unittest, os, tables, strutils]
import proptest
import proptest/[int128, choice, serialize, rng, datasource, shrinker]

suite "ExampleDB":
  setup:
    let dbPath = getTempDir() / "proptest_test_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "save two distinct sequences; loadPrimary returns both, most-recent first":
    let db = newExampleDB(dbPath)
    let seqA = @[integerChoice(1, 0, 100, 0)]
    let seqB = @[integerChoice(2, 0, 100, 0), booleanChoice(true, 0.5)]
    db.save("k", seqA)
    db.save("k", seqB)
    let all = db.loadPrimary("k")
    check all.len == 2
    check all[0] == seqB   # most-recent first
    check all[1] == seqA

  test "saves and loads a single choice sequence keyed by test id":
    let db = newExampleDB(dbPath)
    let original = @[
      integerChoice(42, 0, 100, 0),
      booleanChoice(true, 0.5),
      integerChoice(7, 0, 10, 0),
    ]
    db.save("my-test", original)
    let loaded = db.loadPrimary("my-test")
    check loaded == @[original]

  test "loadPrimary returns empty for an unknown test id":
    let db = newExampleDB(dbPath)
    check db.loadPrimary("never-saved").len == 0

  test "save dedups identical content (saving twice keeps one entry)":
    let db = newExampleDB(dbPath)
    let same = @[integerChoice(1, 0, 100, 0)]
    db.save("k", same)
    db.save("k", same)
    let all = db.loadPrimary("k")
    check all.len == 1
    check all[0] == same

  test "save bounds the corpus to maxEntries (oldest evicted)":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 20:
      db.save("k", @[integerChoice(i, 0, 100, 0)], maxEntries = 5)
    let all = db.loadPrimary("k")
    check all.len == 5
    # Most-recent first: indices 19, 18, 17, 16, 15.
    check toInt64(all[0][0].intVal) == 19
    check toInt64(all[4][0].intVal) == 15

  test "remove drops a specific stored entry":
    let db = newExampleDB(dbPath)
    db.save("k", @[integerChoice(1, 0, 100, 0)])
    db.save("k", @[integerChoice(2, 0, 100, 0)])
    db.save("k", @[integerChoice(3, 0, 100, 0)])
    db.remove("k", @[integerChoice(2, 0, 100, 0)])
    let all = db.loadPrimary("k")
    check all.len == 2
    check all[0] == @[integerChoice(3, 0, 100, 0)]
    check all[1] == @[integerChoice(1, 0, 100, 0)]

  test "engine auto-prunes a stored entry that no longer falsifies":
    let db = newExampleDB(dbPath)
    # Pre-save a sequence yielding x=5 — won't falsify `ensure x >= 0`.
    db.save("auto-prune", @[integerChoice(5, 0, 100, 0)])
    check db.loadPrimary("auto-prune").len == 1

    proc passing(x: int) = ensure x >= 0
    let s = Settings(maxExamples: 10, maxRejections: 100, seed: 1,
                     testId: "auto-prune", dbPath: dbPath)
    let r = forAll(integers(0, 100), passing, s)
    check r.outcome == otPassed
    check newExampleDB(dbPath).loadPrimary("auto-prune").len == 0

  test "engine tries multiple stored entries until one still falsifies":
    let db = newExampleDB(dbPath)
    db.save("multi", @[integerChoice(80, 0, 100, 0)])  # would falsify x<50
    db.save("multi", @[integerChoice(5,  0, 100, 0)])  # would not falsify
    # loadPrimary order: [x=5 (most-recent), x=80].

    proc prop(x: int) = ensure x < 50
    let s = Settings(maxExamples: 1, maxRejections: 100, seed: 1,
                     testId: "multi", dbPath: dbPath)
    let r = forAll(integers(0, 100), prop, s)
    check r.outcome == otFalsified
    check r.counterexample.get == 50   # re-shrunk from 80 to the minimal x<50 violator
    check r.examples == 0          # found via DB, no random gen

  test "Report.dbReplays surfaces DB-reuse activity":
    # Sold feature: DB replays known failures on subsequent runs. The
    # consumer (issue #82) couldn't tell whether persistence was working —
    # `Report.dbReplays` makes it visible.
    proc visProp(x: int) = ensure x < 50
    let visS = Settings(maxExamples: 50, maxRejections: 1000, seed: 42,
                        testId: "db-vis", dbPath: dbPath)
    let visR1 = forAll(integers(0, 100), visProp, visS)
    check visR1.outcome == otFalsified
    check visR1.dbReplays == 0           # empty DB on first run
    let visR2 = forAll(integers(0, 100), visProp, visS)
    check visR2.outcome == otFalsified
    check visR2.dbReplays >= 1           # stored failure replayed
    check "db_replays=" in repro(visR2)

  test "forAll persists a failure and replays it on the next run":
    proc prop(x: int) = ensure x < 50
    let s = Settings(maxExamples: 100, maxRejections: 1000, seed: 42,
                     testId: "demo-prop", dbPath: dbPath)

    let r1 = forAll(integers(0, 100), prop, s)
    check r1.outcome == otFalsified
    check r1.counterexample.get == 50            # found + shrunk

    let r2 = forAll(integers(0, 100), prop, s)
    check r2.outcome == otFalsified
    check r2.counterexample.get == 50            # replayed from DB
    check r2.examples == 0                   # no random generation needed

  test "secondary corpus saves a batch and loads it (highest-score first)":
    let db = newExampleDB(dbPath)
    let a = @[integerChoice(1, 0, 100, 0)]
    let b = @[integerChoice(2, 0, 100, 0)]
    var noLabels: Table[string, float]
    db.saveSecondary("k", @[(choices: a, score: 10.0, scores: noLabels),
                            (choices: b, score: 20.0, scores: noLabels)])
    let all = db.loadSecondary("k")
    check all.len == 2
    check all[0].choices == b
    check all[0].score == 20.0
    check all[1].choices == a
    check all[1].score == 10.0

  test "distinct testIds don't collide on disk":
    # Previously `safeKey` replaced any non-`[A-Za-z0-9._-]` char with `_`,
    # so `"a/b"` and `"a_b"` produced the same filename — cross-test DB
    # contamination. The fix is hex-escape: distinct testIds → distinct
    # filenames.
    let db = newExampleDB(dbPath)
    db.save("a/b", @[integerChoice(1, 0, 100, 0)])
    db.save("a_b", @[integerChoice(2, 0, 100, 0)])
    check db.loadPrimary("a/b") == @[@[integerChoice(1, 0, 100, 0)]]
    check db.loadPrimary("a_b") == @[@[integerChoice(2, 0, 100, 0)]]

  test "truncated DB file is rejected (raises DbError, no IndexDefect)":
    let db = newExampleDB(dbPath)
    db.save("k", @[integerChoice(1, 0, 100, 0)])
    let p = dbPath / "k.bin"
    # Truncate the file mid-record (keep just the version byte + a few bytes).
    let raw = readFile(p)
    writeFile(p, raw[0 ..< 3])  # 3 bytes is far less than even the header
    expect DbError:
      discard db.loadPrimary("k")

  test "DB file with hostile huge length field is rejected (raises DbError)":
    let db = newExampleDB(dbPath)
    createDir(dbPath)
    # Build a header that claims a primary count of 2^64 - 1.
    var raw = newString(17)
    raw[0] = char(2)  # version
    for i in 1 .. 8: raw[i] = char(0xFF)    # nPrimary = u64 max
    for i in 9 .. 16: raw[i] = char(0)      # nSecondary = 0
    let p = dbPath / "k.bin"
    writeFile(p, raw)
    # Corruption raises DbError now — the engine catches and surfaces
    # it via `Report.dbErrors` (or fatally with `Settings.strictDb`).
    expect DbError:
      discard db.loadPrimary("k")

  test "secondary corpus: duplicate choices within one batch keep the LAST entry":
    # Matches the doc: 'add or update' semantics. Pass the same `choices`
    # twice with different scores in one batch; the later score wins.
    let db = newExampleDB(dbPath)
    let cs = @[integerChoice(1, 0, 100, 0)]
    var noLabels: Table[string, float]
    db.saveSecondary("k", @[
      (choices: cs, score: 5.0,  scores: noLabels),
      (choices: cs, score: 99.0, scores: noLabels),
    ])
    let all = db.loadSecondary("k")
    check all.len == 1
    check all[0].score == 99.0  # last entry wins, not first

  test "secondary corpus persists multi-label score maps (v2 round-trip)":
    let db = newExampleDB(dbPath)
    let cs = @[integerChoice(1, 0, 100, 0)]
    var scores: Table[string, float]
    scores["lo"] = -7.0
    scores["hi"] = 42.5
    db.saveSecondary("k", @[(choices: cs, score: 42.5, scores: scores)])
    let all = db.loadSecondary("k")
    check all.len == 1
    check all[0].choices == cs
    check all[0].scores["lo"] == -7.0
    check all[0].scores["hi"] == 42.5
    # Summary `score` is preserved for legacy single-objective consumers.
    check all[0].score == 42.5

  test "secondary corpus bounds to top-N by score":
    let db = newExampleDB(dbPath)
    var noLabels: Table[string, float]
    var batch: seq[ScoredEntry]
    for i in 0 ..< 20:
      batch.add (choices: @[integerChoice(i, 0, 100, 0)],
                 score: float(i), scores: noLabels)
    db.saveSecondary("k", batch, maxEntries = 5)
    let all = db.loadSecondary("k")
    check all.len == 5
    check all[0].score == 19.0
    check all[4].score == 15.0

  test "engine saves best targeted score to secondary corpus on no falsification":
    proc prop(x: int) =
      target(float(x))
      ensure x <= 1000  # always holds for integers(0, 1000)
    let s = Settings(maxExamples: 30, maxRejections: 1000, seed: 1,
                     testId: "tgt-write", dbPath: dbPath)
    let r = forAll(integers(0, 1000), prop, s)
    check r.outcome == otPassed
    let secondary = newExampleDB(dbPath).loadSecondary("tgt-write")
    check secondary.len >= 1
    check secondary[0].score > 0.0

  test "engine seeds hill-climb from secondary corpus when random pool is empty":
    let db = newExampleDB(dbPath)
    let tid = "seed-only"
    # Seeded near the boundary: sum=1980, just below ensure t.0+t.1<=1995.
    var noLabels: Table[string, float]
    db.saveSecondary(tid, @[(
      choices: @[integerChoice(990, 0, 1000, 0),
                 integerChoice(990, 0, 1000, 0)],
      score: 1980.0, scores: noLabels)])

    proc prop(t: (int, int)) =
      target(float(t[0] + t[1]))
      ensure t[0] + t[1] <= 1995

    # maxExamples = 0 → no random generation. The only way to find a
    # falsification is for hill-climb to seed from the secondary corpus.
    let s = Settings(maxExamples: 0, maxRejections: 100, seed: 1,
                     testId: tid, dbPath: dbPath)
    let r = forAll(tuples2(integers(0, 1000), integers(0, 1000)), prop, s)
    check r.outcome == otFalsified
    check r.counterexample.get[0] + r.counterexample.get[1] > 1995

  test "data persists across fresh ExampleDB instances on the same path":
    block:
      let db1 = newExampleDB(dbPath)
      db1.save("p", @[integerChoice(1, 0, 100, 0)])
      db1.save("p", @[integerChoice(2, 0, 100, 0)])
      var noLabels: Table[string, float]
      db1.saveSecondary("p", @[(choices: @[integerChoice(3, 0, 100, 0)],
                                score: 50.0, scores: noLabels)])
    block:
      let db2 = newExampleDB(dbPath)
      let prim = db2.loadPrimary("p")
      let sec = db2.loadSecondary("p")
      check prim.len == 2
      check prim[0] == @[integerChoice(2, 0, 100, 0)]  # most-recent first
      check prim[1] == @[integerChoice(1, 0, 100, 0)]
      check sec.len == 1
      check sec[0].score == 50.0
