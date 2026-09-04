## RFC-fuzzer-nextgen U2: `forAll`/`given` gain a replay-only pass over the
## persisted fuzz `corpus` section (`db.nim`'s `saveCorpus`/`loadCorpus`,
## E3b's delta-log-backed section `fuzz.nim`'s coverage-guided campaigns
## accumulate), ahead of the random phase — "two front doors, one engine":
## `forAll` benefits from coverage seeds `fuzz` already found, at zero
## determinism cost, without ever mutating the corpus (admission stays
## exclusively `fuzz`'s job).

import std/[unittest, os]
import nelli
import nelli/[choice]
import zerofill  # RFC-0010 A1 pin; removed by A3

suite "engine: forAll corpus replay (RFC-fuzzer-nextgen U2)":
  setup:
    let dbPath = getTempDir() / "nelli_test_u2corpusreplay_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "a falsifying corpus entry is found deterministically before the random phase, shrunk to minimal":
    let db = newExampleDB(dbPath)
    db.saveCorpus("u2corpus1", @[integerChoice(87, 0, 100, 0)])

    proc prop(x: int) = ensure x < 50
    # maxExamples: 0 — the random phase contributes NOTHING; any
    # falsification must have come from the corpus-replay phase alone.
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 0, maxRejections: 100, seed: 1,
                                       testId: "u2corpus1", dbPath: dbPath)))
    check r.outcome == otFalsified
    check r.examples == 0                # random phase never ran
    check r.counterexample.get == 50     # shrunk to the minimal x<50 violator

  test "a passing corpus entry doesn't block the random phase from finding its own falsification":
    let db = newExampleDB(dbPath)
    db.saveCorpus("u2corpus2", @[integerChoice(5, 0, 100, 0)])  # x=5 passes x<50

    proc prop(x: int) = ensure x < 50
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 200, maxRejections: 1000, seed: 42,
                                       testId: "u2corpus2", dbPath: dbPath)))
    check r.outcome == otFalsified
    check r.counterexample.get == 50

  test "determinism: corpus entries replay in a fixed (most-recent-first) order, identical across runs":
    let db = newExampleDB(dbPath)
    for v in [11, 22, 33]:
      db.saveCorpus("u2order", @[integerChoice(v, 0, 100, 0)])

    proc runOnce(): tuple[seen: seq[int], r: Report[int]] =
      var seen: seq[int]
      proc prop(x: int) =
        seen.add x
        ensure x < 1000   # never falsifies: corpus + random phase both run to completion
      let s = zeroFilled(Settings(maxExamples: 5, maxRejections: 100, seed: 99,
                                  testId: "u2order", dbPath: dbPath))
      let rep = forAll(integers(0, 100), prop, s)
      (seen: seen, r: rep)

    let run1 = runOnce()
    let run2 = runOnce()
    check run1.seen == run2.seen
    # 3 corpus replays + 5 random examples, corpus replayed most-recent-first
    # (matching `loadCorpus`'s own documented order).
    check run1.seen.len == 8
    check run1.seen[0 .. 2] == @[33, 22, 11]
    check run1.r.outcome == run2.r.outcome
    check run1.r.examples == run2.r.examples

  test "read-only: a forAll run never mutates the corpus, even when a corpus seed falsifies and is shrunk":
    let db = newExampleDB(dbPath)
    db.saveCorpus("u2readonly", @[integerChoice(87, 0, 100, 0)])
    let before = sectionSizes(db, "u2readonly")

    proc prop(x: int) = ensure x < 50
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 10, maxRejections: 100, seed: 3,
                                       testId: "u2readonly", dbPath: dbPath)))
    check r.outcome == otFalsified

    let after = sectionSizes(newExampleDB(dbPath), "u2readonly")
    check after.corpus == before.corpus
    check after.corpus == 1
    check newExampleDB(dbPath).loadCorpus("u2readonly") ==
      @[@[integerChoice(87, 0, 100, 0)]]

  test "no database configured: forAll is unaffected by U2 (no corpus read, same outcome as pre-U2)":
    proc prop(x: int) = ensure x < 50
    let r = forAll(integers(0, 100), prop, zeroFilled(Settings(maxExamples: 200, seed: 42)))
    check r.outcome == otFalsified
    check r.counterexample.get == 50

  test "database configured but no corpus entries: forAll is unaffected (same outcome as dbReuse-only)":
    let db = newExampleDB(dbPath)
    db.save("u2nocorpus", @[integerChoice(80, 0, 100, 0)])  # primary regression witness only

    proc prop(x: int) = ensure x < 50
    let r = forAll(integers(0, 100), prop,
                   zeroFilled(Settings(maxExamples: 100, maxRejections: 1000, seed: 7,
                                       testId: "u2nocorpus", dbPath: dbPath)))
    check r.outcome == otFalsified
    check r.counterexample.get == 50
    check r.examples == 0   # found via primary DB reuse, no random gen needed
