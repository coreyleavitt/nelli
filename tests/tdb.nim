import std/[unittest, os]
import proptest

suite "ExampleDB":
  setup:
    let dbPath = getTempDir() / "proptest_test_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "saves and loads a choice sequence keyed by test id":
    let db = newExampleDB(dbPath)
    let original = @[
      integerChoice(42, 0, 100, 0),
      booleanChoice(true, 0.5),
      integerChoice(7, 0, 10, 0),
    ]
    db.save("my-test", original)
    let loaded = db.load("my-test")
    check loaded == original

  test "load returns empty for an unknown test id":
    let db = newExampleDB(dbPath)
    check db.load("never-saved").len == 0

  test "forAll persists a failure and replays it on the next run":
    proc prop(x: int) = ensure x < 50
    let s = Settings(maxExamples: 100, maxRejections: 1000, seed: 42,
                     testId: "demo-prop", dbPath: dbPath)

    let r1 = forAll(integers(0, 100), prop, s)
    check r1.outcome == otFalsified
    check r1.counterexample == 50            # found + shrunk

    let r2 = forAll(integers(0, 100), prop, s)
    check r2.outcome == otFalsified
    check r2.counterexample == 50            # replayed from DB
    check r2.examples == 0                   # no random generation needed
