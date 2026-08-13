## F8 (docs/RFC-chapulin-hardening.md ~line 640): a cheap section-size
## introspection helper for the example DB. `sectionSizes(db, testId)`
## reports the entry count of the `primary` / `secondary` / `corpus`
## sections (`db.nim`'s `loadPrimary`/`loadSecondary`/`loadCorpus`) so a
## caller (CI dashboards, corpus-management tooling) can track corpus
## growth without materializing and hand-counting every entry at the call
## site. Implemented as a thin wrapper over the existing `load*`
## accessors — see the module doc's F8 section in `db.nim` for the
## wrapper-vs-closure design note.

import std/[unittest, os, tables]
import nelli
import nelli/[choice]

suite "F8: sectionSizes — entry-count introspection":
  setup:
    let dbPath = getTempDir() / "nelli_test_sectionsize_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "empty DB reports all sizes zero":
    let db = newExampleDB(dbPath)
    let sizes = db.sectionSizes("nope")
    check sizes.primary == 0
    check sizes.secondary == 0
    check sizes.corpus == 0

  test "in-memory backend: sizes reflect N primary + M secondary + K corpus saves exactly":
    let db = inMemoryDatabase()
    db.save("t", @[integerChoice(1, 0, 100, 0)])
    db.save("t", @[integerChoice(2, 0, 100, 0)])
    db.save("t", @[integerChoice(3, 0, 100, 0)])
    db.saveSecondary("t", @[(choices: @[integerChoice(4, 0, 100, 0)], score: 1.0,
                            scores: initTable[string, float]())])
    db.saveSecondary("t", @[(choices: @[integerChoice(5, 0, 100, 0)], score: 2.0,
                            scores: initTable[string, float]())])
    db.saveCorpus("t", @[integerChoice(6, 0, 100, 0)])
    let sizes = db.sectionSizes("t")
    check sizes.primary == 3
    check sizes.secondary == 2
    check sizes.corpus == 1

  test "directory backend: sizes reflect N primary + M secondary + K corpus saves exactly":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 4:
      db.save("d", @[integerChoice(i, 0, 100, 0)])
    for i in 0 ..< 5:
      db.saveSecondary("d", @[(choices: @[integerChoice(100 + i, 0, 200, 0)],
                              score: float(i), scores: initTable[string, float]())])
    for i in 0 ..< 6:
      db.saveCorpus("d", @[integerChoice(200 + i, 0, 300, 0)])
    let sizes = db.sectionSizes("d")
    check sizes.primary == 4
    check sizes.secondary == 5
    check sizes.corpus == 6

  test "saving a duplicate choice-seq doesn't grow the reported size (dedup)":
    let db = newExampleDB(dbPath)
    let choices = @[integerChoice(9, 0, 100, 0)]
    db.save("dup", choices)
    db.save("dup", choices)
    db.save("dup", choices)
    db.saveCorpus("dup", choices)
    db.saveCorpus("dup", choices)
    check db.sectionSizes("dup").primary == 1
    check db.sectionSizes("dup").corpus == 1

  test "exceeding maxEntries caps the reported size":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 20:
      db.save("cap", @[integerChoice(i, 0, 1000, 0)], maxEntries = 5)
    for i in 0 ..< 20:
      db.saveCorpus("cap", @[integerChoice(1000 + i, 0, 2000, 0)], maxEntries = 7)
    let sizes = db.sectionSizes("cap")
    check sizes.primary == 5
    check sizes.corpus == 7

  test "round-trips through the directory backend: reload reports the same sizes":
    block:
      let db1 = newExampleDB(dbPath)
      db1.save("rt", @[integerChoice(1, 0, 100, 0)])
      db1.save("rt", @[integerChoice(2, 0, 100, 0)])
      db1.saveSecondary("rt", @[(choices: @[integerChoice(3, 0, 100, 0)], score: 1.0,
                                scores: initTable[string, float]())])
      db1.saveCorpus("rt", @[integerChoice(4, 0, 100, 0)])
      db1.saveCorpus("rt", @[integerChoice(5, 0, 100, 0)])
      db1.saveCorpus("rt", @[integerChoice(6, 0, 100, 0)])
      check db1.sectionSizes("rt") == (primary: 2, secondary: 1, corpus: 3)
    block:
      let db2 = newExampleDB(dbPath)
      check db2.sectionSizes("rt") == (primary: 2, secondary: 1, corpus: 3)

  test "sections are independently sized per test id":
    let db = newExampleDB(dbPath)
    db.save("a", @[integerChoice(1, 0, 100, 0)])
    db.saveCorpus("b", @[integerChoice(2, 0, 100, 0)])
    check db.sectionSizes("a") == (primary: 1, secondary: 0, corpus: 0)
    check db.sectionSizes("b") == (primary: 0, secondary: 0, corpus: 1)
