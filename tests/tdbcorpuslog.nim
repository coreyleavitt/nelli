## RFC-fuzzer-nextgen E3b: corpus/frontier persistence discipline via an
## append-only delta log (docs/RFC-fuzzer-nextgen.E0-findings.md is the
## decision record). The directory backend's `corpus` section moves OUT of
## `<key>.bin` into its own per-testId stream `<key>.corpus.log` — split so
## the fuzzer's hot corpus-admit path (single writer: the orchestrator)
## never shares a rewrite target with the shrinker's `.bin` RMW (E0 race
## (a)). `saveCorpus`/`loadCorpus`'s OBSERVABLE contract (tested exhaustively
## by tfuzzcovcorpus.nim/tfuzzpersist.nim/tdb.nim/tdbbackends.nim) is
## unchanged; this suite pins the new on-disk transport itself.

import std/[unittest, os]
import nelli
import nelli/[choice, serialize]

suite "E3b C1: corpus delta log — directory backend transport":
  setup:
    let dbPath = getTempDir() / "nelli_test_corpuslog_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "saveCorpus writes to <key>.corpus.log, not <key>.bin":
    let db = newExampleDB(dbPath)
    db.saveCorpus("k", @[integerChoice(1, 0, 100, 0)])
    check fileExists(dbPath / "k.corpus.log")
    check not fileExists(dbPath / "k.bin")

  test "corpus.log starts with the NLC0 header":
    let db = newExampleDB(dbPath)
    db.saveCorpus("k", @[integerChoice(1, 0, 100, 0)])
    let raw = readFile(dbPath / "k.corpus.log")
    check raw[0 .. 3] == "NLC0"

  test "loadCorpus round-trips through the log, newest first (F5 order preserved)":
    let db = newExampleDB(dbPath)
    let a = @[integerChoice(1, 0, 100, 0)]
    let b = @[integerChoice(2, 0, 100, 0)]
    db.saveCorpus("k", a)
    db.saveCorpus("k", b)
    check db.loadCorpus("k") == @[b, a]

  test "dedup: re-saving an existing entry moves it to the front, no duplicate":
    let db = newExampleDB(dbPath)
    let a = @[integerChoice(1, 0, 100, 0)]
    let b = @[integerChoice(2, 0, 100, 0)]
    db.saveCorpus("k", a)
    db.saveCorpus("k", b)
    db.saveCorpus("k", a)
    check db.loadCorpus("k") == @[a, b]

  test "cap-the-tail: maxEntries evicts oldest, newest-first order preserved (same handle)":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 20:
      db.saveCorpus("cap", @[integerChoice(i, 0, 100, 0)], maxEntries = 5)
    let all = db.loadCorpus("cap")
    check all.len == 5
    check toInt64(all[0][0].intVal) == 19
    check toInt64(all[4][0].intVal) == 15

  test "corpus persists across fresh directory-backend instances (cold replay)":
    block:
      let db1 = newExampleDB(dbPath)
      db1.saveCorpus("p", @[integerChoice(1, 0, 100, 0)])
      db1.saveCorpus("p", @[integerChoice(2, 0, 100, 0)])
    block:
      let db2 = newExampleDB(dbPath)
      let cp = db2.loadCorpus("p")
      check cp.len == 2
      check cp[0] == @[integerChoice(2, 0, 100, 0)]
      check cp[1] == @[integerChoice(1, 0, 100, 0)]

  test "primary save never touches <key>.corpus.log":
    let db = newExampleDB(dbPath)
    db.save("k", @[integerChoice(1, 0, 100, 0)])
    check not fileExists(dbPath / "k.corpus.log")

  test "legacy .bin with an inline corpus section migrates into the log on first corpus access":
    # Hand-construct a pre-E3b v3 .bin (corpus section lived inside .bin
    # then) carrying two corpus entries, and confirm the new backend
    # surfaces them via loadCorpus AND relocates them into the real log
    # instead of losing them.
    createDir(dbPath)
    let legacyEntries = @[
      @[integerChoice(10, 0, 100, 0)],
      @[integerChoice(20, 0, 100, 0)],
    ]
    var raw: seq[byte]
    raw.add byte(3)          # legacy dbFormatVersion (corpus inline, v3)
    raw.putU64(0'u64)        # nPrimary
    raw.putU64(0'u64)        # nSecondary
    raw.putU64(uint64(legacyEntries.len))
    for cs in legacyEntries:
      raw.putRawBytes(toBytes(cs))
    var s = newString(raw.len)
    if raw.len > 0: copyMem(addr s[0], addr raw[0], raw.len)
    writeFile(dbPath / "legacy.bin", s)

    let db = newExampleDB(dbPath)
    let migrated = db.loadCorpus("legacy")
    check migrated.len == 2
    check legacyEntries[0] in migrated
    check legacyEntries[1] in migrated
    check fileExists(dbPath / "legacy.corpus.log")
    # Migration is one-time + idempotent: a fresh handle still sees the
    # (now log-backed) corpus, not a re-duplicated one.
    let reloaded = newExampleDB(dbPath)
    check reloaded.loadCorpus("legacy").len == 2

suite "E3b C2: tombstone-on-evict + size-triggered compaction":
  setup:
    let dbPath = getTempDir() / "nelli_test_corpuslog_c2_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "a cold (different-handle) replay sees the exact same capped set as the writer":
    # Before C2, only the WRITING handle's in-memory cache reflected the
    # cap; a fresh handle replaying the raw log would see every add ever
    # made (evictions weren't recorded). Tombstone-on-evict closes that gap:
    # the log is self-describing regardless of which handle reads it.
    block:
      let writer = newExampleDB(dbPath)
      for i in 0 ..< 20:
        writer.saveCorpus("cap", @[integerChoice(i, 0, 100, 0)], maxEntries = 5)
      # The writer never itself calls loadCorpus here — only a fresh handle does.
    let reader = newExampleDB(dbPath)
    let all = reader.loadCorpus("cap")
    check all.len == 5
    check toInt64(all[0][0].intVal) == 19
    check toInt64(all[4][0].intVal) == 15

  test "size-triggered compaction shrinks the log file when churn exceeds the ratio":
    let db = newExampleDB(dbPath)
    var sizes: seq[int64]
    for i in 0 ..< 30:
      db.saveCorpus("churn", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
      sizes.add getFileSize(dbPath / "churn.corpus.log")
    var compacted = false
    for i in 1 ..< sizes.len:
      if sizes[i] < sizes[i - 1]: compacted = true
    check compacted
    # Content survives compaction, both via the live handle and cold replay.
    check db.loadCorpus("churn").len == 2
    let fresh = newExampleDB(dbPath)
    check fresh.loadCorpus("churn").len == 2

  test "a compacted log's first record is a resetBulk (op byte 2 right after the header)":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 30:
      db.saveCorpus("churn2", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
    let raw = readFile(dbPath / "churn2.corpus.log")
    check raw.len > 13
    check ord(raw[12]) == 2   # header(8) + u32 recLen(4) -> op byte at offset 12
