## F6 (docs/RFC-chapulin-hardening.md ~line 636): per-primary-entry metadata
## slot (`db.nim`'s on-disk layout + `save`/`loadPrimary`).
##
## The `secondary` section already carries a per-entry `Table[string, float]`
## label table. `primary` (regression witnesses) had none — F6 adds an
## analogous opaque `Table[string, string]` slot per primary entry so a
## caller can attach descriptive tags (a crash message, an origin/verdict
## label, ...) to a stored choice-seq without a side channel keyed on the
## choice bytes. `save(db, testId, choices)` is unchanged (defaults an
## entry's metadata to empty); `save(db, testId, choices, meta)` attaches or
## overwrites it; `loadPrimary` is unchanged (choices only);
## `loadPrimaryWithMeta` returns choices paired with metadata. This suite
## pins the round-trip, the unchanged default behavior, the v3->v4 backward
## compatibility, dedup/prepend/cap with metadata attached, and that
## `secondary`/`corpus` are untouched.

import std/[unittest, os, tables]
import nelli
import nelli/[choice, serialize]

suite "F6: per-primary-entry metadata — round-trip":
  setup:
    let dbPath = getTempDir() / "nelli_test_primarymeta_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "save with metadata round-trips via loadPrimaryWithMeta (directory backend)":
    let db = newExampleDB(dbPath)
    let choices = @[integerChoice(5, 0, 100, 0)]
    let meta = {"origin": "fuzz", "crash": "IndexError"}.toTable
    db.save("t1", choices, meta)
    let entries = db.loadPrimaryWithMeta("t1")
    check entries.len == 1
    check entries[0].choices == choices
    check entries[0].meta == meta

  test "save with metadata round-trips via loadPrimaryWithMeta (in-memory backend)":
    let db = inMemoryDatabase()
    let choices = @[integerChoice(9, 0, 100, 0)]
    let meta = {"tag": "seed-a"}.toTable
    db.save("t1", choices, meta)
    let entries = db.loadPrimaryWithMeta("t1")
    check entries.len == 1
    check entries[0].choices == choices
    check entries[0].meta == meta

  test "metadata survives a reload from a fresh ExampleDB on the same path":
    let choices = @[integerChoice(3, 0, 50, 0)]
    let meta = {"k": "v"}.toTable
    newExampleDB(dbPath).save("t1", choices, meta)
    let reloaded = newExampleDB(dbPath).loadPrimaryWithMeta("t1")
    check reloaded.len == 1
    check reloaded[0].meta == meta

suite "F6: per-primary-entry metadata — existing API unaffected":
  setup:
    let dbPath = getTempDir() / "nelli_test_primarymeta_db2"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "plain save() (no meta) reads back empty metadata":
    let db = newExampleDB(dbPath)
    let choices = @[integerChoice(1, 0, 100, 0)]
    db.save("t1", choices)
    let entries = db.loadPrimaryWithMeta("t1")
    check entries.len == 1
    check entries[0].meta.len == 0

  test "loadPrimary behavior is unchanged regardless of attached metadata":
    let db = newExampleDB(dbPath)
    let c1 = @[integerChoice(1, 0, 100, 0)]
    let c2 = @[integerChoice(2, 0, 100, 0)]
    db.save("t1", c1)
    db.save("t1", c2, {"tag": "x"}.toTable)
    let loaded = db.loadPrimary("t1")
    check loaded.len == 2
    check loaded[0] == c2   # most-recent first (F5 order contract)
    check loaded[1] == c1

  test "in-memory backend: plain save() reads back empty metadata too":
    let db = inMemoryDatabase()
    let choices = @[integerChoice(1, 0, 100, 0)]
    db.save("t1", choices)
    check db.loadPrimaryWithMeta("t1")[0].meta.len == 0

suite "F6: per-primary-entry metadata — backward compatibility (v3 -> v4)":
  setup:
    let dbPath = getTempDir() / "nelli_test_primarymeta_db3"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "a v3 on-disk file (no per-entry metadata) loads to empty metadata":
    # Hand-construct a version-3 file matching the pre-F6 format exactly:
    # [ver=3][nPrimary][nSecondary][primary: size+bytes][secondary...][nCorpus].
    createDir(dbPath)
    let choices = @[integerChoice(7, 0, 100, 0)]
    var raw: seq[byte]
    raw.putU8(3'u8)
    raw.putU64(1'u64)   # nPrimary
    raw.putU64(0'u64)   # nSecondary
    raw.putRawBytes(toBytes(choices))
    raw.putU64(0'u64)   # nCorpus
    let p = dbPath / "legacy.bin"
    writeFile(p, block:
      var s = newString(raw.len)
      if raw.len > 0: copyMem(addr s[0], unsafeAddr raw[0], raw.len)
      s)

    let db = newExampleDB(dbPath)
    let entries = db.loadPrimaryWithMeta("legacy")
    check entries.len == 1
    check entries[0].choices == choices
    check entries[0].meta.len == 0
    check db.loadPrimary("legacy") == @[choices]

  test "a v3 file is transparently upgraded to v4 (with metadata) on next write":
    createDir(dbPath)
    let choices = @[integerChoice(7, 0, 100, 0)]
    var raw: seq[byte]
    raw.putU8(3'u8)
    raw.putU64(1'u64)
    raw.putU64(0'u64)
    raw.putRawBytes(toBytes(choices))
    raw.putU64(0'u64)
    let p = dbPath / "legacy.bin"
    writeFile(p, block:
      var s = newString(raw.len)
      if raw.len > 0: copyMem(addr s[0], unsafeAddr raw[0], raw.len)
      s)

    let db = newExampleDB(dbPath)
    let meta = {"upgraded": "yes"}.toTable
    db.save("legacy", choices, meta)   # re-save with metadata -> re-encodes at v4

    let raw2 = readFile(p)
    check raw2[0] == char(4)   # dbFormatVersion bumped on write
    let reloaded = newExampleDB(dbPath).loadPrimaryWithMeta("legacy")
    check reloaded.len == 1
    check reloaded[0].meta == meta

suite "F6: per-primary-entry metadata — dedup/prepend/cap":
  setup:
    let dbPath = getTempDir() / "nelli_test_primarymeta_db4"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "re-saving an equal choice-seq with plain save() carries existing metadata forward":
    let db = newExampleDB(dbPath)
    let choices = @[integerChoice(4, 0, 100, 0)]
    let meta = {"sticky": "1"}.toTable
    db.save("t1", choices, meta)
    db.save("t1", choices)   # plain re-save, no meta arg
    let entries = db.loadPrimaryWithMeta("t1")
    check entries.len == 1   # still deduped to one entry
    check entries[0].meta == meta   # metadata was NOT clobbered

  test "re-saving an equal choice-seq with explicit meta overwrites it":
    let db = newExampleDB(dbPath)
    let choices = @[integerChoice(4, 0, 100, 0)]
    db.save("t1", choices, {"v": "1"}.toTable)
    db.save("t1", choices, {"v": "2"}.toTable)
    let entries = db.loadPrimaryWithMeta("t1")
    check entries.len == 1
    check entries[0].meta == {"v": "2"}.toTable

  test "dedup + prepend still orders most-recent-first with metadata attached":
    let db = newExampleDB(dbPath)
    let c1 = @[integerChoice(1, 0, 100, 0)]
    let c2 = @[integerChoice(2, 0, 100, 0)]
    db.save("t1", c1, {"a": "1"}.toTable)
    db.save("t1", c2, {"b": "2"}.toTable)
    let entries = db.loadPrimaryWithMeta("t1")
    check entries.len == 2
    check entries[0].choices == c2
    check entries[0].meta == {"b": "2"}.toTable
    check entries[1].choices == c1
    check entries[1].meta == {"a": "1"}.toTable

  test "cap evicts the oldest entry (with its metadata) first":
    let db = newExampleDB(dbPath)
    let c1 = @[integerChoice(1, 0, 100, 0)]
    let c2 = @[integerChoice(2, 0, 100, 0)]
    let c3 = @[integerChoice(3, 0, 100, 0)]
    db.save("t1", c1, {"a": "1"}.toTable, maxEntries = 2)
    db.save("t1", c2, {"b": "2"}.toTable, maxEntries = 2)
    db.save("t1", c3, {"c": "3"}.toTable, maxEntries = 2)
    let entries = db.loadPrimaryWithMeta("t1")
    check entries.len == 2
    check entries[0].choices == c3
    check entries[1].choices == c2   # c1 (oldest) evicted

suite "F6: per-primary-entry metadata — secondary/corpus unaffected":
  setup:
    let dbPath = getTempDir() / "nelli_test_primarymeta_db5"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "attaching primary metadata does not disturb secondary or corpus sections":
    let db = newExampleDB(dbPath)
    let pChoices = @[integerChoice(1, 0, 100, 0)]
    let sChoices = @[integerChoice(2, 0, 100, 0)]
    let cChoices = @[integerChoice(3, 0, 100, 0)]
    db.save("t1", pChoices, {"tag": "meta"}.toTable)
    db.saveSecondary("t1", [(choices: sChoices, score: 1.0,
                             scores: initTable[string, float]())])
    db.saveCorpus("t1", cChoices)

    check db.loadPrimaryWithMeta("t1").len == 1
    check db.loadSecondary("t1").len == 1
    check db.loadSecondary("t1")[0].choices == sChoices
    check db.loadCorpus("t1") == @[cChoices]

    # Reload from disk to make sure section boundaries survived the extra
    # per-primary-entry metadata bytes.
    let reloaded = newExampleDB(dbPath)
    check reloaded.loadPrimaryWithMeta("t1").len == 1
    check reloaded.loadPrimaryWithMeta("t1")[0].meta == {"tag": "meta"}.toTable
    check reloaded.loadSecondary("t1").len == 1
    check reloaded.loadSecondary("t1")[0].choices == sChoices
    check reloaded.loadCorpus("t1") == @[cChoices]

  test "multiplexedDatabase: metadata round-trips through the primary backend":
    let localDb = inMemoryDatabase()
    let sharedDb = inMemoryDatabase()
    let mux = multiplexedDatabase(localDb, sharedDb)
    let choices = @[integerChoice(1, 0, 100, 0)]
    mux.save("t1", choices, {"origin": "local"}.toTable)
    check mux.loadPrimaryWithMeta("t1").len == 1
    check mux.loadPrimaryWithMeta("t1")[0].meta == {"origin": "local"}.toTable
    check localDb.loadPrimaryWithMeta("t1")[0].meta == {"origin": "local"}.toTable
    check sharedDb.loadPrimaryWithMeta("t1").len == 0

  test "readOnlyDatabase: loadPrimaryWithMeta reads through; saving with meta raises":
    let inner = inMemoryDatabase()
    inner.save("t1", @[integerChoice(1, 0, 100, 0)], {"k": "v"}.toTable)
    let ro = readOnlyDatabase(inner)
    check ro.loadPrimaryWithMeta("t1").len == 1
    check ro.loadPrimaryWithMeta("t1")[0].meta == {"k": "v"}.toTable
    expect DbError:
      ro.save("t1", @[integerChoice(2, 0, 100, 0)], {"k": "v2"}.toTable)
