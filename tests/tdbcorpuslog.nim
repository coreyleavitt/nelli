## RFC-fuzzer-nextgen E3b: corpus/frontier persistence discipline via an
## append-only delta log (docs/RFC-fuzzer-nextgen.E0-findings.md is the
## decision record). The directory backend's `corpus` section moves OUT of
## `<key>.bin` into its own per-testId, per-generation stream
## `<key>.corpus.<gen>.log` — split so the fuzzer's hot corpus-admit path
## (single writer: the orchestrator) never shares a rewrite target with the
## shrinker's `.bin` RMW (E0 race (a)). `saveCorpus`/`loadCorpus`'s
## OBSERVABLE contract (tested exhaustively by
## tfuzzcovcorpus.nim/tfuzzpersist.nim/tdb.nim/tdbbackends.nim) is
## unchanged; this suite pins the new on-disk transport itself. `gen` is
## implicitly 1 until the first compaction publishes a `<key>.corpus.head`
## pointer to a later generation (E3b C3).

import std/[unittest, os, strutils]
import nelli
import nelli/[choice, serialize]

suite "E3b C1: corpus delta log — directory backend transport":
  setup:
    let dbPath = getTempDir() / "nelli_test_corpuslog_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "saveCorpus writes to <key>.corpus.1.log, not <key>.bin":
    let db = newExampleDB(dbPath)
    db.saveCorpus("k", @[integerChoice(1, 0, 100, 0)])
    check fileExists(dbPath / "k.corpus.1.log")
    check not fileExists(dbPath / "k.bin")

  test "corpus.<gen>.log starts with the NLC0 header":
    let db = newExampleDB(dbPath)
    db.saveCorpus("k", @[integerChoice(1, 0, 100, 0)])
    let raw = readFile(dbPath / "k.corpus.1.log")
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

  test "primary save never touches <key>.corpus.1.log":
    let db = newExampleDB(dbPath)
    db.save("k", @[integerChoice(1, 0, 100, 0)])
    check not fileExists(dbPath / "k.corpus.1.log")

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
    check fileExists(dbPath / "legacy.corpus.1.log")
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

  test "size-triggered compaction publishes a later, smaller generation when churn exceeds the ratio":
    let db = newExampleDB(dbPath)
    var gens: seq[int]
    for i in 0 ..< 30:
      db.saveCorpus("churn", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
      gens.add openCorpusSnapshot(dbPath, "churn").cutPoint.generation
    check gens[^1] > 1   # at least one compaction bumped the generation
    # The newly-published generation starts as a bare resetBulk — smaller
    # than the generation it superseded right before the bump.
    var sawSmallerGenAfterBump = false
    for i in 1 ..< gens.len:
      if gens[i] > gens[i - 1]:
        let prevSize = getFileSize(dbPath / ("churn.corpus." & $gens[i - 1] & ".log"))
        let newSize = getFileSize(dbPath / ("churn.corpus." & $gens[i] & ".log"))
        if newSize < prevSize: sawSmallerGenAfterBump = true
    check sawSmallerGenAfterBump
    # Content survives compaction, both via the live handle and cold replay.
    check db.loadCorpus("churn").len == 2
    let fresh = newExampleDB(dbPath)
    check fresh.loadCorpus("churn").len == 2

  test "a compacted generation's first record is a resetBulk (op byte 2 right after the header)":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 30:
      db.saveCorpus("churn2", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
    let gen = openCorpusSnapshot(dbPath, "churn2").cutPoint.generation
    check gen > 1
    let raw = readFile(dbPath / ("churn2.corpus." & $gen & ".log"))
    check raw.len > 13
    check ord(raw[12]) == 2   # header(8) + u32 recLen(4) -> op byte at offset 12

suite "E3b C3: generation files + head pointer + reader snapshot cut point":
  setup:
    let dbPath = getTempDir() / "nelli_test_corpuslog_c3_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "openCorpusSnapshot resolves the implicit generation 1 before any compaction":
    let db = newExampleDB(dbPath)
    db.saveCorpus("k", @[integerChoice(1, 0, 100, 0)])
    let snap = openCorpusSnapshot(dbPath, "k")
    check snap.cutPoint.generation == 1
    check snap.cutPoint.offset == int64(getFileSize(dbPath / "k.corpus.1.log"))
    check snap.entries == @[@[integerChoice(1, 0, 100, 0)]]

  test "no <key>.corpus.head is written before the first compaction":
    let db = newExampleDB(dbPath)
    db.saveCorpus("k", @[integerChoice(1, 0, 100, 0)])
    check not fileExists(dbPath / "k.corpus.head")

  test "after compaction, <key>.corpus.head names the new generation and a fresh snapshot sees it":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 30:
      db.saveCorpus("k", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
    check fileExists(dbPath / "k.corpus.head")
    let snap = openCorpusSnapshot(dbPath, "k")
    check snap.cutPoint.generation > 1
    check fileExists(dbPath / ("k.corpus." & $snap.cutPoint.generation & ".log"))

  test "POSIX reader-safety: an fd opened on a superseded generation is unaffected by later publishes":
    # E0-findings item 3's actual gating claim: a reader's open handle on a
    # generation the compactor has since superseded keeps reading exactly
    # what it always did — compaction publishes a NEW generation + head, it
    # never mutates or unlinks an already-superseded one. (Generation 1 is
    # still the ACTIVE write target until the first compaction actually
    # fires — churn drives it there first, so "superseded" is unambiguous.)
    let db = newExampleDB(dbPath)
    for i in 0 ..< 3:
      db.saveCorpus("posix", @[integerChoice(i, 0, 100, 0)], maxEntries = 10)
    var i = 3
    while openCorpusSnapshot(dbPath, "posix").cutPoint.generation == 1 and i < 500:
      db.saveCorpus("posix", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
      inc i
    check openCorpusSnapshot(dbPath, "posix").cutPoint.generation > 1   # gen 1 is now superseded

    # Open a persistent OS handle on the now-frozen generation 1 file, and
    # read it once to capture the "before" bytes.
    let gen1Path = dbPath / "posix.corpus.1.log"
    var f: File
    check open(f, gen1Path, fmRead)
    let before = f.readAll()
    check before.len > 0

    # Drive further churn — entirely on generation 2+ now — forcing at
    # least one more compaction on top of the already-superseded gen 1.
    for j in 0 ..< 30:
      db.saveCorpus("posix", @[integerChoice(1000 + j, 0, 100000, 0)], maxEntries = 2)
    check openCorpusSnapshot(dbPath, "posix").cutPoint.generation > 1

    # The already-open fd on generation 1 reads identical bytes to what it
    # read right after it was superseded: that file was never mutated or
    # unlinked out from under it by any later publish.
    f.setFilePos(0)
    let after = f.readAll()
    f.close()
    check after == before
    check getFileSize(gen1Path) == before.len

suite "E3b C5: corpus log versioned-header rule":
  setup:
    let dbPath = getTempDir() / "nelli_test_corpuslog_c5_db"
    removeDir(dbPath)
    createDir(dbPath)
  teardown:
    removeDir(dbPath)

  proc writeRawCorpusLog(dbPath, testId: string, magic: string, formatVersion: uint16,
                         records: seq[byte]) =
    var raw: seq[byte]
    for c in magic: raw.add byte(c)
    raw.putU16(formatVersion)
    raw.putU16(0'u16)   # flags
    raw.add records
    var s = newString(raw.len)
    if raw.len > 0: copyMem(addr s[0], addr raw[0], raw.len)
    writeFile(dbPath / (testId & ".corpus.1.log"), s)   # gen 1 is implicit pre-compaction

  proc addCorpusRecordBytes(choices: seq[ChoiceNode]): seq[byte] =
    let payload = toBytes(choices)
    result.putU32(uint32(1 + payload.len))
    result.add byte(0)   # opAddCorpus
    result.add payload

  test "a corpus log newer than this build refuses with both versions named":
    writeRawCorpusLog(dbPath, "newver", "NLC0", 999'u16,
                      addCorpusRecordBytes(@[integerChoice(1, 0, 100, 0)]))
    let db = newExampleDB(dbPath)
    var msg = ""
    try:
      discard db.loadCorpus("newver")
      fail()
    except DbError as e:
      msg = e.msg
    check "999" in msg
    check "1" in msg   # the current corpusLogFormatVersion this build supports

  test "an unrecognized magic refuses (not a silent misread)":
    writeRawCorpusLog(dbPath, "badmagic", "XXXX", 1'u16,
                      addCorpusRecordBytes(@[integerChoice(1, 0, 100, 0)]))
    let db = newExampleDB(dbPath)
    expect DbError:
      discard db.loadCorpus("badmagic")

  test "a corpus log older than current reads as-is; the next compaction rewrites it at current version":
    let entry = @[integerChoice(1, 0, 100, 0)]
    writeRawCorpusLog(dbPath, "oldver", "NLC0", 0'u16, addCorpusRecordBytes(entry))
    let db = newExampleDB(dbPath)
    # Read-older-than-current: no refusal, the entry comes through.
    check db.loadCorpus("oldver") == @[entry]
    # Drive enough churn to force a compaction — the fold rewrites the log
    # at the CURRENT format version, regardless of what version it started at.
    for i in 0 ..< 30:
      db.saveCorpus("oldver", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
    let gen = openCorpusSnapshot(dbPath, "oldver").cutPoint.generation
    check gen > 1
    let raw = readFile(dbPath / ("oldver.corpus." & $gen & ".log"))
    check ord(raw[4]) == 1   # u16 formatVersion low byte, little-endian: current v1
    check ord(raw[5]) == 0   # high byte

  test "R25: a genuinely TRUNCATED trailing record (recLen exceeds the file's actual remaining bytes) refuses loudly -- the torn-tail case (E0 findings mandate 4)":
    # Every corruption test above constructs a well-formed HEADER with a
    # wrong magic/version -- none writes the literal "torn tail" shape a
    # process killed mid-`appendCorpusRecord` (db.nim) actually leaves on
    # disk: one COMPLETE, valid record, followed by a SECOND record whose
    # length-prefix was written (or partially written) before the crash but
    # whose payload never made it -- `recLen` claims more bytes than the
    # file has. `readCorpusRecords`' `needBytes` check must catch this and
    # refuse (DbError), not silently truncate the read to "just the
    # complete record" and not decode-panic.
    var records: seq[byte]
    records.add addCorpusRecordBytes(@[integerChoice(1, 0, 100, 0)])   # one COMPLETE record
    records.putU32(500'u32)   # a second record's length prefix: claims 500 bytes
    records.add byte(0)       # op byte only -- then the file just ends (the crash point)
    writeRawCorpusLog(dbPath, "torn", "NLC0", 1'u16, records)

    let db = newExampleDB(dbPath)
    var raised = false
    var msg = ""
    try:
      discard db.loadCorpus("torn")
    except DbError as e:
      raised = true
      msg = e.msg
    check raised
    check "truncated" in msg

  test "R25: garbage bytes mid-record (a well-formed length/op header, but a payload that is not a valid encoded choice-sequence) refuses loudly rather than silently misdecoding":
    # A DIFFERENT corruption shape than the torn tail above: the record
    # FRAMING survives intact (a correct `recLen`, a real `opAddCorpus`
    # byte), but the PAYLOAD inside it is garbage -- not a valid
    # `toBytes(ChoiceNode)` encoding. This exercises `fromBytes`'s own
    # decode-time `DbCorrupt` (serialize.nim), a DIFFERENT code path than
    # the record-framing `needBytes` check the torn-tail test above hits.
    #
    # Pinned as OBSERVED, not assumed: unlike a framing-level torn tail
    # (`readCorpusLogFile`'s own try/except wraps that into `DbError`), a
    # bad PAYLOAD is decoded later, inside `replayCorpusRecords`'s
    # `fromBytes` call (`replayCorpusLog` = `replayCorpusRecords(
    # readCorpusLogFile(p))`) -- OUTSIDE that wrapping try/except -- so the
    # raw `DbCorrupt` propagates uncaught rather than being folded into
    # `DbError` the way every other corruption test in this suite is. A
    # caller that only catches `DbError` (as this suite's OTHER corruption
    # tests all do) would NOT be shielded from this specific corruption
    # shape -- worth flagging as a real inconsistency between the two
    # corruption-handling layers, even though closing it is a `db.nim`
    # change outside this suite's scope.
    var records: seq[byte]
    records.add addCorpusRecordBytes(@[integerChoice(1, 0, 100, 0)])   # one COMPLETE, valid record
    let garbagePayload = @[0xFF'u8, 0xFF'u8, 0xFF'u8, 0xFF'u8]
    records.putU32(uint32(1 + garbagePayload.len))
    records.add byte(0)   # opAddCorpus -- structurally valid
    records.add garbagePayload   # ...but not a valid encoded ChoiceSeq
    writeRawCorpusLog(dbPath, "midgarbage", "NLC0", 1'u16, records)

    let db = newExampleDB(dbPath)
    expect DbCorrupt:
      discard db.loadCorpus("midgarbage")

suite "R10: mid-campaign reclaim of superseded corpus generations":
  ## R10 (HIGH, verified): E3b's compactor (`maybeCompactCorpusLog`) never
  ## unlinked a superseded generation, and the only reclaim path
  ## (`sweepSupersededCorpusGenerations`) ran once, at campaign STARTUP —
  ## so a long-running campaign that compacts N times accumulated N
  ## superseded generation files that survived until the NEXT campaign.
  ## Fixed by implementing the reader-lease scheme the RFC's E3b section
  ## specified (`openCorpusSnapshot`/`closeCorpusSnapshot`) and running
  ## reclaim MID-campaign: right after every compaction publishes a new
  ## head, and again whenever a lease is released. A generation is only
  ## ever reclaimed once it is (a) not the current head and (b) not pinned
  ## by an open lease — see `reclaimUnpinnedGenerations` in `db.nim`.
  setup:
    let dbPath = getTempDir() / "nelli_test_corpuslog_r10_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  proc corpusGenFiles(dbPath, key: string): seq[string] =
    for kind, p in walkDir(dbPath, relative = false):
      let n = extractFilename(p)
      if kind == pcFile and n.startsWith(key & ".corpus.") and n.endsWith(".log"):
        result.add n

  test "repeated compaction does not grow the generation-file count without bound (no open snapshot)":
    let db = newExampleDB(dbPath)
    var maxFilesSeen = 0
    var compactions = 0
    var lastGen = 1
    for i in 0 ..< 300:
      db.saveCorpus("bounded", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
      let files = corpusGenFiles(dbPath, "bounded")
      maxFilesSeen = max(maxFilesSeen, files.len)
      let gen = openCorpusSnapshot(dbPath, "bounded").cutPoint.generation
      closeCorpusSnapshot(dbPath, "bounded", CorpusCutPoint(generation: gen, offset: 0))
      if gen > lastGen:
        inc compactions
        lastGen = gen
    check compactions >= 5   # drove enough churn to trigger reclaim repeatedly, not just once
    # With no snapshot ever held open across a compaction, mid-campaign
    # reclaim removes the previous generation the instant a new one is
    # published — exactly one generation file for this key exists on disk
    # at any observation point, regardless of how many compactions ran.
    check maxFilesSeen == 1

  test "head generation and corpus contents are intact after many rounds of reclaim":
    let db = newExampleDB(dbPath)
    for i in 0 ..< 300:
      db.saveCorpus("integrity", @[integerChoice(i, 0, 100000, 0)], maxEntries = 5)
    let live = db.loadCorpus("integrity")
    check live.len == 5
    check toInt64(live[0][0].intVal) == 299   # newest-first
    check toInt64(live[4][0].intVal) == 295
    # A fresh (cold) handle replaying from disk sees the identical set —
    # reclaim never touched data still reachable from the head.
    let fresh = newExampleDB(dbPath)
    check fresh.loadCorpus("integrity") == live
    # Exactly the head generation remains on disk; nothing orphaned.
    check corpusGenFiles(dbPath, "integrity").len == 1

  test "an open snapshot lease blocks mid-campaign reclaim of its generation; releasing it unblocks reclaim":
    let db = newExampleDB(dbPath)
    db.saveCorpus("leased", @[integerChoice(0, 0, 100, 0)])
    let snap = openCorpusSnapshot(dbPath, "leased")   # lease on gen 1 while it is still ACTIVE
    check snap.cutPoint.generation == 1
    let gen1Path = dbPath / "leased.corpus.1.log"
    let headPath = dbPath / "leased.corpus.head"

    # Drive churn until generation 1 is actually superseded. While it is
    # still the active append target its bytes are EXPECTED to keep
    # growing (ordinary appends) — that is not a reader-safety violation,
    # it is exactly what `CorpusCutPoint.offset` exists to bound. Only a
    # generation that has stopped being the head is guaranteed frozen, so
    # this loop stops at the first compaction, not before.
    var j = 1
    while not fileExists(headPath):
      db.saveCorpus("leased", @[integerChoice(1000 + j, 0, 100000, 0)], maxEntries = 2)
      inc j
      check j < 500   # sanity bound — fail fast instead of hanging on a regression
    # Generation 1 is superseded now; the lease opened above must have
    # kept mid-campaign reclaim from removing it.
    check fileExists(gen1Path)
    let frozen = readFile(gen1Path)

    # Drive further churn — entirely on generation 2+ — forcing at least
    # one more compaction on top of the already-superseded, still-leased
    # generation 1. The concurrent/mid-read reader case: a lease taken out
    # before ANY of this churn must survive it untouched.
    for k in 0 ..< 30:
      db.saveCorpus("leased", @[integerChoice(2000 + k, 0, 100000, 0)], maxEntries = 2)

    check readFile(gen1Path) == frozen        # unmutated since it was superseded
    check corpusGenFiles(dbPath, "leased").len == 2   # gen 1 (leased) + the new head
    check db.loadCorpus("leased").len == 2    # writer-side view is unaffected by the held lease

    # Releasing the lease finishes reclaiming generation 1 immediately —
    # bounded growth resumes without waiting for the next compaction.
    closeCorpusSnapshot(dbPath, "leased", snap.cutPoint)
    check not fileExists(gen1Path)
    check corpusGenFiles(dbPath, "leased").len == 1
    check db.loadCorpus("leased").len == 2    # content intact once the lease is gone

  test "R25: two overlapping reader leases, pinned at DIFFERENT generations, each survive reclaim independently -- concurrent-reader-vs-compaction":
    # The lease test above only ever holds ONE snapshot open at a time.
    # `corpusSnapshotLeases` (db.nim) is refcounted per `(dbPath, testId,
    # generation)` precisely so MORE THAN ONE reader can be outstanding
    # simultaneously -- the scenario "concurrent reader vs compaction"
    # actually names: a reader that opened before a compaction and a
    # SECOND reader that opened after it, both still live when a THIRD
    # compaction fires, must each keep exactly their own pinned generation
    # alive regardless of what the other reader — or the writer's ongoing
    # churn — is doing.
    let db = newExampleDB(dbPath)
    db.saveCorpus("multilease", @[integerChoice(0, 0, 100, 0)])
    let leaseA = openCorpusSnapshot(dbPath, "multilease")   # pins gen 1, still ACTIVE
    check leaseA.cutPoint.generation == 1
    let gen1Path = dbPath / "multilease.corpus.1.log"
    let headPath = dbPath / "multilease.corpus.head"

    # Drive churn until the FIRST compaction publishes gen 2.
    var j = 1
    while not fileExists(headPath):
      db.saveCorpus("multilease", @[integerChoice(1000 + j, 0, 100000, 0)], maxEntries = 2)
      inc j
      check j < 500
    check fileExists(gen1Path)   # leaseA's open lease kept gen 1 alive through the compaction

    # A SECOND reader opens NOW, with leaseA STILL open -- resolves to the
    # CURRENT head (gen 2), a DIFFERENT generation than leaseA pins.
    let leaseB = openCorpusSnapshot(dbPath, "multilease")
    check leaseB.cutPoint.generation == 2
    let gen2Path = dbPath / "multilease.corpus.2.log"
    check fileExists(gen2Path)

    # Drive further churn — entirely on generation 2+ — forcing at least
    # one more compaction (a new head) while BOTH leases are still open.
    for k in 0 ..< 30:
      db.saveCorpus("multilease", @[integerChoice(2000 + k, 0, 100000, 0)], maxEntries = 2)

    # All THREE generations coexist: gen 1 (leaseA), gen 2 (leaseB), and
    # whatever the new head now is (unleased, current, reclaim never
    # touches the head) — reclaim skips every generation a live lease
    # pins, no matter how much churn runs on top of either.
    check fileExists(gen1Path)
    check fileExists(gen2Path)
    check corpusGenFiles(dbPath, "multilease").len == 3

    # Releasing leaseA reclaims ONLY generation 1 — leaseB (still open)
    # keeps generation 2 alive regardless.
    closeCorpusSnapshot(dbPath, "multilease", leaseA.cutPoint)
    check not fileExists(gen1Path)
    check fileExists(gen2Path)
    check corpusGenFiles(dbPath, "multilease").len == 2

    # Releasing leaseB now reclaims generation 2 too — only the current
    # head remains.
    closeCorpusSnapshot(dbPath, "multilease", leaseB.cutPoint)
    check not fileExists(gen2Path)
    check corpusGenFiles(dbPath, "multilease").len == 1
