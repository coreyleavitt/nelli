## RFC-fuzzer-nextgen E-cleanup (C1): campaign-startup sweep of stale
## campaign-scoped OS resources a hard-killed prior campaign left behind.
##
## Mirrors the precedent `directoryBasedDatabase`'s constructor already sets
## (`db.nim`'s `.tmp.<pid>.<tid>` sweep): a namespaced-prefix sweep run once,
## at construction time, before this campaign's own workers/writers have
## created anything of their own — so everything the sweep finds is
## necessarily left over from a PRIOR run, never something live.
##
## Two resource classes, both swept from the SAME constructor call:
##  - superseded `<safeKey>.corpus.<gen>.log` generation files. R10 fix:
##    `db.nim` now also reclaims these MID-campaign, right after each
##    compaction and whenever a reader-lease (`openCorpusSnapshot`/
##    `closeCorpusSnapshot`) is released, so in the common (no live lease)
##    case there is nothing left for this sweep to do by the time it runs.
##    This sweep is the unconditional BACKSTOP: it ignores lease state
##    entirely and reclaims everything but the head generation, which is
##    only safe because no reader from a PRIOR campaign's PROCESS can still
##    be alive by the time a NEW campaign constructs its DB handle (a fresh
##    process starts with an empty lease table, so even a lease that never
##    got released — e.g. a hard-killed campaign — carries no weight here).
##  - stale POSIX `shm_open` segments in `/dev/shm` from a crashed prior
##    campaign's coverage transport (E2b) — identified by the `nelli_` name
##    prefix ALONE (matching the tmp-sweep's own prefix-only scoping), never
##    touching a foreign process's differently-prefixed segment.

import std/[unittest, os]
import nelli
import nelli/choice

when defined(posix):
  import std/posix

suite "E-cleanup C1: campaign-startup sweep — superseded corpus generations":
  setup:
    let dbPath = getTempDir() / "nelli_test_cleanupsweep_db"
    removeDir(dbPath)
  teardown:
    removeDir(dbPath)

  test "a fresh campaign start sweeps a superseded corpus generation, keeps the head generation":
    # R10 fix: mid-campaign reclaim now removes an UNPINNED superseded
    # generation immediately (see tdbcorpuslog.nim's "R10" suite), so an
    # ordinary compaction loop with no open snapshot leaves nothing for
    # THIS sweep to find. Exercise the sweep's actual necessary case: a
    # generation a lease pinned during the campaign and never released —
    # standing in for a reader from a campaign that was hard-killed before
    # it could call `closeCorpusSnapshot`. Mid-campaign reclaim must leave
    # a pinned generation alone; only a NEW campaign's startup sweep (which
    # ignores lease state, safe because a fresh process starts with an
    # empty lease table) reclaims it.
    var headGen: int
    block:
      let db = newExampleDB(dbPath)
      db.saveCorpus("k", @[integerChoice(0, 0, 100, 0)])
      discard openCorpusSnapshot(dbPath, "k")   # leases gen 1, deliberately never closed
      for i in 0 ..< 30:
        db.saveCorpus("k", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
      headGen = openCorpusSnapshot(dbPath, "k").cutPoint.generation
    check headGen > 1                                    # compaction actually ran
    check fileExists(dbPath / "k.corpus.1.log")           # still leased: mid-campaign reclaim left it alone

    # A NEW campaign constructing its DB handle is the sweep trigger.
    discard newExampleDB(dbPath)
    check not fileExists(dbPath / "k.corpus.1.log")       # swept: no reader from the OLD campaign survives
    check fileExists(dbPath / ("k.corpus." & $headGen & ".log"))  # CURRENT generation untouched
    check newExampleDB(dbPath).loadCorpus("k").len == 2   # content intact through the sweep

  test "a key with only generation 1 (no compaction ever ran) is left untouched":
    block:
      let db = newExampleDB(dbPath)
      db.saveCorpus("k2", @[integerChoice(1, 0, 100, 0)])
    check fileExists(dbPath / "k2.corpus.1.log")
    discard newExampleDB(dbPath)
    check fileExists(dbPath / "k2.corpus.1.log")          # nothing superseded here — nothing swept
    check newExampleDB(dbPath).loadCorpus("k2").len == 1

  test "distinct test ids each keep their own head generation independently":
    block:
      let db = newExampleDB(dbPath)
      for i in 0 ..< 30:
        db.saveCorpus("multiA", @[integerChoice(i, 0, 100000, 0)], maxEntries = 2)
      db.saveCorpus("multiB", @[integerChoice(1, 0, 100, 0)])   # never compacted
    let headGenA = openCorpusSnapshot(dbPath, "multiA").cutPoint.generation
    check headGenA > 1
    discard newExampleDB(dbPath)
    check not fileExists(dbPath / "multiA.corpus.1.log")
    check fileExists(dbPath / ("multiA.corpus." & $headGenA & ".log"))
    check fileExists(dbPath / "multiB.corpus.1.log")      # multiB's only generation: untouched

when defined(posix):
  suite "E-cleanup C1: campaign-startup sweep — stale nelli shm segments":
    proc leakShmFile(name: string) =
      ## Simulates a `shm_open`-created segment a prior campaign never
      ## cleaned up: on Linux, `shm_open("/foo", ...)` materializes as an
      ## ordinary file at `/dev/shm/foo` (the leading slash stripped) — so
      ## planting one by hand faithfully stands in for a real leaked
      ## segment without needing an actual crashed worker.
      writeFile("/dev/shm" / name, "leaked")

    proc shmFileExists(name: string): bool =
      fileExists("/dev/shm" / name)

    setup:
      let dbPath = getTempDir() / "nelli_test_cleanupsweep_shm_db"
      removeDir(dbPath)
      let staleName = "nelli_stale_test_" & $getCurrentProcessId()
      let foreignName = "otherapp_live_test_" & $getCurrentProcessId()
      leakShmFile(staleName)
      leakShmFile(foreignName)
    teardown:
      removeDir(dbPath)
      try: removeFile("/dev/shm" / ("nelli_stale_test_" & $getCurrentProcessId()))
      except OSError: discard
      try: removeFile("/dev/shm" / ("otherapp_live_test_" & $getCurrentProcessId()))
      except OSError: discard

    test "a nelli-prefixed shm segment is swept; a foreign-prefixed one is left untouched":
      check shmFileExists(staleName)
      check shmFileExists(foreignName)

      discard newExampleDB(dbPath)                        # campaign-startup sweep trigger

      check not shmFileExists(staleName)                  # nelli's own leaked segment: reclaimed
      check shmFileExists(foreignName)                     # a foreign process's segment: untouched
