## Phase 6b (docs/fuzz/FUZZ_PLAN.md): corpus persistence + resume. The fuzz loop saves every
## new-coverage input to an ExampleDatabase and reloads it as seeds on the next run, keyed by
## fuzzCorpusKey(persistKey, targetId). Folding the targetId in means a changed binary re-keys:
## the stale corpus (tied to a now-invalid coverage map) is simply missed. Pure — stub Target
## with value-dependent coverage, in-memory db; no subprocess.
##
## F1 (RFC-chapulin-hardening) moved this persistence off the `primary` section (shared with
## `forAll`'s regression-replay, which prunes on pass) onto a dedicated, never-pruned `corpus`
## section — `loadCorpus`/`saveCorpus`. These assertions were updated accordingly.

import std/unittest
import proptest

proc coverageByValue(): Target[int] =
  ## One hot edge per (x mod 8): distinct inputs light distinct edges, so the
  ## corpus grows and several entries get persisted.
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](8)
    c[(x mod 8 + 8) mod 8] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc settings(db: ExampleDatabase; iters: int; seed: uint64): FuzzSettings =
  FuzzSettings(maxIterations: iters, seed: seed, database: db, persistKey: "camp")

suite "fuzz: corpus persistence + resume (Phase 6b)":
  test "new-coverage inputs are persisted to the database":
    let db = inMemoryDatabase()
    var fr = newCoverageFrontier("bin1")
    discard fuzz(integers(0, 1000), coverageByValue(), fr, settings(db, 300, 1))
    check db.loadCorpus(fuzzCorpusKey("camp", "bin1")).len >= 3

  test "a fresh run resumes the persisted corpus as seeds":
    let db = inMemoryDatabase()
    var fr1 = newCoverageFrontier("bin1")
    discard fuzz(integers(0, 1000), coverageByValue(), fr1, settings(db, 300, 1))
    let saved = db.loadCorpus(fuzzCorpusKey("camp", "bin1")).len
    check saved >= 3
    # A second run with one iteration still starts from all persisted seeds.
    var fr2 = newCoverageFrontier("bin1")
    let repB = fuzz(integers(0, 1000), coverageByValue(), fr2, settings(db, 1, 2))
    check repB.corpus.irEntries.len >= saved

  test "a changed targetId re-keys: the stale corpus is not resumed":
    let db = inMemoryDatabase()
    var fr1 = newCoverageFrontier("bin1")
    discard fuzz(integers(0, 1000), coverageByValue(), fr1, settings(db, 300, 1))
    let savedV1 = db.loadCorpus(fuzzCorpusKey("camp", "bin1")).len
    check savedV1 >= 3
    # The binary changed → new targetId. The old corpus stays under the old key,
    # but this run must not load it (its coverage map is no longer comparable).
    var fr2 = newCoverageFrontier("bin2")
    let repB = fuzz(integers(0, 1000), coverageByValue(), fr2, settings(db, 1, 2))
    check repB.corpus.irEntries.len < savedV1          # started fresh, not from bin1's corpus
    check db.loadCorpus(fuzzCorpusKey("camp", "bin1")).len == savedV1  # bin1 corpus untouched
