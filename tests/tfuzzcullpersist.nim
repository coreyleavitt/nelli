## RFC-fuzzer-nextgen S4 deliverable 2: coverage-value-aware persisted-corpus
## eviction — the DOCUMENTED scope-cut (see fuzz.nim's `uniformCorpus`/
## `favoredIndices` doc and the RFC's own text): db.nim's `saveCorpus`/
## `dedupPrepend` stays PURELY recency-based and untouched (it has no
## coverage signal — coverage lives in the fuzz loop, not the DB, and
## `dedupPrepend` is shared with the `primary` regression-replay section,
## which has no coverage concept at all). Instead, the FUZZ LOOP decides
## what to (re)persist coverage-awarely BEFORE calling `saveCorpus`: at each
## cull tick it re-saves the still-favored (coverage-valuable) live corpus,
## ordered least-to-most-valuable — `dedupPrepend`'s own documented
## move-to-front-on-resave contract (db.nim ~352-368) then keeps the most
## valuable entries frontmost, i.e. safest from `corpusLimit`'s recency-only
## cap, over an untouched flood of newer, redundant admits.
##
## This is the sharpest instance of the RFC's stated risk: a preloaded
## rare-edge SEED is admitted into the in-memory frontier up front (F2's
## up-front replay pass) but — because its edge is already covered by the
## time the loop starts — no mutant can ever "freshly discover" it again,
## so pre-S4 it is NEVER individually `saveCorpus`'d and never reaches disk
## at all. S4's periodic re-touch is what puts it there and keeps it there
## across a long campaign that floods dozens of other (individually
## legitimate) admissions past a small `corpusLimit`.

import std/unittest
import nelli
import nelli/choice

proc coverageWithRareEdge(): Target[int] =
  ## 50 "common" edges (`x mod 50`) any mutant can freely rediscover early;
  ## ONE rare edge (slot 50) that only the exact seeded value ever lights.
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](51)
    c[((x mod 50) + 50) mod 50] = 1'u8
    if x == 999_000: c[50] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc runCampaign(uniformCorpus: bool): tuple[db: ExampleDatabase, testId: string] =
  let db = inMemoryDatabase()
  var fr = newCoverageFrontier("bin1")
  let rareSeed = @[integerChoice(999_000, 0, 1_000_000, 0)]
  let s = FuzzSettings(maxIterations: 300, seed: 7, database: db, persistKey: "camp", corpusLimit: 5, initialIRCorpus: @[rareSeed], scheduling: SchedulingConfig(cullCadence: 20, uniformCorpus: uniformCorpus))
  discard fuzz(integers(0, 1_000_000), coverageWithRareEdge(), fr, s)
  (db: db, testId: fuzzCorpusKey("camp", "bin1"))

suite "S4 deliverable 2: coverage-value-aware persisted-corpus protection":

  test "a rare-edge seed survives a flood of redundant on-disk admits (S4 default)":
    let rareSeed = @[integerChoice(999_000, 0, 1_000_000, 0)]
    let (db, testId) = runCampaign(uniformCorpus = false)
    let onDisk = db.loadCorpus(testId)
    check onDisk.len <= 5              # corpusLimit is honored, not bypassed
    check rareSeed in onDisk           # ...but the rare seed is never the casualty

  test "without S4 (uniformCorpus), the rare-edge seed never reaches disk at all":
    let rareSeed = @[integerChoice(999_000, 0, 1_000_000, 0)]
    let (db, testId) = runCampaign(uniformCorpus = true)
    check rareSeed notin db.loadCorpus(testId)   # the pre-S4 gap this deliverable closes

  test "db.nim's saveCorpus/dedupPrepend itself is untouched: still pure recency, still capped":
    ## Direct characterization of the CHOSEN scope-cut's other half — no
    ## coverage-aware logic was added inside db.nim itself. A plain flood of
    ## saves with no fuzz-loop involvement still evicts purely by recency.
    let db = inMemoryDatabase()
    for i in 0 ..< 10:
      db.saveCorpus("t", @[integerChoice(i, 0, 1000, 0)], maxEntries = 3)
    let kept = db.loadCorpus("t")
    check kept.len == 3
    check @[integerChoice(9, 0, 1000, 0)] in kept   # newest survives
    check @[integerChoice(0, 0, 1000, 0)] notin kept # oldest evicted, regardless of value
