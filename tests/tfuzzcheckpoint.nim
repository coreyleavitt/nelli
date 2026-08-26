## RFC-fuzzer-nextgen S6 — learned-state checkpoint/resume, at the fuzz loop
## level (see `tlearnedstate.nim` for the pure encode/decode unit tests).
##
## `fuzz`'s open-ended, wall-clock-scheduled contract means routine
## interruption (Ctrl-C, OOM-kill, a CI timeout) and restart is the normal
## case. The corpus already survives via `ExampleDatabase` (Phase 6b); this
## suite proves the SCHEDULING state built on top of it — S1 rarity/energy,
## S2 bandit weights, G5's dictionary — now survives too, via
## `FuzzSettings.checkpointCadence`, without perturbing any pre-S6 campaign
## that leaves it at its default (off).
import std/unittest
import nelli
import nelli/db

proc deadbeefGate(x: int) {.cover, covercmp.} =
  ## Same headline gate G5's own suite (`tfuzzi2s.nim`) uses — instrumented
  ## with `{.covercmp.}` so `enableI2S` actually harvests a non-trivial
  ## dictionary, giving this suite a real (not vacuous) `Dictionary` to
  ## prove resumes warm.
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

proc warmSettings(db: ExampleDatabase; key: string; iters: int; seed: uint64;
                  cadence = 50): FuzzSettings =
  FuzzSettings(seed: seed, maxIterations: iters, database: db, persistKey: key,
              enableI2S: true, checkpointCadence: cadence)

suite "fuzz: learned-state checkpoint/resume (RFC-fuzzer-nextgen S6)":
  test "a resumed campaign starts warm: bandit / frontier / dictionary are non-cold":
    let db = inMemoryDatabase()
    var fr1 = newCoverageFrontier("bin1")
    let repA = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr1,
                    warmSettings(db, "camp", 300, 1'u64))
    check fr1.stats.totalAdmitted >= 300
    check repA.dictionary.entries.len > 0

    var fr2 = newCoverageFrontier("bin1")
    let repB = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr2,
                    warmSettings(db, "camp", 1, 2'u64))
    # Frontier: a genuinely cold campaign's totalAdmitted after one iteration
    # would be at most (resumed-corpus preload count) + 1, nowhere near
    # campaign A's ~300 — so a value well above that can only come from the
    # restored checkpoint.
    check fr2.stats.totalAdmitted > 100
    # Bandit: one iteration's havoc stack can pull at most `maxHavocStackOps`
    # (8) arms total, so a discounted-pull sum above 8 can only come from
    # restored pull-mass, never from this run's own single iteration.
    var pullSum = 0.0
    for p in repB.stats.operatorPulls: pullSum += p
    check pullSum > 8.0
    # Dictionary only ever grows (harvested, deduped, never pruned) —
    # a resumed campaign starts at least as large as where A left off.
    check repB.dictionary.entries.len >= repA.dictionary.entries.len

  test "a fresh persistKey has no checkpoint to resume: cold start":
    let db = inMemoryDatabase()
    var fr1 = newCoverageFrontier("bin1")
    discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr1,
                warmSettings(db, "camp-a", 300, 1'u64))

    var fr2 = newCoverageFrontier("bin1")
    let repB = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr2,
                    warmSettings(db, "camp-b", 1, 2'u64))
    check fr2.stats.totalAdmitted <= 10
    var pullSum = 0.0
    for p in repB.stats.operatorPulls: pullSum += p
    check pullSum <= 8.0

  test "a corrupt/incompatible checkpoint is ignored: cold start, not a crash":
    let db = inMemoryDatabase()
    var fr1 = newCoverageFrontier("bin1")
    discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr1,
                warmSettings(db, "camp", 300, 1'u64))
    # Overwrite the real checkpoint with garbage bytes — the loop must
    # degrade to cold start, never raise.
    db.saveSched(fuzzCorpusKey("camp", "bin1"), @[1'u8, 2'u8, 3'u8])

    var fr2 = newCoverageFrontier("bin1")
    let repB = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr2,
                    warmSettings(db, "camp", 1, 2'u64))
    check fr2.stats.totalAdmitted <= 10
    var pullSum = 0.0
    for p in repB.stats.operatorPulls: pullSum += p
    check pullSum <= 8.0

  test "checkpointCadence: 0 (the default) never touches the checkpoint at all":
    let db = inMemoryDatabase()
    var fr = newCoverageFrontier("bin1")
    discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr,
                FuzzSettings(seed: 1'u64, maxIterations: 300, database: db,
                            persistKey: "camp", enableI2S: true))
      # checkpointCadence left at its zero-value default.
    check db.loadSched(fuzzCorpusKey("camp", "bin1")).len == 0

  test "an arm-count mismatch (settings changed since checkpoint) skips bandit restore only":
    let db = inMemoryDatabase()
    var fr1 = newCoverageFrontier("bin1")
    # enableI2S: true -> 7 arms (5 base + I2S + interestingValue + dictInsert).
    discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr1,
                warmSettings(db, "camp", 300, 1'u64))

    var fr2 = newCoverageFrontier("bin1")
    # enableI2S: false -> 6 arms (5 base + interestingValue only): a
    # positional mismatch against the 7-arm checkpoint. Must not crash, and
    # must produce exactly 6 arms (this run's own layout), not the stale 7.
    let repB = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr2,
                    FuzzSettings(seed: 2'u64, maxIterations: 1, database: db,
                                persistKey: "camp", checkpointCadence: 50))
    check repB.stats.operatorPulls.len == 6
