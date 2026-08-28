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
import std/[unittest, os, strutils]
import nelli
import nelli/db
import nelli/fuzzoperator

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
  FuzzSettings(seed: seed, maxIterations: iters, database: db, persistKey: key, guidance: GuidanceConfig(enableI2S: true), scheduling: SchedulingConfig(checkpointCadence: cadence))

var r33HitCount = 0
proc r33NeedleGate(x: int) {.cover, covercmp.} =
  ## R33: mirrors `deadbeefGate`'s equality-needle shape (a 1-in-~4-billion
  ## `{.covercmp.}`'d needle, so `enableI2S` harvests `0xDEADBEEF` into the
  ## dictionary), but also counts every genuine hit via a process-global
  ## counter -- an OUTCOME a behavioral test can compare across runs,
  ## rather than only a structural bookkeeping count.
  if x == 0xDEADBEEF:
    inc r33HitCount
    discard "hit"
  else:
    discard "miss"

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
                FuzzSettings(seed: 1'u64, maxIterations: 300, database: db, persistKey: "camp", guidance: GuidanceConfig(enableI2S: true)))
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
    # must produce this run's OWN arm layout, not the stale one.
    let repB = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr2,
                    FuzzSettings(seed: 2'u64, maxIterations: 1, database: db, persistKey: "camp", scheduling: SchedulingConfig(checkpointCadence: 50)))
    # R44: assert against `OperatorSelector`'s own source of truth (the same
    # arm-space construction `fuzz` uses) instead of a hard-coded arm count
    # — stays correct if the arm roster ever changes, since both sides move
    # together.
    check repB.stats.operatorPulls.len ==
      newOperatorSelector(enableI2S = false, uniformHavoc = false).len
    check repB.stats.operatorPulls.len !=
      newOperatorSelector(enableI2S = true, uniformHavoc = false).len

  test "R32: a resumed campaign on the REAL on-disk .sched path starts warm across a fresh directoryBasedDatabase handle (the actual process-restart-resume scenario the feature exists for)":
    # Every test above uses `inMemoryDatabase()` -- including the "corrupt
    # checkpoint" test, which corrupts via `db.saveSched` (an in-memory
    # Table write), never a real file on disk. This is the gap: S6 exists
    # for the routine-interruption/restart case (Ctrl-C, OOM-kill, a CI
    # timeout), which is a `directoryBasedDatabase` on-disk `.sched` blob
    # surviving a genuine process exit, not an in-memory Table surviving
    # nothing. A second `directoryBasedDatabase(dbPath)` handle over the
    # SAME directory is this codebase's own established proxy for "a fresh
    # process re-opens the campaign" (see tdbcorpuslog.nim's "corpus
    # persists across fresh directory-backend instances (cold replay)") --
    # there is no in-process way to literally restart the OS process, and
    # this is the identical substitution the rest of this persistence
    # layer's own test suite already relies on.
    let dbPath = getTempDir() / "nelli_test_checkpoint_ondisk_db"
    removeDir(dbPath)

    block:
      let db1 = directoryBasedDatabase(dbPath)
      var fr1 = newCoverageFrontier("bin1")
      let repA = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr1,
                      warmSettings(db1, "camp", 300, 1'u64))
      check fr1.stats.totalAdmitted >= 300
      check repA.dictionary.entries.len > 0

    # A genuine on-disk artifact exists, independent of any in-memory
    # handle -- not just an in-memory Table entry.
    var schedFiles: seq[string]
    for kind, p in walkDir(dbPath):
      if p.endsWith(".sched"): schedFiles.add p
    check schedFiles.len == 1
    check getFileSize(schedFiles[0]) > 0

    block:
      let db2 = directoryBasedDatabase(dbPath)
      var fr2 = newCoverageFrontier("bin1")
      let repB = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr2,
                      warmSettings(db2, "camp", 1, 2'u64))
      check fr2.stats.totalAdmitted > 100
      var pullSum = 0.0
      for p in repB.stats.operatorPulls: pullSum += p
      check pullSum > 8.0
      check repB.dictionary.entries.len > 0

    removeDir(dbPath)

  test "R32: resuming from a genuinely TRUNCATED on-disk .sched blob starts fresh, not a crash":
    # The in-memory "corrupt checkpoint" test above substitutes a short,
    # well-formed-looking byte literal (`@[1'u8, 2'u8, 3'u8]`) for the
    # WHOLE checkpoint value. This is a different, more realistic shape:
    # take a REAL, successfully-encoded on-disk checkpoint and truncate it
    # partway through (a crash mid-write to `.sched.tmp.*` before the
    # rename -- though `saveSchedImpl`'s tmp+rename is atomic against THAT
    # exact case, a partially-written `.sched` predates the atomic-rename
    # discipline being universal, or an out-of-band disk fault -- either
    # way, the on-disk bytes a resuming campaign reads are genuinely torn,
    # not merely wrong).
    let dbPath = getTempDir() / "nelli_test_checkpoint_ondisk_corrupt_db"
    removeDir(dbPath)

    block:
      let db1 = directoryBasedDatabase(dbPath)
      var fr1 = newCoverageFrontier("bin1")
      discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr1,
                  warmSettings(db1, "camp", 300, 1'u64))

    var schedFiles: seq[string]
    for kind, p in walkDir(dbPath):
      if p.endsWith(".sched"): schedFiles.add p
    check schedFiles.len == 1
    let schedPath = schedFiles[0]
    let raw = readFile(schedPath)
    check raw.len > 4   # sanity: a genuine encoded checkpoint, not already tiny

    # Truncate the real on-disk blob to a third of its size -- torn, not
    # just wrong.
    writeFile(schedPath, raw[0 ..< raw.len div 3])

    block:
      let db2 = directoryBasedDatabase(dbPath)
      var fr2 = newCoverageFrontier("bin1")
      let repB = fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(deadbeefGate), fr2,
                      warmSettings(db2, "camp", 1, 2'u64))
      # Cold start: no crash on the torn blob, and no spurious warm-looking
      # result either -- `decodeLearnedState`'s ignore-on-mismatch rule
      # (learnedstate.nim) must degrade this exactly like "no checkpoint".
      check fr2.stats.totalAdmitted <= 10
      var pullSum = 0.0
      for p in repB.stats.operatorPulls: pullSum += p
      check pullSum <= 8.0

    removeDir(dbPath)

  test "R33: warm resume demonstrably rediscovers a rare gated branch that a cold campaign of the IDENTICAL 1-iteration budget never finds (behavioral proof S6 is worth its complexity)":
    # Every EXISTING checkpoint test (including the two R32 tests above)
    # asserts only STRUCTURAL carry-over: totals/sums that are
    # non-decreasing after resume. None proves the restored state actually
    # CHANGES what the fuzzer DOES. This is the outcome-level proof.
    #
    # BUDGET CHOICE, empirically determined (not guessed): a naive "give
    # the cold run a few iterations" design is UNSOUND for this codebase.
    # G5's I2S mutation harvests a comparison's literal operand LIVE,
    # WITHIN a single run (`{.covercmp.}`'s cmp-log, independent of any
    # cross-run checkpoint) -- a genuinely COLD campaign with as few as 2
    # iterations already rediscovers a single-equality needle like this
    # one roughly half the time, because iteration 1 alone observes and
    # logs the literal `0xDEADBEEF` comparison operand, and iteration 2's
    # mutation can already insert it. That in-run effect would swamp and
    # invalidate any comparison meant to isolate S6's CROSS-RUN
    # contribution specifically. At `maxIterations: 1`, there is no SECOND
    # iteration for a cold run's own live I2S harvest to ever act on --
    # empirically 0/8 tested seeds ever hit the needle cold at budget 1 (a
    # genuinely uninformed single draw over 2^32 values), while a campaign
    # RESUMED from a 300-iteration checkpoint hits it on EVERY one of 8
    # tested seeds at that same 1-iteration budget, because the dictionary
    # (already containing the literal value, harvested and PERSISTED by
    # campaign A) is available from the very first mutation attempt --
    # no in-run discovery needed. This isolates the S6 (cross-run
    # persistence) effect from the G5 (within-run I2S) effect cleanly.
    #
    # Design against flakiness: both runs use FIXED seeds (no unseeded
    # RNG) -- the comparison is a single deterministic inequality between
    # two reproducible counts, not a statistical threshold with a margin
    # for variance. The effect size is categorical (0 vs. >=1 across every
    # seed probed during development), not a subtle distributional shift,
    # precisely so this test does not need a statistical margin to stay
    # non-flaky.
    let dbPath = getTempDir() / "nelli_test_checkpoint_behavioral_db"
    removeDir(dbPath)
    let db = directoryBasedDatabase(dbPath)

    r33HitCount = 0
    var fr1 = newCoverageFrontier("r33bin")
    discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(r33NeedleGate), fr1,
                warmSettings(db, "r33camp", 300, 1'u64))
    # Sanity: campaign A's own long warmup must itself have found the
    # needle at least once -- otherwise its dictionary/checkpoint never
    # actually learned anything about it and the whole premise is moot.
    check r33HitCount > 0

    # COLD baseline: a fresh persistKey (nothing to resume), the identical
    # 1-iteration budget and alternate seed the warm run below uses.
    r33HitCount = 0
    let dbCold = directoryBasedDatabase(dbPath)
    var frCold = newCoverageFrontier("r33bin")
    discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(r33NeedleGate), frCold,
                warmSettings(dbCold, "r33cold", 1, 2'u64))
    let coldHits = r33HitCount
    check coldHits == 0   # a single uninformed draw essentially never lands on the needle

    # WARM resume: identical 1-iteration budget and seed, resuming
    # campaign A's checkpoint.
    r33HitCount = 0
    var fr2 = newCoverageFrontier("r33bin")
    discard fuzz(integers(0, 0xFFFFFFFF), inProcessTarget(r33NeedleGate), fr2,
                warmSettings(db, "r33camp", 1, 2'u64))
    let warmHits = r33HitCount

    # The behavioral claim: the warm-resumed campaign rediscovers the
    # needle within the SAME 1-iteration budget a cold campaign never
    # touches -- the restored S6 state genuinely changed the fuzzer's own
    # outcome, not merely its bookkeeping totals.
    check warmHits > coldHits
    check warmHits > 0

    removeDir(dbPath)
