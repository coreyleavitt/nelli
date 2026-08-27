## RFC-fuzzer-nextgen R27 (code review, MEDIUM/design): `fuzz[T]` is being
## decomposed into collaborators (checkpoint load/save, culling, energy +
## operator selection, crash recording / corpus-growth bookkeeping — see
## `fuzz.nim`'s module doc and the new `fuzzcheckpoint`/`fuzzcorpus`/
## `fuzzoperator`/`fuzzcrash` modules). The constraint on that work is
## behavioral identity: same seed, same campaign, byte-for-byte.
##
## This suite pins a full campaign's OBSERVABLE report against a fingerprint
## captured from the pre-refactor `fuzz[T]` monolith (commit 0cc32a6, before
## any R27 extraction) — the strongest form of the determinism proof the
## review asked for: not "it still passes its own tests" but "here is the
## exact trajectory the old code produced, byte for byte, and the new code
## reproduces it."
##
## The target is a hand-built `Target[int]` (never `inProcessTarget`) so
## `Observation.runResult.durationNs` is a value THIS test controls (fixed at
## 0) rather than a real `getMonoTime` measurement — S1's `entropicEnergy`
## folds `durationNs` into its exec-cost term, so leaving it wall-clock-real
## would make the campaign's own parent-selection trajectory sensitive to
## machine load, which is a real nondeterminism source `fuzz()` no test
## should paper over. Likewise `Observation.cmpLog` is set directly (a
## deterministic function of `x`) rather than relying on the in-process
## `currentCmpLog()` threadvar, which only `inProcessTarget`/`observeInProcess`
## reset per run — a stub `Target` never touches it, so reading it here would
## pick up whatever an EARLIER fuzz() call in this same test binary left
## behind (see `Observation.cmpLog`'s own doc for this exact hazard).
##
## Exercises every track's adaptive default in one campaign — S1 Entropic
## scheduling, S2 bandit operator selection, S3 havoc stacking, S4 periodic
## culling, S5 stats, S6 checkpointing (mid-run resume from a warm
## `inMemoryDatabase`), G5 I2S/dictionary — so a regression in any
## collaborator's wiring (not just its own unit tests) shows up here as a
## fingerprint mismatch.

import std/[unittest, options]
import nelli
import nelli/[db, serialize]

proc fnv(data: openArray[byte]; seed: uint64): uint64 =
  result = seed
  for b in data:
    result = result xor uint64(b)
    result = result * 1099511628211'u64

proc fnvStr(s: string; seed: uint64): uint64 =
  var bytes = newSeq[byte](s.len)
  for i, c in s: bytes[i] = byte(c)
  fnv(bytes, seed)

proc detTarget(): Target[int] =
  ## Deterministic, wall-clock-free stand-in for an instrumented property:
  ## coverage, verdict, message, and cmpLog are all pure functions of `x`.
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](40)
    for i in 0 ..< 32:
      if ((x shr i) and 1) == 1: c[i] = 1'u8
    c[32 + (x mod 8)] = 1'u8
    var verdict = vOk
    var msg = ""
    # A deterministic crash condition common enough (1-in-8) for havoc/bandit
    # mutation to reliably reach within a few hundred iterations, with a
    # handful of distinct messages so `recordCrashIfInteresting`'s de-dup
    # (keyed on coverage+message+CrashKind) gets real exercise, not a
    # permanently-empty `irCrashes`.
    if (x and 0x7) == 0x7:
      verdict = vInteresting
      msg = "boom-" & $((x shr 3) mod 5)
    let log = @[CmpLogEntry(kind: clkInt, op: coEq, width: 8,
                            lhsInt: uint64(x and 0xFFFFFFFF),
                            rhsInt: 0xDEADBEEF'u64)]
    Observation[int](verdict: verdict, coverage: Coverage(counters: c),
                     message: msg, cmpLog: some(log)))

proc fingerprint(seed: uint64; maxIterations: int): string =
  ## Runs one full campaign exercising every adaptive default (Entropic
  ## scheduling, the operator bandit, havoc stacking, periodic culling,
  ## checkpoint save+resume, I2S/dictionary) and folds every observable
  ## field of the resulting `FuzzReport` (excluding wall-clock-only fields:
  ## `CampaignStats.elapsed`/`execsPerSec`, which are real timings by
  ## design and not part of the campaign's logical trajectory) into one
  ## fingerprint string.
  let sharedDb = inMemoryDatabase()
  let persistKey = "r27-determinism"
  let warmupIters = maxIterations div 3

  # A short warmup campaign against the SAME persisted db/key first, so the
  # main campaign below exercises S6's mid-run RESUME path (a checkpoint
  # written by a distinct earlier run, not just this run's own periodic
  # ticks) — the fullest exercise of `CheckpointManager`'s load side.
  var warmupFr = newCoverageFrontier()
  discard fuzz(integers(0, 1_000_000), detTarget(), warmupFr,
    FuzzSettings(seed: seed xor 0xA5A5A5A5'u64, maxIterations: warmupIters,
                 database: sharedDb, persistKey: persistKey,
                 guidance: GuidanceConfig(enableI2S: true),
                 scheduling: SchedulingConfig(checkpointCadence: 11)))

  var fr = newCoverageFrontier()
  let settings = FuzzSettings(
    seed: seed,
    maxIterations: maxIterations,
    database: sharedDb,
    persistKey: persistKey,
    minimizeCorpus: true,
    guidance: GuidanceConfig(enableI2S: true),
    scheduling: SchedulingConfig(cullCadence: 17, checkpointCadence: 23))
  let rep = fuzz(integers(0, 1_000_000), detTarget(), fr, settings)

  var h = 1469598103934665603'u64   # FNV-1a offset basis
  for entry in rep.corpus.irEntries:
    h = fnv(toBytes(entry), h)
  for cr in rep.irCrashes:
    h = fnv(toBytes(cr.choices), h)
    h = fnvStr(cr.message, h)
  for e in rep.dictionary.entries:
    h = fnvStr($ord(e.kind), h)
    case e.kind
    of dvInt: h = fnvStr($e.intVal, h)
    of dvBytes: h = fnv(e.bytesVal, h)
    of dvString: h = fnvStr(e.strVal, h)
  var opPullsStr = ""
  for p in rep.stats.operatorPulls: opPullsStr.add($p & ",")
  var provStr = ""
  for pv in rep.stats.provenanceCounts: provStr.add($pv & ",")

  result = "iterations=" & $rep.iterations &
    "|coverageHits=" & $rep.coverageHits &
    "|corpusLen=" & $rep.corpus.irEntries.len &
    "|crashes=" & $rep.irCrashes.len &
    "|timedOut=" & $rep.timedOut &
    "|droppedSeeds=" & $rep.droppedSeeds &
    "|dictLen=" & $rep.dictionary.entries.len &
    "|totalMutationOps=" & $rep.totalMutationOps &
    "|stats.execs=" & $rep.stats.execs &
    "|stats.corpusSize=" & $rep.stats.corpusSize &
    "|stats.coverageEdges=" & $rep.stats.coverageEdges &
    "|stats.respawnCount=" & $rep.stats.respawnCount &
    "|stats.stormTripped=" & $rep.stats.stormTripped &
    "|stats.stormBackoffLevel=" & $rep.stats.stormBackoffLevel &
    "|stats.sinceLastCoverageAdmits=" & $rep.stats.sinceLastCoverageAdmits &
    "|stats.sinceLastCrashIters=" & $rep.stats.sinceLastCrashIters &
    "|stats.crashCount=" & $rep.stats.crashCount &
    "|stats.totalMutationOps=" & $rep.stats.totalMutationOps &
    "|stats.cullCount=" & $rep.stats.cullCount &
    "|stats.operatorPulls=" & opPullsStr &
    "|stats.provenanceCounts=" & provStr &
    "|corpusHash=" & $h

suite "R27 determinism: fuzz[T] decomposition must reproduce the pre-refactor trajectory":

  test "fixed seed 424242, 300 iterations":
    # Captured from the pre-refactor `fuzz[T]` monolith at commit 0cc32a6
    # (rfc-fuzzer-nextgen), before any R27 collaborator was extracted.
    let fp = fingerprint(424242'u64, 300)
    check fp == "iterations=300|coverageHits=28|corpusLen=8|crashes=27|timedOut=false|droppedSeeds=0|dictLen=87|totalMutationOps=627|stats.execs=300|stats.corpusSize=8|stats.coverageEdges=28|stats.respawnCount=0|stats.stormTripped=false|stats.stormBackoffLevel=0|stats.sinceLastCoverageAdmits=183|stats.sinceLastCrashIters=1|stats.crashCount=27|stats.totalMutationOps=627|stats.cullCount=17|stats.operatorPulls=4.690634365795028,4.57926115443476,4.05507246210057,2.9730255769644547,3.066962922574455,3.05478542083394,4.532113671170199,6.38147775901399,|stats.provenanceCounts=4,0,0,0,|corpusHash=9187963311723698617"

  test "fixed seed 7, 150 iterations (a second seed/budget point)":
    # Same provenance as above — commit 0cc32a6, pre-R27.
    let fp = fingerprint(7'u64, 150)
    check fp == "iterations=150|coverageHits=27|corpusLen=8|crashes=12|timedOut=false|droppedSeeds=0|dictLen=57|totalMutationOps=283|stats.execs=150|stats.corpusSize=8|stats.coverageEdges=27|stats.respawnCount=0|stats.stormTripped=false|stats.stormBackoffLevel=0|stats.sinceLastCoverageAdmits=73|stats.sinceLastCrashIters=0|stats.crashCount=12|stats.totalMutationOps=283|stats.cullCount=8|stats.operatorPulls=4.306143537352539,3.6017310198573003,3.686701839180994,3.8387974654969526,4.453835072588232,4.487104089407573,4.2424966819981655,4.716377264512058,|stats.provenanceCounts=2,0,1,0,|corpusHash=3245867094147137454"
