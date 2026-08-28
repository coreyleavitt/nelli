## RFC-fuzzer-nextgen E2a (C1): the POSIX persistent worker — argv dispatch,
## genuine fork+exec self-re-exec, and the versioned framed pipe round-trip.
##
## POSIX-only (guarded by `when defined(posix)`, mirroring
## `tests/tfuzzexternal.nim`). Unlike `tfuzzexternal.nim` this needs no C
## compiler: the "external" process here is a fresh fork+exec of THIS SAME
## compiled test binary, launched in `--nelli-worker=<id>` mode
## (`fuzzworker.nim`'s `spawnWorkerProcess`). RFC-fuzzer-nextgen E4a (C2):
## the Windows `CreateProcess` counterpart lives in its own file,
## `tests/tfuzzwinworker.nim` — genuinely separate rather than an in-file
## `when defined(windows)` branch, since every test here reaches for raw
## `posix.pipe`/`kill`/`SIGSEGV`/`Pid`, not just the portable
## `spawnWorkerProcess`/`readFrame`/`writeFrame` surface both platforms share.
##
## The central assertion is the RECONSTRUCTION SENTINEL (RFC round-3
## feasibility fix, DoD #3): a plain COW `fork()` WITHOUT `exec()` would
## satisfy a weaker test (the child is a distinct address space either way),
## so the pin has to discriminate "genuinely re-ran construction in a fresh
## process" from "inherited the parent's already-constructed state". See the
## `sentinelStrategy`/`sentinelProp` pair below for how.

import std/[unittest, options, strutils, os]
import nelli
import nelli/[datasource, rng, serialize, binaryio]

# `std/unittest` treats EVERY argv parameter as a test-name/suite-name glob
# filter (`ensureInitialized`, unittest.nim) — so a re-exec'd worker child,
# launched with `--nelli-worker=<id>` on argv (the RFC's explicit "argv
# call-site ID, not an env var" dispatch), would otherwise have unittest
# silently filter OUT every `test:` block (nothing matches that glob),
# meaning the worker-mode branch embedded in a test body never runs. This
# is a real, non-obvious systems obstacle E2a hits precisely because worker
# dispatch reuses the SAME compiled test binary as its own worker process.
# Disabling unittest's own param filtering (our library's test suites never
# rely on it — `dt.sh` never passes filter args) is the fix.
disableParamFiltering()

when defined(posix):
  import std/posix

  # --- the reconstruction sentinel --------------------------------------------
  #
  # `rebuildCounter` is a process-local global, incremented once per
  # EVALUATION of `sentinelStrategy(...)` (not once per process — a fresh
  # process starts it at its compile-time initial value, 0, regardless of
  # what value the PARENT process's own copy holds).
  #
  # The parent's own front-door `fuzz(...)` call (below) evaluates
  # `sentinelStrategy` exactly once as its own argument — matching
  # `tfuzzmacro.nim`'s existing C5 pin ("the macro's own immediate call
  # constructed once") — so by the time the parent spawns a worker,
  # `rebuildCounter == 1` IN THE PARENT'S MEMORY.
  #
  # A REAL fork+exec child starts with its OWN fresh `rebuildCounter == 0`
  # (exec replaces the address space entirely — nothing is inherited). When
  # the worker loop services its one input, it re-runs
  # `sentinelStrategy(...)` from scratch (E1's `runWorkerReentry`
  # contract) — `rebuildCounter` becomes exactly `1` in the CHILD's memory.
  #
  # A NAIVE COW `fork()` WITHOUT `exec()` — the shortcut the DoD explicitly
  # forbids — would instead COPY the parent's memory at fork time
  # (`rebuildCounter` already `1`, inherited); one more construction call
  # would push it to `2`. So "the child reports exactly 1, not 2" is the
  # discriminator: it can ONLY happen if the child's `rebuildCounter` began
  # this run at 0 — i.e., a genuinely fresh process, not an inherited one.
  #
  # `sentinelProp` ALWAYS "crashes" (an unconditional `doAssert false` at
  # the end) and embeds `rebuildCounter` in the message — piggy-backing DoD
  # #3's sentinel on the SAME crash-message wire field DoD #4 needs anyway,
  # so the reconstruction proof rides the real result-frame payload, not a
  # test-only side channel. It ALSO branches on `n` first (mirroring
  # `tfuzzworker.nim`/`tfuzzmacro.nim`'s own `branchyProp`), so two
  # well-chosen inputs hit DISJOINT coverage edges before the crash — what
  # C2's coverage/N=1 tests need — WITHOUT a second `fuzz(...)` call site.
  #
  # Deliberately only ONE call site exists in this whole file. A worker
  # spawned for call-site id K must, by construction, run every line of
  # code the binary would normally execute UP TO reaching K (including any
  # OTHER `fuzz(...)` call site that happens to sit earlier in program
  # flow) before it can even check whether it matches K — so a SECOND call
  # site would make every spawn in a LATER test cascade into re-running
  # every EARLIER fuzz-call-site test's full body (each of which spawns and
  # blocks on its OWN nested worker). One call site sidesteps this
  # entirely: it sits at the top of the first test, so any worker matches
  # and exits there, before any later test's code could run at all.
  var rebuildCounter = 0
  proc sentinelStrategy(lo, hi: int): Strategy[int] =
    inc rebuildCounter
    integers(lo, hi)

  proc sentinelProp(n: int) {.cover.} =
    if n == -13:
      # C3's process-death trigger. A genuine nil-pointer DEREFERENCE is
      # NOT reliably an uncatchable OS signal here: Nim's default (checked)
      # build inserts a runtime nil-access check that raises `NilAccessDefect`
      # — a Defect `observeInProcess`'s `except Defect` already catches,
      # which would just produce an ordinary (non-crash-isolating) result
      # frame and defeat this test's premise. `kill(getpid(), SIGSEGV)`
      # delivers the signal directly, bypassing Nim's exception machinery
      # entirely — genuinely uncatchable, exactly DoD #4's "segfault" case:
      # the worker process dies mid-dispatch, never reaching `writeFrame`.
      discard kill(getpid(), SIGSEGV)
    if n mod 2 == 0:
      if n >= 25: discard else: discard
    else:
      if n <= -25: discard else: discard
    doAssert false, "rebuildCounter=" & $rebuildCounter

  proc drawUntil(lo, hi: int; seedBase: uint64; pred: proc(n: int): bool): tuple[val: int, choices: ChoiceSeq] =
    ## Draw a value matching `pred` through the REAL `integers(lo, hi)`
    ## strategy (never hand-build a `ChoiceNode` — replay must stay
    ## strategy-valid).
    for attempt in 0'u64 ..< 10_000'u64:
      var ds = newDataSource(initSplitMix64(seedBase + attempt))
      let v = integers(lo, hi).generate(ds)
      if pred(v): return (v, ds.recorded)
    doAssert false, "could not draw a value matching the predicate"

  var covFileCtr = 0
  proc freshCovPath(): string =
    inc covFileCtr
    getTempDir() / ("nelli_e2a_cov_" & $getCurrentProcessId() & "_" & $covFileCtr & ".bin")

  suite "fuzz: POSIX persistent worker (RFC-fuzzer-nextgen E2a C1/C2)":
    test "a real fork+exec'd worker round-trips one framed input and proves genuine reconstruction":
      rebuildCounter = 0
      # The parent's own front door: registers the worker entry for this
      # call site AND constructs `sentinelStrategy` once in the PARENT.
      discard fuzz(sentinelStrategy(-50, 50), sentinelProp,
                   FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      check rebuildCounter == 1   # parent's own construction, per tfuzzmacro.nim's C5 pin

      # Build a valid choice-sequence input for `integers(-50, 50)`.
      var ds = newDataSource(initSplitMix64(0xC0FFEE'u64))
      discard integers(-50, 50).generate(ds)
      let choices = ds.recorded

      # Spawn a REAL fork+exec'd worker (self-re-exec of this binary) AFTER
      # the parent's own construction already ran — the ordering the
      # sentinel depends on.
      let (pid, inFd, outFd) = spawnWorkerProcess(id, "")
      writeFrame(inFd, toBytes(choices))

      let frameOpt = readFrame(outFd)
      check frameOpt.isSome
      let obs = decodeObservationLite[void](frameOpt.get)

      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      check obs.verdict == vInteresting
      check obs.crash.isSome
      check obs.crash.get.kind == ckException
      # The reconstruction sentinel: the CHILD's rebuilt strategy reports
      # rebuildCounter == 1 (a fresh process's first-ever construction) —
      # NOT 2 (what an inherited-from-parent COW fork would report).
      check "rebuildCounter=1" in obs.crash.get.message

    test "a worker's coverage rides the file-dump path and matches an equivalent in-process run":
      # Reuses test 1's ALREADY-registered call site (`nelliLastFuzzCallSiteId`,
      # process-global, populated once test 1 ran its front door) — no NEW
      # `fuzz(...)` call site here, so no cascade (see the module doc above).
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      var ds = newDataSource(initSplitMix64(0xAAAA'u64))
      let val = integers(-50, 50).generate(ds)
      let choices = ds.recorded

      let covPath = freshCovPath()
      let (pid, inFd, outFd) = spawnWorkerProcess(id, covPath)
      writeFrame(inFd, toBytes(choices))
      let frameOpt = readFrame(outFd)
      check frameOpt.isSome
      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      check fileExists(covPath)
      let dumped = parseCoverageMap(readFile(covPath))
      let reference = inProcessTarget(sentinelProp).run(val)
      check dumped.counters == reference.coverage.counters
      removeFile(covPath)

    test "a pre-placed symlink at the coverage dump's .tmp path is refused, not followed (RFC-fuzzer-nextgen R20)":
      # CWE-377/CWE-59: models a local attacker on a shared host who
      # predicts (or, pre-R20, computed outright from a visible pid+counter)
      # the worker's coverage dump path and pre-places a symlink there aimed
      # at a file they want clobbered. The child's `writeFileNoFollow`
      # (fuzzworker.nim) opens that `.tmp` path with `O_CREAT|O_EXCL` — since
      # the symlink already occupies it, the open fails with `EEXIST` and
      # NOTHING is ever written through it, regardless of what the symlink
      # points at. The worker itself does NOT crash over this (the refusal
      # is caught in `runWorkerLoopAndExit` and treated as "coverage not
      # published this round", the same acceptable degradation the
      # once-per-process dump gate already accepts elsewhere) — it still
      # answers its result frame normally, so an attacker cannot turn a
      # symlink plant into a denial of service against the worker either.
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      let (_, choices) = drawUntil(-50, 50, 42'u64, proc(n: int): bool = n != -13)

      let covPath = freshCovPath()
      let tmpPath = covPath & ".tmp"
      let victimPath = getTempDir() / ("nelli_r20_victim_" & $getCurrentProcessId() & ".txt")
      let victimContent = "do-not-touch"
      writeFile(victimPath, victimContent)
      createSymlink(victimPath, tmpPath)   # pre-attack: tmpPath -> victimPath

      let (pid, inFd, outFd) = spawnWorkerProcess(id, covPath)
      writeFrame(inFd, toBytes(choices))
      let frameOpt = readFrame(outFd)
      check frameOpt.isSome    # the refused dump does not crash the worker
      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      let obs = decodeObservationLiteSafe[void](frameOpt.get)
      check obs.verdict == vInteresting   # sentinelProp's ordinary doAssert-false outcome, unaffected

      # The attack's actual target: the victim file must be untouched.
      check readFile(victimPath) == victimContent
      # And no coverage was ever published at the intended path -- the
      # rename step never ran, so nothing but the attacker's own symlink
      # sits at `tmpPath`, and `covPath` itself was never created.
      check not fileExists(covPath)

      removeFile(tmpPath); removeFile(victimPath)

    test "N>1 via shm: a persistent worker's SECOND input has INDEPENDENTLY VALID coverage (RFC-fuzzer-nextgen E2b C3)":
      # DELIBERATE PIN CHANGE (the one intentional assertion flip E2b makes,
      # called out explicitly): this test used to characterize the OPPOSITE
      # claim — on the E2a interim file-dump transport, `dumpCoverageOnce`'s
      # once-per-process gate meant a worker's SECOND input observed
      # STALE/absent coverage, forcing E2a's shipped N=1 recycle-every-input
      # policy. E2b's shm transport (C1: double-buffered publish + generation
      # word; C2: per-input reset/republish, signal-safe) lifts that
      # constraint: `runWorkerLoopAndExit` now resets+republishes via shm
      # once per input when `$NELLI_COV_SHM` is set (`shmResetCoverage`/
      # `shmPublishCoverage`, coverage.nim), so a SINGLE persistent worker
      # servicing TWO inputs that hit DISJOINT coverage edges now publishes
      # EACH one independently — matching what a fresh single-shot process
      # would have observed for that input alone, proving N>1 validity.
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      let (vA, choicesA) = drawUntil(-50, 50, 11'u64, proc(n: int): bool = n mod 2 == 0 and n >= 25)
      let (vB, choicesB) = drawUntil(-50, 50, 22'u64, proc(n: int): bool = n mod 2 != 0 and n <= -25)

      let refA = inProcessTarget(sentinelProp).run(vA)
      let refB = inProcessTarget(sentinelProp).run(vB)
      check refA.coverage.counters != refB.coverage.counters   # sanity: distinguishable edges

      let shmName = "/nelli_e2bc3_" & $getCurrentProcessId()
      let probe = shmProbe(shmName)

      putEnv("NELLI_WORKER_MAX_INPUTS", "2")
      let (pid, inFd, outFd) = spawnWorkerProcess(id, "", shmName)
      delEnv("NELLI_WORKER_MAX_INPUTS")

      writeFrame(inFd, toBytes(choicesA))
      let f1 = readFrame(outFd)
      check f1.isSome
      # read-before-redispatch: the worker's per-input publish for A already
      # completed (inside `dispatch` -> `shmPublishCoverage`, BEFORE it wrote
      # the result frame) by the time this readFrame returns, so this read
      # is race-free — the same invariant a real Orchestrator relies on.
      let covA = probe.read()

      writeFrame(inFd, toBytes(choicesB))
      let f2 = readFrame(outFd)
      check f2.isSome
      let covB = probe.read()

      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      check covA.counters == refA.coverage.counters   # input A's own snapshot, not stale
      check covB.counters == refB.coverage.counters   # input B's own snapshot, not A's, not a union

    test "read-before-redispatch: a delayed probe.read() keeps observing generation N until this test itself redispatches -- the worker cannot have published N+1 (RFC-fuzzer-nextgen round-3 pin, RFC ~332-342)":
      # The RFC pins a named contract, not just a mechanism: the shm double-
      # buffer's `generation` word (nelli_shm.c) is a single acquire-check,
      # not a full seqlock -- its never-torn guarantee rests on the
      # ORCHESTRATOR completing `probe.read()` for input K strictly BEFORE
      # the SAME worker is ever dispatched input K+1. That is true here
      # because `runWorkerLoopAndExit` (fuzzworker.nim) blocks inside
      # `readFrame(nelliWorkerInFd)` at the top of every loop iteration --
      # it cannot reach its own `shmPublishCoverage` call for a SECOND
      # generation until this test writes a second input frame, which it
      # deliberately withholds below.
      #
      # This is the real worker/shm pairing (genuine fork+exec, genuine
      # generation-word protocol via `shmProbe`), not a fabricated sequence
      # -- the previous test already sets up this exact N>1-via-shm
      # scenario; this one adds the DELAY and the negative assertion the RFC
      # calls for, rather than only reading immediately after each frame.
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      let (vA, choicesA) = drawUntil(-50, 50, 11'u64, proc(n: int): bool = n mod 2 == 0 and n >= 25)
      let (vB, choicesB) = drawUntil(-50, 50, 22'u64, proc(n: int): bool = n mod 2 != 0 and n <= -25)

      let refA = inProcessTarget(sentinelProp).run(vA)
      let refB = inProcessTarget(sentinelProp).run(vB)
      check refA.coverage.counters != refB.coverage.counters   # sanity: distinguishable edges

      let shmName = "/nelli_e2bc3_rbr_" & $getCurrentProcessId()
      let probe = shmProbe(shmName)

      putEnv("NELLI_WORKER_MAX_INPUTS", "2")
      let (pid, inFd, outFd) = spawnWorkerProcess(id, "", shmName)
      delEnv("NELLI_WORKER_MAX_INPUTS")

      writeFrame(inFd, toBytes(choicesA))
      let f1 = readFrame(outFd)
      check f1.isSome   # generation 1 published (BEFORE the frame, per E2b's own ordering)

      # Deliberately DELAY: do not write input B yet. As long as this test
      # withholds it, the worker is stuck inside its blocking `readFrame` for
      # input B and has no code path to reach a second publish -- so ANY
      # number of reads issued here, however long the "delay" before them,
      # must all observe the identical generation-1 snapshot.
      let delayedRead1 = probe.read()
      let delayedRead2 = probe.read()
      check delayedRead1.counters == refA.coverage.counters
      check delayedRead2.counters == refA.coverage.counters   # unchanged: no redispatch occurred between these two reads
      check delayedRead2.counters != refB.coverage.counters   # explicitly NOT generation 2's data

      # Only now does this test redispatch -- the read-before-redispatch
      # order the RFC pins as what makes the single acquire-check safe.
      writeFrame(inFd, toBytes(choicesB))
      let f2 = readFrame(outFd)
      check f2.isSome
      let covB = probe.read()
      check covB.counters == refB.coverage.counters   # generation DID advance, now that a redispatch actually happened

      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

    test "a worker that segfaults makes the pipe read fail cleanly, mapped to vCrashed (DoD #4a)":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (_, deathChoices) = drawUntil(-50, 50, 1'u64, proc(n: int): bool = n == -13)

      let (pid, inFd, outFd) = spawnWorkerProcess(id, "")
      writeFrame(inFd, toBytes(deathChoices))
      # The child dies INSIDE dispatch(), before it ever reaches
      # `writeFrame` — so the parent must see a CLEAN failure (no frame at
      # all), not a hang and not a malformed-but-present frame.
      let frameOpt = readFrame(outFd)
      check frameOpt.isNone
      discard close(inFd); discard close(outFd)

      let (exitCode, signal) = reapWorker(pid)
      check signal == 11                        # SIGSEGV

      let obs = observationForDeath[void](exitCode, signal)
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckSignal
      check obs.crash.get.signal == 11

    test "persistent-loop geometry: a crash on input K does not wedge the pipe, and a fresh worker continues the campaign (DoD #4b)":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (_, okChoices) = drawUntil(-50, 50, 2'u64, proc(n: int): bool = n mod 2 != 0 and n > -25 and n != -13)
      let (_, deathChoices) = drawUntil(-50, 50, 3'u64, proc(n: int): bool = n == -13)

      # One worker, forced (test-only knob) to service more than one input,
      # so a crash on the SECOND input is observed within a SINGLE worker's
      # pipe lifetime — the geometry DoD #4b is about, not the shipped N=1
      # per-submit policy (which sidesteps this by construction: C4 spawns
      # fresh every submit regardless).
      putEnv("NELLI_WORKER_MAX_INPUTS", "0")     # unbounded
      let (pid, inFd, outFd) = spawnWorkerProcess(id, "")
      delEnv("NELLI_WORKER_MAX_INPUTS")

      writeFrame(inFd, toBytes(okChoices))
      let okFrame = readFrame(outFd)
      check okFrame.isSome                       # input 1: answered normally

      writeFrame(inFd, toBytes(deathChoices))
      let deadFrame = readFrame(outFd)
      check deadFrame.isNone                      # input 2 (K): clean failure, not a hang
      discard close(inFd); discard close(outFd)
      let (_, signal) = reapWorker(pid)
      check signal == 11

      # The campaign continues: a FRESH worker (a new spawn, the ordinary
      # per-submit policy) still answers a further input normally.
      let (_, moreChoices) = drawUntil(-50, 50, 4'u64, proc(n: int): bool = n mod 2 != 0 and n > -25 and n != -13)
      let (pid2, inFd2, outFd2) = spawnWorkerProcess(id, "")
      writeFrame(inFd2, toBytes(moreChoices))
      let revived = readFrame(outFd2)
      check revived.isSome
      discard close(inFd2); discard close(outFd2)
      let (exitCode2, signal2) = reapWorker(pid2)
      check signal2 == 0
      check exitCode2 == 0

    test "an Orchestrator drives a process Worker[T] interchangeably with in-process — same observable outcomes (DoD #6)":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      let (_, okChoices) = drawUntil(-50, 50, 5'u64, proc(n: int): bool = n mod 2 == 0 and n >= 25)
      let (_, deathChoices) = drawUntil(-50, 50, 6'u64, proc(n: int): bool = n == -13)

      var frontier = newCoverageFrontier()
      let worker = newProcessWorker[int](id)
      let orch = newOrchestrator(worker, frontier)

      # A normal (non-death) input: sentinelProp always ends in `doAssert
      # false`, so this is ALSO a crash-detection proof, flowing through the
      # FULL Worker[T]/Orchestrator seam this time (not the raw pipe calls
      # C1-C3 used directly) — the same `ckException` outcome C1 proved.
      let obs1 = orch.run(okChoices)
      check obs1.verdict == vInteresting
      check obs1.crash.isSome
      check obs1.crash.get.kind == ckException
      let admit1 = admit(orch, okChoices, obs1)
      check admit1.admitted           # first coverage this frontier has ever seen
      check frontier.coveredEdges > 0

      # A process-death input: the SAME vCrashed outcome C3 proved directly
      # against the pipe, now reached via `orch.run` — the Orchestrator seam
      # never sees an exception, never blocks indefinitely; it just gets an
      # ordinary (if unwelcome) `Observation` back, exactly like an
      # in-process `Orchestrator` would for a `Defect` it catches.
      let obs2 = orch.run(deathChoices)
      check obs2.verdict == vCrashed
      check obs2.crash.isSome
      check obs2.crash.get.kind == ckSignal
      check obs2.crash.get.signal == 11

      # Same observable outcome as an in-process Orchestrator over the SAME
      # (strategy, property) pair and input, modulo isolation: the verdict
      # and crash KIND agree (the in-process path reports the ORIGINAL
      # exception as ckException, since it never actually dies — that IS
      # the isolation difference the RFC's "modulo isolation" caveats).
      var inProcFrontier = newCoverageFrontier()
      let inProcOrch = newOrchestrator(sentinelStrategy(-50, 50), inProcessTarget(sentinelProp), inProcFrontier)
      let inProcObs = inProcOrch.run(okChoices)
      check inProcObs.verdict == obs1.verdict
      check inProcObs.crash.get.kind == obs1.crash.get.kind
      check inProcObs.coverage.counters == obs1.coverage.counters

    test "readFrame rejects a truncated frame":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      # Write a header claiming a 100-byte payload but supply none, then
      # close — the reader must raise FrameError, not hang or silently
      # return an empty/zeroed frame.
      var hdr: seq[byte]
      hdr.putU32(0x464C454E'u32)
      hdr.putU32(1'u32)
      hdr.putU32(100'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      discard close(pipeFds[1])
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0])

    test "readFrame rejects a bad-magic frame":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      var hdr: seq[byte]
      hdr.putU32(0xDEADBEEF'u32)
      hdr.putU32(1'u32)
      hdr.putU32(0'u32)
      var checksum: seq[byte]
      checksum.putU32(0'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      discard posix.write(pipeFds[1], addr checksum[0], checksum.len)
      discard close(pipeFds[1])
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0])

    test "readFrame rejects an unsupported version":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      var hdr: seq[byte]
      hdr.putU32(0x464C454E'u32)
      hdr.putU32(99'u32)
      hdr.putU32(0'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      discard close(pipeFds[1])
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0])

    test "readFrame rejects a length prefix over the max frame size, without attempting the read":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      var hdr: seq[byte]
      hdr.putU32(0x464C454E'u32)
      hdr.putU32(1'u32)
      hdr.putU32(uint32(nelliMaxFrameBytes) + 1'u32)
      discard posix.write(pipeFds[1], addr hdr[0], hdr.len)
      # Deliberately do NOT close the write end and do NOT supply the
      # (impossibly large) payload: if `readFrame` tried to read that many
      # bytes it would block forever. The bound must fire on the length
      # prefix alone, before any further read.
      expect(FrameError):
        discard readFrame(pipeFds[0])
      discard close(pipeFds[0]); discard close(pipeFds[1])

    test "writeFrame/readFrame round-trip a small payload exactly":
      var pipeFds: array[2, cint]
      discard posix.pipe(pipeFds)
      let payload = @[1'u8, 2'u8, 3'u8, 255'u8, 0'u8]
      writeFrame(pipeFds[1], payload)
      let got = readFrame(pipeFds[0])
      check got.isSome
      check got.get == payload
      discard close(pipeFds[0]); discard close(pipeFds[1])

    test "decodeObservationLiteSafe folds a checksum-valid but out-of-range Verdict into vCrashed, not an exception (R16)":
      # Simulates a version-skewed re-exec (the orchestrator binary replaced
      # on disk mid-campaign, so a freshly exec'd worker's
      # `encodeObservationLite` no longer agrees with THIS process's
      # `decodeObservationLite`) or a corrupted worker: the FRAME checksum is
      # valid -- proving the bytes crossed the pipe intact -- but the
      # Observation-lite payload inside is semantically invalid. `200` is not
      # a valid `Verdict` ordinal (`Verdict` has 6 cases, 0..5), so
      # `decodeObservationLite`'s `Verdict(getU8(...))` cast raises
      # `RangeDefect` -- the exact failure mode R16 names.
      var payload: seq[byte]
      payload.putU8(200'u8)
      payload.putBool(false)        # no crash
      payload.putRawStr("garbage")  # message

      let wire = encodeFrame(payload)
      let length = decodeFrameHeader(wire[0 ..< 12])
      let recovered = decodeFrameBody(length, wire[12 .. ^1])   # succeeds: checksum IS valid
      check recovered == payload

      var raised = false
      var obs: Observation[void]
      try:
        obs = decodeObservationLiteSafe[void](recovered)
      except Exception:
        raised = true
      check not raised
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckException

    test "decodeObservationLiteSafe folds a checksum-valid but truncated length-prefixed field into vCrashed too (R16)":
      # Same premise, different underlying decode failure: a `DbCorrupt`
      # (binaryio.nim) from a length prefix that claims more bytes than the
      # payload actually carries -- the OTHER failure mode R16 names.
      var payload: seq[byte]
      payload.putU8(uint8(ord(vOk)))
      payload.putBool(false)
      payload.putU64(999'u64)   # claims a 999-byte message; none follow

      let wire = encodeFrame(payload)
      let length = decodeFrameHeader(wire[0 ..< 12])
      let recovered = decodeFrameBody(length, wire[12 .. ^1])
      check recovered == payload

      var raised = false
      var obs: Observation[void]
      try:
        obs = decodeObservationLiteSafe[void](recovered)
      except Exception:
        raised = true
      check not raised
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckException

    test "spawnWorkerProcess surfaces a genuine spawn failure (pipe() exhaustion) as an OSError, not a hang or a miscategorized crash observation (R23)":
      # R23: every OTHER spawn in this suite uses an always-succeeding
      # `posix.pipe()` and a real, exec'able self-binary -- spawn FAILURE
      # itself is never exercised. `spawnWorkerProcess`'s FIRST fallible
      # syscall is `posix.pipe(inPipe)` (fuzzworker.nim ~266); this
      # provokes that call to genuinely fail by lowering this PROCESS's own
      # `RLIMIT_NOFILE` soft limit to "just enough for what's already open,
      # plus one" -- one short of the two fds a pipe() needs, so it fails
      # with EMFILE deterministically, no timing/ordering dependence.
      #
      # `RLIMIT_NOFILE` is a per-process limit (unlike `RLIMIT_NPROC`, which
      # is per-EUID and would leak into any OTHER test suite running
      # concurrently in this same container/sweep) -- safe to lower and
      # restore within a single test process without disturbing siblings.
      proc countOpenFds(): int =
        for kind, p in walkDir("/proc/self/fd"): inc result

      let openBefore = countOpenFds()
      var oldLimit: RLimit
      check getrlimit(RLIMIT_NOFILE, oldLimit) == 0
      var tight = RLimit(rlim_cur: openBefore + 1, rlim_max: oldLimit.rlim_max)
      check setrlimit(RLIMIT_NOFILE, tight) == 0

      var raised = false
      var msg = ""
      try:
        discard spawnWorkerProcess(nelliLastFuzzCallSiteId, "")
      except OSError as e:
        raised = true
        msg = e.msg
      finally:
        # Restore FIRST, unconditionally, before any further check that
        # might itself need an fd (temp files, echo, etc.) -- a failed
        # restore would poison every later test in this process.
        check setrlimit(RLIMIT_NOFILE, oldLimit) == 0

      check raised
      check "pipe" in msg

    test "a real exec-into-a-nonexistent-path death (the shape spawnWorkerProcess's child produces via exitnow(127) on execvpe failure) is classified vCrashed/ckExitCode by reapWorker/observationForDeath (R23)":
      # HISTORICAL NOTE (superseded by R49 below, kept as a lower-level pin):
      # at the time this test was written, `spawnWorkerProcess` could not be
      # driven to an EXEC failure through its public surface at all -- the
      # exec target was unconditionally `getAppFilename()` (self-re-exec),
      # with no parameter or env override, so there was no seam to point it
      # at a bad path without a `src/` change. What WAS honestly testable
      # without one is the CONSUMING half of that failure mode: fork+exec
      # into a path that does not exist, mirroring EXACTLY what
      # `spawnWorkerProcess`'s own child does between `fork()` and
      # `execvpe()` (arm the pdeath signal, then
      # `discard execvpe(...); exitnow(127)` on failure -- see
      # fuzzworker.nim ~283-296) -- and prove `reapWorker`/
      # `observationForDeath` (the real functions a process `Worker[T]`
      # calls on ANY dead-before-answering worker, spawn-exec-failed or
      # not) classify that death as a clean `vCrashed`/`ckExitCode`
      # observation, never a hang and never miscategorized as a signal
      # death.
      #
      # R49 (code review, LOW) added `spawnWorkerProcess`'s own `execPath`
      # parameter, closing the seam this note describes -- see the
      # dedicated end-to-end test right after this one, which drives the
      # SAME classification through the real public API instead of a
      # hand-rolled fork+execvpe. This test is kept as-is: a lower-level
      # characterization of `reapWorker`/`observationForDeath` alone,
      # independent of `spawnWorkerProcess`'s own fork/pipe/argv plumbing.
      let pid = fork()
      if pid == 0:
        discard execvpe("/nelli-r23-does-not-exist".cstring,
                        allocCStringArray(@["/nelli-r23-does-not-exist"]),
                        allocCStringArray(newSeq[string]()))
        exitnow(127)   # exec failed -- the exact path spawnWorkerProcess's own child takes
      check int(pid) > 0
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 127

      let obs = observationForDeath[void](exitCode, signal)
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckExitCode
      check obs.crash.get.exitCode == 127

    test "spawnWorkerProcess's execPath override provokes a genuine exec failure, classified vCrashed/ckExitCode/127 end-to-end (R49)":
      # RFC-fuzzer-nextgen R49 (code review, LOW): unlike the R23 test above
      # (which hand-rolls fork+execvpe OUTSIDE `spawnWorkerProcess` because
      # that proc had no seam to reach a real exec failure), this drives the
      # REAL public API: `execPath` (new, optional, defaults to
      # `getAppFilename()` for every OTHER existing caller) points the exec
      # target at a path that cannot exist, so `spawnWorkerProcess`'s own
      # child takes its own genuine `exitnow(127)` branch -- fork succeeds
      # (`pid > 0`), `execvpe` fails, the child dies before ever reading its
      # input pipe.
      #
      # Deliberately does NOT write an input frame first (unlike a real
      # `Worker[T].submit`, which writes before reading): by the time this
      # process could write to `inFd`, the child -- the pipe's ONLY reader
      # -- is already gone (it never even reaches the point where it would
      # dup2/read), and writing to a pipe with no open read end raises
      # `SIGPIPE` (default-fatal; this codebase never installs it as
      # ignored) rather than the catchable `FrameError` a live-but-crashing
      # worker would produce. Skipping the write sidesteps that unrelated
      # hazard entirely while still exercising exactly what THIS finding is
      # about: `spawnWorkerProcess` (fork+exec) and the real consuming half
      # (`reapWorker`/`observationForDeath`) it feeds.
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (pid, inFd, outFd) =
        spawnWorkerProcess(id, "", execPath = "/nelli-r49-does-not-exist")
      check int(pid) > 0

      let frameOpt = readFrame(outFd)
      check frameOpt.isNone   # dead before ever answering -- never truncated/garbage
      discard close(inFd); discard close(outFd)

      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 127

      let obs = observationForDeath[void](exitCode, signal)
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckExitCode
      check obs.crash.get.exitCode == 127
else:
  # RFC-fuzzer-nextgen E4a (C2): genuinely POSIX-only, not just un-audited —
  # every test above reaches for raw `posix.pipe`/`kill`/`SIGSEGV`/`Pid`, not
  # merely the portable `spawnWorkerProcess`/`readFrame`/`writeFrame` surface
  # `fuzzworker.nim` now also exposes on Windows (`CreateProcess` + anonymous
  # inherited pipes). The Windows counterpart — the SAME reconstruction-
  # sentinel round-trip and death-detection contract, through the SAME real
  # `fuzz(...)` macro call-site path — lives in its own file,
  # `tests/tfuzzwinworker.nim` (also `tfuzz*`-glob-discovered, so both suites
  # run on their respective CI legs).
  echo "SKIP (posix-only; see tests/tfuzzwinworker.nim for the Windows CreateProcess counterpart): fork+exec persistent worker suite"
