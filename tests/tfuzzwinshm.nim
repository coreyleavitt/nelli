## RFC-fuzzer-nextgen E4b: Windows shm coverage transport — the
## `CreateFileMapping`/`MapViewOfFile` counterpart to
## `tests/tfuzzworkerprocess.nim`'s POSIX "N>1 via shm" suite (E2b C3), now
## reached through `fuzzworker.nim`'s Windows `spawnWorkerProcess`/
## `runWorkerLoopAndExit` (E4a C2). Same shape as `tests/tfuzzwinworker.nim`
## (E4a C2): a `when defined(windows)` suite that RUNS natively on the
## `fuzzer-windows` CI leg (this file is `tfuzz*`-glob-discovered),
## build-checked only on this host via `dt-crosswin.sh` — no local Windows
## RUN channel exists (`docs/RFC-fuzzer-nextgen.windows-capability.md`) —
## plus a smaller `when defined(posix)` parity suite proving the SAME shm
## round-trip contract on this (`dt-bounded.sh`-run) platform, mirroring
## `tfuzzwinworker.nim`'s own "smaller, focused parity companion" style
## rather than re-deriving `tfuzzworkerprocess.nim`'s exhaustive POSIX
## coverage.
##
## A THIRD, platform-neutral section (no `when` guard at all) pins
## `shmWinName` — the ONE pure naming-transform function `nelli_shm.c`'s
## Windows `CreateFileMapping` arm calls to turn a POSIX-style `"/nelli_..."`
## shm name into the Windows kernel-object name it actually opens — directly,
## on POSIX, via `dt-bounded.sh`. That piece of the Windows mechanism gets
## genuine RED-GREEN coverage rather than trusting it un-exercised until a
## CI push (see `nelli_shm.c`'s module doc comment for why this one function
## is deliberately compiled unconditionally).
##
## One `fuzz(...)` call site per COMPILED binary (see
## `tests/tfuzzworkerprocess.nim`'s module doc comment for the full
## discriminating argument): the `when defined(windows)`/`when defined(posix)`
## suites below are mutually exclusive at compile time, so any one actual
## build still has exactly one call site, even though the source has two.
import std/[unittest, options, os]
import nelli
import nelli/[datasource, rng, serialize]

disableParamFiltering()

# --- the ONE naming function, pinned on every platform (E4b) ---------------

suite "RFC-fuzzer-nextgen E4b - the shared Windows shm naming transform":
  test "shmWinName strips the leading POSIX '/' and prefixes 'Local\\' -- the SAME transform nelli_shm.c's CreateFileMapping arm calls for real":
    check shmWinName("/nelli_e2bc3_1234") == "Local\\nelli_e2bc3_1234"
    check shmWinName("/nelli_g4c2both_cov_1") == "Local\\nelli_g4c2both_cov_1"

  test "shmWinName is idempotent-shaped even without a leading slash (defensive; every real caller in this codebase always passes one)":
    check shmWinName("nelli_noslash_5678") == "Local\\nelli_noslash_5678"

# --- portable reconstruction-sentinel property, shared by both suites ------
#
# Mirrors tfuzzworkerprocess.nim's own sentinel exactly (branch-on-n-mod-2
# for disjoint coverage edges between two chosen inputs, embed
# `rebuildCounter` in the always-taken crash message for the reconstruction
# proof) plus ONE `{.covercmp.}` comparison up front, so this single call
# site also exercises the cmp-log shm channel (RFC-fuzzer-nextgen G4 C2,
# now portable via the same `nelli_shm.c` widening) without a second `fuzz`
# registration.
var rebuildCounter = 0
proc sentinelStrategy(lo, hi: int): Strategy[int] =
  inc rebuildCounter
  integers(lo, hi)

proc sentinelProp(n: int) {.cover, covercmp.} =
  if n == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"
  if n mod 2 == 0:
    if n >= 25: discard else: discard
  else:
    if n <= -25: discard else: discard
  doAssert false, "rebuildCounter=" & $rebuildCounter

proc drawUntil(lo, hi: int; seedBase: uint64; pred: proc(n: int): bool): tuple[val: int, choices: ChoiceSeq] =
  ## Draw a value matching `pred` through the REAL `integers(lo, hi)`
  ## strategy (never hand-build a `ChoiceNode` — replay must stay
  ## strategy-valid). Identical to tfuzzworkerprocess.nim's own helper.
  for attempt in 0'u64 ..< 10_000'u64:
    var ds = newDataSource(initSplitMix64(seedBase + attempt))
    let v = integers(lo, hi).generate(ds)
    if pred(v): return (v, ds.recorded)
  doAssert false, "could not draw a value matching the predicate"

when defined(windows):
  import std/winlean   # `Handle`/`closeHandle` -- see tfuzzworkerprocess.nim's
                        # own direct `import std/posix` for the same pattern.

  suite "fuzz: Windows CreateFileMapping shm coverage transport (RFC-fuzzer-nextgen E4b)":
    test "N>1 via shm: a persistent CreateProcess'd worker's SECOND input has INDEPENDENTLY VALID coverage":
      # DELIBERATE PIN (mirrors tfuzzworkerprocess.nim's own E2b C3 pin,
      # ported to Windows): before E4b, a Windows worker's coverage stayed
      # the zero-value default no matter what — there was no transport at
      # all. `runWorkerLoopAndExit`'s new `$NELLI_COV_SHM` reset/publish
      # wiring lifts that: a SINGLE persistent worker servicing TWO inputs
      # that hit DISJOINT coverage edges now publishes EACH one
      # independently, matching what a fresh single-shot process would have
      # observed for that input alone.
      rebuildCounter = 0
      discard fuzz(sentinelStrategy(-50, 50), sentinelProp,
                   FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      check rebuildCounter == 1   # the parent's own construction

      let (vA, choicesA) = drawUntil(-50, 50, 11'u64, proc(n: int): bool = n mod 2 == 0 and n >= 25)
      let (vB, choicesB) = drawUntil(-50, 50, 22'u64, proc(n: int): bool = n mod 2 != 0 and n <= -25)

      let refA = inProcessTarget(sentinelProp).run(vA)
      let refB = inProcessTarget(sentinelProp).run(vB)
      check refA.coverage.counters != refB.coverage.counters   # sanity: distinguishable edges

      let shmName = "/nelli_e4b_" & $getCurrentProcessId()
      let probe = shmProbe(shmName)

      putEnv("NELLI_WORKER_MAX_INPUTS", "2")
      let (procH, threadH, inH, outH) = spawnWorkerProcess(id, "", shmName)
      delEnv("NELLI_WORKER_MAX_INPUTS")

      writeFrame(inH, toBytes(choicesA))
      let f1 = readFrame(outH)
      check f1.isSome
      # read-before-redispatch (E2b's own invariant, ported unchanged): the
      # worker's per-input publish for A already completed inside
      # `dispatch` -- BEFORE it wrote the result frame -- so this read is
      # race-free, the same invariant a real Orchestrator relies on.
      let covA = probe.read()

      writeFrame(inH, toBytes(choicesB))
      let f2 = readFrame(outH)
      check f2.isSome
      let covB = probe.read()

      discard closeHandle(inH); discard closeHandle(outH)
      let (exitCode, _) = reapWorker(procH, threadH)
      check exitCode == 0

      check covA.counters == refA.coverage.counters   # input A's own snapshot, not stale
      check covB.counters == refB.coverage.counters   # input B's own snapshot, not A's, not a union

    test "a worker with $NELLI_COV_SHM unset publishes nothing (opt-in, default off, no prior-transport regression)":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (_, choices) = drawUntil(-50, 50, 33'u64, proc(n: int): bool = n mod 2 == 0)

      let (procH, threadH, inH, outH) = spawnWorkerProcess(id, "")   # no covShm, no cmpShm
      writeFrame(inH, toBytes(choices))
      let frameOpt = readFrame(outH)
      check frameOpt.isSome
      discard closeHandle(inH); discard closeHandle(outH)
      let (exitCode, _) = reapWorker(procH, threadH)
      check exitCode == 0
      # Nothing to read back -- no shm segment was ever asked for by this run.

    test "$NELLI_CMP_SHM: a worker running a {.covercmp.}'d comparison publishes the observed/constant operand pair":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (vC, choicesC) = drawUntil(-50, 50, 55'u64, proc(n: int): bool = n mod 2 == 0 and n >= 25)

      let cmpShmName = "/nelli_e4b_cmp_" & $getCurrentProcessId()
      let (procH, threadH, inH, outH) = spawnWorkerProcess(id, "", "", cmpShmName)
      writeFrame(inH, toBytes(choicesC))
      let frameOpt = readFrame(outH)
      check frameOpt.isSome
      let entries = shmReadCmpLog(cmpShmName)
      discard closeHandle(inH); discard closeHandle(outH)
      let (exitCode, _) = reapWorker(procH, threadH)
      check exitCode == 0

      check entries.len == 1
      check entries[0].kind == clkInt
      check entries[0].op == coEq
      check (entries[0].lhsInt == uint64(vC) or entries[0].rhsInt == uint64(vC))
      check (entries[0].lhsInt == 0xDEADBEEF'u64 or entries[0].rhsInt == 0xDEADBEEF'u64)

    test "newProcessWorker[T] now gets REAL coverage via shm (E4b lifts the zero-coverage default) -- an Orchestrator sees covered edges after admit":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (_, choices) = drawUntil(-50, 50, 44'u64, proc(n: int): bool = n mod 2 == 0 and n >= 25)

      var frontier = newCoverageFrontier()
      let worker = newProcessWorker[int](id)
      let orch = newOrchestrator(worker, frontier)
      let obs = orch.run(choices)
      check obs.verdict == vInteresting
      check obs.coverage.counters.len > 0
      let admitResult = admit(orch, choices, obs)
      check admitResult.admitted
      check frontier.coveredEdges > 0

when defined(posix):
  import std/posix

  suite "fuzz: POSIX fork+exec shm coverage transport, portable-entry parity check (RFC-fuzzer-nextgen E4b)":
    # A smaller, focused parity companion to tfuzzworkerprocess.nim's
    # exhaustive POSIX suite (which already covers this exact shm N>1
    # contract in full) -- this suite's job is narrower: prove the SAME
    # `$NELLI_COV_SHM` reset/publish contract this file's Windows suite
    # proves, through the SAME call site, so both platforms are
    # demonstrably exercising an identical observable behavior.
    test "N>1 via shm through the REAL fuzz(...) call site: a persistent worker's SECOND input has independently valid coverage":
      rebuildCounter = 0
      discard fuzz(sentinelStrategy(-50, 50), sentinelProp,
                   FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      check rebuildCounter == 1

      let (vA, choicesA) = drawUntil(-50, 50, 111'u64, proc(n: int): bool = n mod 2 == 0 and n >= 25)
      let (vB, choicesB) = drawUntil(-50, 50, 222'u64, proc(n: int): bool = n mod 2 != 0 and n <= -25)
      let refA = inProcessTarget(sentinelProp).run(vA)
      let refB = inProcessTarget(sentinelProp).run(vB)
      check refA.coverage.counters != refB.coverage.counters

      let shmName = "/nelli_e4b_posix_" & $getCurrentProcessId()
      let probe = shmProbe(shmName)

      putEnv("NELLI_WORKER_MAX_INPUTS", "2")
      let (pid, inFd, outFd) = spawnWorkerProcess(id, "", shmName)
      delEnv("NELLI_WORKER_MAX_INPUTS")

      writeFrame(inFd, toBytes(choicesA))
      let f1 = readFrame(outFd)
      check f1.isSome
      let covA = probe.read()

      writeFrame(inFd, toBytes(choicesB))
      let f2 = readFrame(outFd)
      check f2.isSome
      let covB = probe.read()

      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      check covA.counters == refA.coverage.counters
      check covB.counters == refB.coverage.counters
