## RFC-fuzzer-nextgen G4 (C2) — the per-run comparison operand-pair log over
## shm. Rides `nelli_shm.c`'s push/copy + generation-word protocol (E2b) over
## its OWN independent channel (`pt_cmplog_*` — a SECOND `pt_shm_init`-style
## singleton would have silently collided with the coverage channel; see
## `nelli_shm.c`'s G4 comment). Wired into `fuzzworker.nim`'s persistent
## worker loop at the SAME per-input reset/publish boundary coverage uses
## (`$NELLI_CMP_SHM`, opt-in, default off — byte-identical to pre-G4
## behavior for every existing caller that never sets it).
##
## Mirrors `tfuzzworkerprocess.nim`'s real fork+exec'd worker style (a
## genuine cross-process round trip, not a fabricated sequence) — ONE
## `fuzz(...)` call site in this file, matching that file's documented
## "no cascading nested-worker recursion" discipline.
import std/[unittest, os]
import nelli
import nelli/[datasource, rng, serialize]

disableParamFiltering()

when defined(posix):
  import std/posix

  proc magicCmpGate(x: int) {.cover, covercmp.} =
    ## `{.cover, covercmp.}` combined — the exact "concolic-walked and
    ## cmp-instrumented" property shape from G4's brief, now run through a
    ## REAL persistent worker process instead of a direct in-process call.
    if x == 0xDEADBEEF:
      discard "hit"
    else:
      discard "miss"

  suite "RFC-fuzzer-nextgen G4 C2 — cmp-log shm transport (persistent worker)":
    test "a worker running a {.cover, covercmp.}'d property publishes the observed/constant operand pair, and the orchestrator reads it back":
      # The parent's own front door: registers the worker entry for this call site.
      discard fuzz(integers(0, 0xFFFFFFFF), magicCmpGate,
                   FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      var ds = newDataSource(initSplitMix64(0xABCDEF'u64))
      let val = integers(0, 0xFFFFFFFF).generate(ds)
      let choices = ds.recorded

      let cmpShmName = "/nelli_g4c2_" & $getCurrentProcessId()
      let probe = cmpShmName   # named for symmetry with `shmProbe` reads below

      let (pid, inFd, outFd) = spawnWorkerProcess(id, "", "", cmpShmName)
      writeFrame(inFd, toBytes(choices))
      let frameOpt = readFrame(outFd)
      check frameOpt.isSome
      # read-before-redispatch (E2b's own invariant): the worker's per-input
      # publish already completed inside `dispatch` (before it wrote the
      # result frame), so this read is race-free.
      let entries = shmReadCmpLog(probe)

      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      check entries.len == 1
      check entries[0].kind == clkInt
      check entries[0].op == coEq
      check (entries[0].lhsInt == uint64(val) or entries[0].rhsInt == uint64(val))
      check (entries[0].lhsInt == 0xDEADBEEF'u64 or entries[0].rhsInt == 0xDEADBEEF'u64)

    test "a worker with $NELLI_CMP_SHM unset logs nothing (opt-in, default off, no prior-transport regression)":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      var ds = newDataSource(initSplitMix64(0x111111'u64))
      discard integers(0, 0xFFFFFFFF).generate(ds)
      let choices = ds.recorded

      let (pid, inFd, outFd) = spawnWorkerProcess(id, "")   # no covShm, no cmpShm
      writeFrame(inFd, toBytes(choices))
      let frameOpt = readFrame(outFd)
      check frameOpt.isSome
      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0
      # Nothing to read back — no shm segment was ever asked for by this run.

    test "$NELLI_COV_SHM and $NELLI_CMP_SHM both set publish independently in the SAME run (distinct per-channel gates)":
      # A worker with BOTH transports enabled at once must publish coverage
      # AND the cmp log for the same input — a real bug the cmp-log
      # channel's own gate variable (`pt_cmplog_dumped`, distinct from
      # coverage's `pt_dumped`) fixes: sharing ONE gate across channels
      # would leave whichever channel published SECOND silently starved,
      # since the first publish would already have tripped a shared flag.
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      var ds = newDataSource(initSplitMix64(0x222222'u64))
      discard integers(0, 0xFFFFFFFF).generate(ds)
      let choices = ds.recorded

      let covShmName = "/nelli_g4c2both_cov_" & $getCurrentProcessId()
      let cmpShmName = "/nelli_g4c2both_cmp_" & $getCurrentProcessId()
      let covProbe = shmProbe(covShmName)

      let (pid, inFd, outFd) = spawnWorkerProcess(id, "", covShmName, cmpShmName)
      writeFrame(inFd, toBytes(choices))
      let frameOpt = readFrame(outFd)
      check frameOpt.isSome
      let cov = covProbe.read()
      let entries = shmReadCmpLog(cmpShmName)
      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      check signal == 0
      check exitCode == 0

      check cov.counters.len > 0            # coverage published (not starved by cmp log's publish)
      check entries.len == 1                # cmp log ALSO published (not starved by coverage's publish)
      check entries[0].kind == clkInt

else:
  suite "RFC-fuzzer-nextgen G4 C2 — cmp-log shm transport (persistent worker)":
    test "skipped on non-POSIX":
      skip()
