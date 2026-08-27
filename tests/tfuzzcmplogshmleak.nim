## RFC-fuzzer-nextgen R12 follow-up (code review): the per-spawn cmp-log shm
## segments `newProcessWorker`/`externalTarget` now create (fuzz.nim,
## fuzzworker.nim — see `tests/tfuzzcmplogprocess.nim`'s module doc for the
## original R12 fix) must NOT leak on POSIX. `nelli_shm.c`'s `generation`
## word only ever increments once a channel has published, so each spawn
## needs a FRESH, never-before-published segment name (the earlier draft of
## this fix reused one name per `Worker[T]`/`Target[T]` lifetime and read
## back STALE data from an earlier spawn — `tests/tfuzzcbuild.nim` catches
## that class of bug directly). But a fresh name per spawn means a fresh
## `shm_open`-backed file under `/dev/shm` per spawn too — unlike a Windows
## named section (destroyed automatically once its last handle closes, the
## whole reason `shmHoldCmpLog` exists to pre-attach before a producer does),
## a POSIX shm segment persists until explicitly `shm_unlink`'d. Without a
## per-spawn unlink, a 100k-iteration campaign (an ordinary size for this
## tool) would leave roughly 100k small segments in `/dev/shm` — typically a
## tmpfs sized at a fraction of RAM — a more damaging regression than the
## dark-consumer gap R12 closed.
##
## The fix: `coverage.nim`'s `shmUnlinkCmpLog` (POSIX-only) — `shm_open`
## materializes as an ordinary file at `/dev/shm/<name>` (the same fact
## `db.nim`'s `sweepStaleShmSegments` startup backstop documents for ITS OWN
## reclaim), so an ordinary `removeFile` there IS `shm_unlink`. Called from
## `newProcessWorker` (fuzzworker.nim, POSIX) and `externalTarget` (fuzz.nim,
## `when defined(posix)`) right after each spawn's own `shmReadCmpLog`
## completes — unlinking a still-mapped segment is safe (POSIX `unlink` only
## removes the directory entry; the underlying object survives until every
## mapping/fd referencing it is gone), and a failed `removeFile` degrades to
## a leaked segment (for `db.nim`'s startup sweep to catch on a LATER
## campaign) rather than raising and failing an otherwise-successful run.
##
## This suite proves the reclaim empirically: run a real, multi-iteration
## `processIsolation: true` campaign (genuine re-exec'd child processes, the
## same proof technique `tests/tfuzzprocessisolation.nim`/
## `tests/tfuzzcmplogprocess.nim` use) and assert the count of nelli-owned
## `/dev/shm` entries does NOT grow with iteration count — the exact
## assertion that would have caught the leak this follow-up closes (a
## pre-fix binary would show growth equal to `maxIterations`; this asserts
## growth stays a small constant instead).
##
## Exactly ONE `fuzz(...)` macro call site, first in the file — see
## `tests/tfuzzprocessisolation.nim`'s module doc for why: a re-exec'd
## worker child replays the WHOLE binary's earlier top-level code before it
## can even check whether it matches its OWN call-site id. POSIX-only (the
## leak this proves is POSIX-specific — Windows named mappings self-clean on
## last handle close, per `shmHoldCmpLog`'s own doc), gated at the suite
## level, matching `tests/tfuzzcmplogshm.nim`'s own platform-gate shape.

import std/[unittest, os, strutils]
import nelli
import nelli/[datasource, rng]

disableParamFiltering()

when defined(posix):
  proc countNelliShmEntries(): int =
    ## Mirrors `db.nim`'s `sweepStaleShmSegments` prefix-only scoping
    ## (`nelliShmPrefix = "nelli_"`) rather than importing it: this test
    ## deliberately does not depend on `db.nim`'s own internals, only on the
    ## SAME observable fact its module doc states (a POSIX `shm_open`
    ## segment is an ordinary file under `/dev/shm`).
    if not dirExists("/dev/shm"): return 0
    for kind, p in walkDir("/dev/shm", relative = false):
      if kind == pcFile and extractFilename(p).startsWith("nelli_"):
        inc result

proc leakProbeGate(x: int) {.cover, covercmp.} =
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

when defined(posix):
  suite "RFC-fuzzer-nextgen R12 follow-up — cmp-log shm segments are reclaimed, not leaked, on POSIX":
    test "a 60-iteration processIsolation: true + enableI2S: true campaign does not accumulate one /dev/shm segment per iteration":
      let before = countNelliShmEntries()
      let report = fuzz(integers(0, 0xFFFFFFFF), leakProbeGate,
                        FuzzSettings(seed: 7'u64, maxIterations: 60, guidance: GuidanceConfig(enableI2S: true), executor: ExecutorConfig(processIsolation: true)))
      let after = countNelliShmEntries()
      check report.iterations == 60   # the campaign genuinely ran all 60 spawns
      # Before the follow-up fix, every spawn's cmp-log segment was left
      # behind permanently (no unlink anywhere in this codebase) -- a
      # 60-spawn campaign would show `after - before == 60` (one
      # `/dev/shm/nelli_worker_cmp_<pid>_<n>` per iteration, never
      # reclaimed). The per-spawn `shmUnlinkCmpLog` call reclaims each
      # segment before the NEXT spawn even starts, so growth here must stay
      # a small constant, never proportional to `maxIterations`.
      check after - before < 10
else:
  suite "RFC-fuzzer-nextgen R12 follow-up — cmp-log shm segments are reclaimed, not leaked, on POSIX":
    test "skipped on non-POSIX (no /dev/shm; Windows named mappings self-clean on last handle close)":
      skip()
