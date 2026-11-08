## RFC-fuzzer-nextgen R53 (code review): a `spawnWorkerProcess` failure
## occurring AFTER `newProcessWorker`'s POSIX submit closure has already
## called `shmHoldCmpLog(cmpShmName)` must not leak that segment.
##
## R12 made the cross-process cmp-log live; the R12 follow-up (see
## `tests/tfuzzcmplogshmleak.nim`) added the per-spawn `shmUnlinkCmpLog`
## reclaim, but only on the SUCCESS path -- right after this spawn's own
## `shmReadCmpLog` completes (fuzzworker.nim ~665-666). Between the hold
## (fuzzworker.nim ~653) and that point sits `spawnWorkerProcess` itself,
## which can raise for real: `pipe()`/`fork()` failure under fd/process
## pressure being the POSIX case `tests/tfuzzworkerprocess.nim`'s R23 suite
## already proves reachable (a tightened `RLIMIT_NOFILE` forces a genuine
## `pipe()` EMFILE). Before this fix, that exception skipped straight over
## the success-path unlink, leaving the freshly-held (and thus, per
## `shmHoldCmpLog`'s own R47 contract, freshly-CREATED) segment behind in
## `/dev/shm` for the rest of the campaign -- one leaked segment per failed
## submit, contradicting the "does not accumulate one segment per
## iteration" invariant `newProcessWorker`'s own doc comment states.
##
## This suite reuses `tests/tfuzzworkerprocess.nim`'s RLIMIT_NOFILE-to-EMFILE
## technique to provoke a REAL `spawnWorkerProcess` failure, and
## `tests/tfuzzcmplogshmleak.nim`'s `/dev/shm` nelli-entry counting idiom to
## observe whether that failure leaks. It drives `newProcessWorker[T]`'s
## actual `submit` directly (not through a multi-iteration `fuzz(...)`
## campaign) because the induced spawn failure is a genuine unhandled
## `OSError` that would abort a `fuzz(...)` campaign outright rather than
## being absorbed as a crash `Observation` -- `spawnWorkerProcess` failing
## is a harness/environment fault, not a finding about the property under
## test.
##
## POSIX-only (gated at the suite level, matching
## `tests/tfuzzcmplogshmleak.nim`'s own platform gate) -- the leak this
## proves is POSIX-specific; a Windows named section dies with its last
## handle regardless (see `shmUnlinkCmpLog`'s own doc for why Windows needs
## no counterpart).
##
## Exactly ONE `fuzz(...)` macro call site, first in the file -- see
## `tests/tfuzzcmplogshmleak.nim`'s module doc for why (a re-exec'd worker
## child replays the whole binary's earlier top-level code before it can
## even check whether it matches its OWN call-site id). The second test
## below reuses that SAME call-site id directly via `newProcessWorker`,
## exactly as `tests/tfuzzworkerprocess.nim`'s own "DoD #6" test does --
## the induced spawn failure never forks at all, so no second worker
## process, and no second re-exec path, is ever in play.

import std/[unittest, os, strutils]
import nelli
import nelli/[datasource, rng]

when defined(posix):
  import std/posix

disableParamFiltering()

when defined(posix):
  proc countNelliShmEntries(): int =
    ## Mirrors `tests/tfuzzcmplogshmleak.nim`'s own helper -- see there for
    ## why this deliberately does not import `db.nim`'s internals.
    if not dirExists("/dev/shm"): return 0
    for kind, p in walkDir("/dev/shm", relative = false):
      if kind == pcFile and extractFilename(p).startsWith("nelli_"):
        inc result

proc spawnfailProbeGate(x: int) {.cover, covercmp.} =
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

when defined(posix):
  suite "RFC-fuzzer-nextgen R53 -- a failed spawnWorkerProcess does not leak the held cmp-log shm segment":
    test "establish a real fuzz call-site id via a small processIsolation campaign":
      let report = fuzz(integers(0, 0xFFFFFFFF), spawnfailProbeGate,
                        FuzzSettings(seed: 13'u64, maxIterations: 3,
                                     executor: ExecutorConfig(processIsolation: true)))
      check report.iterations == 3

    test "spawnWorkerProcess failing (EMFILE via tightened RLIMIT_NOFILE) after shmHoldCmpLog leaves /dev/shm unchanged (R53)":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      let before = countNelliShmEntries()

      # Same technique as tests/tfuzzworkerprocess.nim's R23 suite: tighten
      # this process's own RLIMIT_NOFILE to one short of what a fresh
      # pipe() needs, so spawnWorkerProcess's first fallible syscall fails
      # deterministically with EMFILE -- no timing/ordering dependence, and
      # safe to lower/restore within this one test process (RLIMIT_NOFILE
      # is per-process, unlike RLIMIT_NPROC).
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
        let worker = newProcessWorker[int](id)
        # spawnWorkerProcess fails before `input` is ever touched (it's
        # only written to the child's stdin pipe AFTER a successful spawn),
        # so an empty ChoiceSeq is fine -- this submit never gets that far.
        discard worker.submit(@[])
      except OSError as e:
        raised = true
        msg = e.msg
      finally:
        # Restore FIRST, unconditionally, before any further check that
        # might itself need an fd -- a failed restore would poison every
        # later test in this process.
        check setrlimit(RLIMIT_NOFILE, oldLimit) == 0

      check raised
      check "pipe" in msg   # confirms this genuinely hit spawnWorkerProcess's pipe() failure, not something else

      let after = countNelliShmEntries()
      # Before the R53 fix: shmHoldCmpLog's freshly-created segment was
      # never reclaimed on this failure path, so `after == before + 1`.
      # After the fix: the except-and-reraise cleanup at the spawn call
      # site unlinks it before the OSError propagates, so the count must
      # come back to exactly what it was.
      check after == before
else:
  suite "RFC-fuzzer-nextgen R53 -- a failed spawnWorkerProcess does not leak the held cmp-log shm segment":
    test "skipped on non-POSIX (no /dev/shm; Windows named mappings self-clean on last handle close)":
      skip()
