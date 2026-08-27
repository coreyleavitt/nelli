## RFC-fuzzer-nextgen R12 (code review, HIGH, verified): closes the
## cross-process cmp-log CONSUMER gap. Track G's RedQueen-style
## input-to-state guidance had a fully built, correct PRODUCER
## (`nelli_cov.c`'s `covercmp` instrumentation / `pt_cmplog_*`,
## `nelli_shm.c`'s publish channel) and an already-tested read-back side
## (`coverage.nim`'s `shmReadCmpLog`/`shmHoldCmpLog`) but NO production
## code ever connected them for the cross-process case: `shmHoldCmpLog`
## had zero call sites in `src/`, `newProcessWorker` (fuzzworker.nim, both
## platforms) hardcoded `cmpShm = ""`, `externalTarget`/`fuzzBinary` never
## set `$NELLI_CMP_SHM`, and `Observation[T]` had nowhere to carry a
## worker-captured log even if one had been read back. The only thing
## exercising the shm transport was tests calling `shmReadCmpLog`/
## `shmHoldCmpLog` directly — standing in for an orchestrator role no
## production code played. `tests/tfuzzi2s.nim`'s in-process path
## (`currentCmpLog()` threadvar, gated on `settings.enableI2S`) was live
## and stays untouched by this fix.
##
## The fix (`fuzz.nim`, `fuzzworker.nim`): `Observation[T]` gained
## `cmpLog*: Option[seq[CmpLogEntry]]` — `none` for every in-process path
## (unchanged), `some(entries)` for a producer that captured the log
## OUT-OF-PROCESS (a process `Worker[T]` reading its child's
## `$NELLI_CMP_SHM` publish; `externalTarget` reading an instrumented
## external binary's own publish). `newProcessWorker` (both platforms) now
## requests a real cmp-log shm segment via `spawnWorkerProcess`'s existing
## `cmpShm` parameter and reads it back via `shmReadCmpLog`, pre-attached
## via `shmHoldCmpLog` the same way `shmHoldCoverage` already avoids the
## Windows named-mapping-lifetime race. `fuzz*[T]`'s `captureCmpLog`
## (fuzz.nim) now prefers `obs.cmpLog` whenever `.isSome`, falling back to
## the in-process `currentCmpLog()` threadvar only when it's `none` — the
## `.isSome` signal (not `.len > 0`) matters: an out-of-process run that
## genuinely logged zero comparisons must not fall through to a threadvar
## that could hold STALE data left by an earlier in-process `fuzz()` call
## sharing the same OS thread (nelli's own test binaries run many `fuzz()`
## calls back to back in one thread).
##
## This suite proves the closed gap the way the finding demands: operands
## captured IN A CHILD PROCESS reaching the PARENT's mutation path, driven
## through a REAL `fuzz(...)` campaign with `processIsolation: true` AND
## `enableI2S: true` — not a test that calls `shmReadCmpLog` directly (that
## already exists, in `tests/tfuzzcmplogshm.nim`/`tests/tfuzzcbuild.nim`,
## and is exactly the gap this closes). The property is the SAME
## `0xDEADBEEF`-gate headline shape `tests/tfuzzi2s.nim` already uses to
## prove the in-process I2S path solves a 1-in-4-billion gate ordinary
## mutation cannot reasonably pass in 200 iterations — here, EVERY
## iteration additionally runs in a genuinely re-exec'd worker process
## (`tests/tfuzzprocessisolation.nim`'s own proof technique), so solving it
## is only possible if the child's logged operand pair genuinely rode the
## shm channel back to the parent's `mutateIRI2SReplace` call.
##
## Exactly ONE `fuzz(...)` macro call site, and it comes FIRST in the file
## — see `tests/tfuzzprocessisolation.nim`'s module doc for why: a
## re-exec'd worker child replays the WHOLE binary's earlier top-level code
## before it can even check whether it matches its OWN call-site id.

import std/[unittest, os]
import nelli
import nelli/[datasource, rng, choice]

disableParamFiltering()

proc deadbeefGateIsolated(x: int) {.cover, covercmp.} =
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

suite "RFC-fuzzer-nextgen R12 — cross-process cmp-log reaches the parent's mutation path":
  var report: FuzzReport

  test "processIsolation: true + enableI2S: true solves the 0xDEADBEEF gate via real child-process worker runs":
    report = fuzz(integers(0, 0xFFFFFFFF), deadbeefGateIsolated,
                  FuzzSettings(seed: 42'u64, maxIterations: 200, guidance: GuidanceConfig(enableI2S: true), executor: ExecutorConfig(processIsolation: true)))
    # Behavioral proof, mirroring tfuzzi2s.nim's in-process headline: random
    # mutation alone cannot reasonably hit a 1-in-4-billion constant in 200
    # iterations (tfuzzi2s.nim's own "enableI2S left at false" sibling test
    # pins exactly that, same strategy/seed/budget) -- both edges being hit
    # here, under FULL process isolation, means the I2S operator actually
    # received the real operand pair.
    check report.coverageHits == 2   # both the "hit" and "miss" edges

  test "the report's own dictionary carries the exact constant only the CHILD's logged comparison could supply":
    # Direct proof (not just the behavioral outcome above): `harvestDictionary`
    # is called from inside `captureCmpLog` (fuzz.nim), which before this fix
    # always fell through to `currentCmpLog()` for an isolated campaign --
    # the PARENT's own thread-local buffer, never touched when every actual
    # run happens in a child process, so the dictionary would have stayed
    # permanently empty regardless of how many iterations ran. Finding
    # `0xDEADBEEF` here is only possible if `Observation.cmpLog` genuinely
    # carried the child's own shm-published operand pair back across the
    # process boundary.
    var found = false
    for e in report.dictionary.entries:
      if e.kind == dvInt and e.intVal == toInt128(0xDEADBEEF'i64):
        found = true
    check found

  test "iterations and crash-free bookkeeping stayed sane across every re-exec'd submit":
    # Cheap sanity companion to the two proofs above, reusing the same
    # already-completed campaign (no second fuzz(...) call site): a
    # 200-iteration process-isolated campaign that silently died partway
    # through (a bootstrap-breaker trip, an unhandled worker crash) could
    # otherwise present a deceptively small `coverageHits`/empty dictionary
    # for the WRONG reason.
    check report.iterations == 200
    check report.irCrashes.len == 0    # the gate property never raises -- only branches
