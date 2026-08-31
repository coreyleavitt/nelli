## RFC-fuzzer-nextgen E4a (C2): the Windows `CreateProcess` persistent-worker
## round-trip through the REAL `fuzz(...)` macro call site — the Windows
## counterpart to `tests/tfuzzworkerprocess.nim`'s POSIX fork+exec suite.
##
## One call site only (see that file's module doc comment for why: a
## re-exec'd/re-spawned worker child runs the WHOLE binary's top-level code
## up to the matching call site before it can even check whether it matches,
## so a second site in the same file would cascade). Both platform suites
## below share the SAME reconstruction-sentinel property — proving
## `fuzz(...)`'s worker-mode entry (E1's captured-construction-closure
## re-entry, exec-based and platform-neutral by design — see
## `fuzzmacro.nim`'s `when defined(posix) or defined(windows)` gate) genuinely
## re-executes construction from scratch on EITHER platform, not just POSIX.
##
## The portable parts (imports, `disableParamFiltering`, the sentinel
## strategy/property, `drawUntil`) carry no OS-specific syscalls — they
## compile and RUN identically under `dt-bounded.sh` (POSIX, verified here)
## and cross-compile clean under `dt-crosswin.sh` (Windows). The Windows
## suite itself is BUILD-checked only on this (Linux) dev host — no local
## Windows RUN channel exists (`docs/rfc/0003-fuzzer-nextgen.windows-capability.md`);
## it is RUN-verified via the CI push-and-wait channel this glob (`tfuzz*`)
## is discovered by on `windows-latest`.

import std/[unittest, options, strutils]
import nelli
import nelli/[datasource, rng, serialize]

# See tests/tfuzzworkerprocess.nim's module doc: a re-exec'd/re-spawned
# worker child is launched with `--nelli-worker=<id>` on argv, which
# `std/unittest` would otherwise treat as a test/suite-name glob filter and
# silently match nothing.
disableParamFiltering()

var rebuildCounter = 0
  ## The reconstruction sentinel (see tests/tfuzzworkerprocess.nim for the
  ## full discriminating argument: a genuinely fresh worker process starts
  ## this at 0 and reports exactly 1 after its own single construction call;
  ## an inherited/COW state would report 2+). Windows has no `fork` at all —
  ## `CreateProcess` always starts a brand-new process image — so THIS file
  ## does not need to discriminate "real exec" from "a naive COW fork" the
  ## way the POSIX file does; the sentinel here instead proves the simpler
  ## but still load-bearing fact that worker-mode re-entry runs construction
  ## AT ALL (not zero times, not skipped) exactly once per spawn.
proc sentinelStrategy(lo, hi: int): Strategy[int] =
  inc rebuildCounter
  integers(lo, hi)

proc sentinelProp(n: int) {.cover.} =
  if n == -13:
    # Death-before-answer trigger. Unlike tfuzzworkerprocess.nim's
    # `kill(getpid(), SIGSEGV)` (needed there to bypass Nim's checked-build
    # nil-access instrumentation reliably), the property under test here is
    # `observationForDeath`'s EXIT-CODE decode path (`GetExitCodeProcess`),
    # not a signal/NTSTATUS decode — so a plain, 100%-portable `quit(7)`
    # (exits before this worker's dispatch loop ever reaches `writeFrame`)
    # exercises the exact same "the pipe read comes back empty, not a hang"
    # contract without depending on any platform's raw-fault semantics.
    quit(7)
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

  suite "fuzz: Windows CreateProcess persistent worker (RFC-fuzzer-nextgen E4a C2)":
    test "a real CreateProcess'd worker round-trips one framed input and proves genuine reconstruction":
      rebuildCounter = 0
      discard fuzz(sentinelStrategy(-50, 50), sentinelProp,
                   FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      check rebuildCounter == 1   # the parent's own construction

      let (_, choices) = drawUntil(-50, 50, 0xC0FFEE'u64, proc(n: int): bool = n != -13)
      let (procH, threadH, inH, outH) = spawnWorkerProcess(id, "")
      writeFrame(inH, toBytes(choices))
      let frameOpt = readFrame(outH)
      check frameOpt.isSome
      let obs = decodeObservationLite[void](frameOpt.get)
      discard closeHandle(inH); discard closeHandle(outH)
      let (exitCode, signal) = reapWorker(procH, threadH)
      check signal == 0
      check exitCode == 0

      check obs.verdict == vInteresting
      check obs.crash.isSome
      check obs.crash.get.kind == ckException
      # The reconstruction sentinel: the CHILD's rebuilt strategy reports
      # rebuildCounter == 1 -- proof worker-mode re-entry genuinely ran
      # `sentinelStrategy` (not zero times, not skipped, not re-using
      # anything from the parent, which has no COW-shared state to re-use
      # in the first place since CreateProcess never forks).
      check "rebuildCounter=1" in obs.crash.get.message

    test "a worker that dies before answering is reported vCrashed via GetExitCodeProcess, not a hang":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (_, deathChoices) = drawUntil(-50, 50, 1'u64, proc(n: int): bool = n == -13)

      let (procH, threadH, inH, outH) = spawnWorkerProcess(id, "")
      writeFrame(inH, toBytes(deathChoices))
      # The child `quit(7)`s inside `dispatch()`, before it ever reaches
      # `writeFrame` -- the parent must see a CLEAN failure (no frame at
      # all), not a hang and not a malformed-but-present frame.
      let frameOpt = readFrame(outH)
      check frameOpt.isNone
      discard closeHandle(inH); discard closeHandle(outH)

      let (exitCode, signal) = reapWorker(procH, threadH)
      check signal == 0
      check exitCode == 7

      let obs = observationForDeath[void](exitCode)
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckWinException
      check obs.crash.get.code == 7'u32

when defined(posix):
  import std/posix

  suite "fuzz: POSIX fork+exec persistent worker, portable-entry parity check (RFC-fuzzer-nextgen E4a C2)":
    # A smaller, focused parity companion to tfuzzworkerprocess.nim's
    # exhaustive POSIX suite (which already covers the fork-vs-exec
    # discriminating sentinel, coverage file-dump, shm N>1, and the
    # SIGSEGV/ckSignal death path in full). This suite's job is narrower:
    # prove the SAME quit(7)-triggered "died before answering" contract this
    # file's Windows suite proves, so both platforms are demonstrably
    # exercising an identical observable behavior through ONE shared call
    # site -- here decoded as `ckExitCode` (POSIX's `WEXITSTATUS`), the
    # direct POSIX analog of the Windows suite's `ckWinException` decode of
    # the SAME `quit(7)`.
    test "a real fork+exec'd worker round-trips one framed input and proves genuine reconstruction":
      rebuildCounter = 0
      discard fuzz(sentinelStrategy(-50, 50), sentinelProp,
                   FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      check rebuildCounter == 1

      let (_, choices) = drawUntil(-50, 50, 0xC0FFEE'u64, proc(n: int): bool = n != -13)
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
      check "rebuildCounter=1" in obs.crash.get.message

    test "a worker that dies before answering (quit, not a signal) is reported vCrashed via WEXITSTATUS, not a hang":
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let (_, deathChoices) = drawUntil(-50, 50, 1'u64, proc(n: int): bool = n == -13)

      let (pid, inFd, outFd) = spawnWorkerProcess(id, "")
      writeFrame(inFd, toBytes(deathChoices))
      let frameOpt = readFrame(outFd)
      check frameOpt.isNone
      discard close(inFd); discard close(outFd)

      let (exitCode, signal) = reapWorker(pid)
      check signal == 0        # a plain `quit(7)`, not a signal -- WIFSIGNALED is false
      check exitCode == 7

      let obs = observationForDeath[void](exitCode, signal)
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckExitCode
      check obs.crash.get.exitCode == 7
