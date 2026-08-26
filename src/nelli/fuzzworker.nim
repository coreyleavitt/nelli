## RFC-fuzzer-nextgen E2a: the POSIX persistent worker — argv dispatch, a
## versioned framed pipe protocol, and genuine fork+exec worker spawn.
##
## E1 (`fuzzmacro.nim`) proved worker-mode RE-ENTRY in-process: the same
## `fuzz(...)` call site that runs the front door also registers a closure
## (`nelliWorkerRegistry`) that re-runs the captured strategy/property
## construction from scratch. E2a makes that closure reachable from a REAL,
## separately-exec'd OS process instead of calling it in-process:
##
## - The orchestrator side (`spawnWorkerProcess`) fork+exec's a FRESH copy of
##   the CURRENT binary (`getAppFilename()`, self-re-exec — no separate
##   worker binary exists) with `--nelli-worker=<call-site-id>` on argv, wired
##   to two pipes on fixed fds (`nelliWorkerInFd`/`nelliWorkerOutFd`). This
##   mirrors `fuzz.nim`'s `runChild`: argv/env are allocated BEFORE `fork()`,
##   and the child touches nothing but raw POSIX syscalls between `fork()`
##   and `execvpe()` — no Nim GC/allocator runs in the not-yet-exec'd,
##   COW-shared address space.
## - The worker side (`nelliWorkerModeId`, parsed from argv at module load —
##   before ANY of the re-exec'd binary's own top-level code, including
##   `fuzz(...)` call sites, has run) is read by `fuzzmacro.nim`'s generated
##   code: the SAME `fuzz(...)` call site that would normally run the front
##   door instead calls `runWorkerLoopAndExit`, "double-serving" per the
##   RFC's resolution — no separate `nelli.workerMain` the user must call.
##
## Wire protocol: both input and result frames are
## `magic(u32) | version(u32) | len(u32) | payload | checksum(u32)`,
## mirroring `nelli_cov.c`'s PCOV dump format. `nelliMaxFrameBytes` bounds the
## length prefix BEFORE any attempt to read that many bytes, so a
## hostile/buggy/unbounded-recursive strategy fails loudly (`FrameError`)
## instead of wedging a fixed-size pipe buffer in an indefinite blocking
## read. A version mismatch is `FrameError` too — a worker cannot silently
## outlive a wire-format bump mid-campaign.
##
## Coverage does NOT ride the result frame (round-2 RFC text: "coverage
## rides the existing file-dump path... interim"). The result frame carries
## only `Verdict` + `Option[CrashInfo]` + the human `message` — a process
## `Worker[T]` reads the child's coverage back from `$NELLI_COV_FILE` after
## the child exits, the same file-dump convention `externalTarget` already
## uses for a C child, extended here to a Nim in-process property running
## inside the worker (`dumpCoverageToFile`, C2).
##
## RFC-fuzzer-nextgen E4a (C1): this module carries the PLATFORM-DEPENDENT
## glue over the PLATFORM-INDEPENDENT protocol (frame encode/decode, the
## observation-lite codec, argv dispatch, the bootstrap circuit-breaker
## policy, the Job-Object limit policy) factored into `./workerproto` — see
## that module's doc comment. `readFrame`/`writeFrame` on EITHER platform are
## thin raw-I/O wrappers around `workerproto`'s pure `decodeFrameHeader`/
## `decodeFrameBody`/`encodeFrame`; `spawnWorkerProcess` on EITHER platform
## builds its argv/env via `workerproto.workerArgv`/`workerEnv` instead of
## inlining that logic — one codec, two transports.
##
## RFC-fuzzer-nextgen E4a (C2): the Windows half. `when defined(posix)`
## below is fork+exec + POSIX pipes (E2a/E3a/E-cleanup, unchanged); the
## sibling `when defined(windows)` block is `CreateProcess` + anonymous
## inheritable pipes (no `fork` exists on Windows — the worker side always
## re-executes the captured construction from scratch, never inherits
## COW-shared memory). TRANSPORT-EQUIVALENCE DECISION: the RFC bullet names
## "named pipes"; this cycle uses anonymous pipes with inherited handles
## instead — the canonical `CreateProcess` stdio-redirection pattern,
## generalized to a dedicated (non-stdio) handle pair so worker-mode's own
## stray output can never corrupt the frame stream (matching WHY POSIX uses
## fixed fds 3/4 instead of 0/1/2, "1:1 with the POSIX fd design"). Same
## framed protocol, same verdict semantics as the POSIX pipe(2) pair; a
## named pipe would add naming/ACL surface with no benefit for a single
## parent-child relationship with no other client. Unlike POSIX's
## compile-time-fixed fd numbers, a Windows pipe handle's numeric value is
## only known after `CreatePipe` allocates it, so the child learns its two
## handle values via `NELLI_WORKER_IN_HANDLE`/`NELLI_WORKER_OUT_HANDLE` —
## two additional inherited environment variables, the closest Windows
## analog to POSIX's fixed-fd convention.
##
## RFC-fuzzer-nextgen E4b: coverage now rides the SAME shm transport as the
## POSIX side (`coverage.nim`'s `pt_shm_*`/`pt_cmplog_*` wrappers, now
## portable via `nelli_shm.c`'s `CreateFileMapping`/`MapViewOfFile` arm) —
## `runWorkerLoopAndExit` resets/publishes per input when `$NELLI_COV_SHM`/
## `$NELLI_CMP_SHM` are set, exactly mirroring the POSIX loop's own
## boundary. A Windows worker with NEITHER set still leaves
## `Observation.coverage` at its zero-value default (this platform never
## had a file-dump fallback to preserve, unlike POSIX's E2a interim). Job
## Object creation/limits are E4c — `spawnWorkerProcess` here does not
## create one; `workerproto.JobLimitPolicy`/`verdictForJobLimit` stay
## consumed only by their own tests until then.

import std/[os, options, strutils, times]
import ./fuzz, ./binaryio, ./serialize, ./workerproto
# RFC-fuzzer-nextgen E4a (C1): the framed-protocol pure decoders, the
# observation-lite codec, argv call-site-ID dispatch
# (`nelliWorkerModeId`/`nelliWorkerFlagPrefix`/`parseWorkerModeId`), the
# bootstrap circuit-breaker policy, and the Job-Object limit policy moved to
# the platform-independent leaf module `./workerproto` (frame/argv/env
# constants and types this module's own POSIX code below still uses
# directly, e.g. `FrameError`/`nelliMaxFrameBytes`/`workerArgv`) —
# re-exported here so every existing `import nelli`/`import nelli/fuzzworker`
# caller keeps the same surface.
export workerproto

when defined(posix):
  import std/posix

  proc readN(fd: cint; n: int): seq[byte] =
    ## Read up to exactly `n` bytes, retrying on a `EINTR`-interrupted or
    ## short read. Returns fewer than `n` bytes ONLY on EOF (the peer closed
    ## its write end) — `result.len == 0` is a clean boundary EOF, anything
    ## in between is a truncation the caller must treat as a protocol error.
    result = newSeq[byte](n)
    var off = 0
    while off < n:
      let r = posix.read(fd, addr result[off], n - off)
      if r < 0:
        if osLastError().int32 == EINTR: continue
        result.setLen(off)
        return
      elif r == 0:
        result.setLen(off)
        return
      off += r

  proc writeAll(fd: cint; data: seq[byte]): bool =
    ## Write every byte, retrying on `EINTR`/short writes. `false` on a hard
    ## error (e.g. `EPIPE` — the peer closed its read end; DoD #4b's clean
    ## write-side failure signal).
    var off = 0
    while off < data.len:
      let r = posix.write(fd, unsafeAddr data[off], data.len - off)
      if r < 0:
        if osLastError().int32 == EINTR: continue
        return false
      elif r == 0:
        return false
      off += r
    true

  proc readFrame*(fd: cint): Option[seq[byte]] =
    ## Read one framed message. `none` on a clean frame-boundary EOF (no
    ## bytes read at all — "no more input" / "the peer closed before writing
    ## anything"). Raises `FrameError` for a truncated header/body, a bad
    ## magic, an unsupported version, an oversized length, or a checksum
    ## mismatch — all decided by `workerproto`'s pure decoders; this is only
    ## the raw-fd read side (RFC-fuzzer-nextgen E4a C1).
    let hdr = readN(fd, 12)
    if hdr.len == 0: return none(seq[byte])
    let length = decodeFrameHeader(hdr)
    let body = readN(fd, length + 4)
    some(decodeFrameBody(length, body))

  proc writeFrame*(fd: cint; payload: seq[byte]) =
    ## Write one framed message. Raises `FrameError` if `payload` exceeds
    ## `nelliMaxFrameBytes` (`workerproto.encodeFrame` — never emit a frame a
    ## well-behaved reader would have to reject) or the underlying pipe
    ## write fails (broken pipe).
    if not writeAll(fd, encodeFrame(payload)):
      raise newException(FrameError, "frame: write failed (broken pipe)")

  # --- workers die with the orchestrator (RFC-fuzzer-nextgen E-cleanup C2) ----
  #
  # A persistent worker can be deep inside `dispatch` (running a fuzzed
  # input — including one that HANGS, the realistic case this guards
  # against) when its orchestrator dies (OOM-killed, Ctrl-C'd). Such a
  # worker never comes back around to notice anything about its parent —
  # not even a closed input pipe, since it isn't calling `read` on it at
  # that moment — so it would otherwise survive its orchestrator forever.
  # `PR_SET_PDEATHSIG` is the kernel-enforced backstop: armed in the child
  # BEFORE `execvpe` (the setting survives exec), the kernel delivers
  # `SIGKILL` to it the instant its parent process dies, regardless of what
  # the worker itself is doing at that moment. `PR_SET_CHILD_SUBREAPER`
  # (`setChildSubreaper`) is test/harness support only — it lets a test
  # observe a reparented grandchild's death via a genuine blocking
  # `waitpid` instead of polling `kill(pid, 0)` against a container's PID 1,
  # which may not reap orphans.
  proc prctl(option: cint; arg2, arg3, arg4, arg5: culong): cint
    {.importc: "prctl", header: "<sys/prctl.h>".}
  const
    PR_SET_PDEATHSIG = 1.cint
    PR_SET_CHILD_SUBREAPER = 36.cint

  proc armParentDeathSignal() =
    ## Called by a freshly forked CHILD, as early as possible (before any
    ## other syscall) — arms `SIGKILL` to be delivered by the kernel the
    ## moment THIS process's parent dies. Also covers the race where the
    ## parent died in the tiny window between `fork()` returning here and
    ## this call actually landing: if `getppid()` no longer matches the pid
    ## we were forked from, the parent is already gone, so this exits
    ## immediately rather than risk an unarmed orphan.
    let parentAtFork = getppid()
    discard prctl(PR_SET_PDEATHSIG, SIGKILL.culong, 0.culong, 0.culong, 0.culong)
    if getppid() != parentAtFork:
      exitnow(1)

  proc setChildSubreaper*() =
    ## Test/harness support (see the module doc above): marks the CALLING
    ## process a Linux "child subreaper" so an orphaned grandchild
    ## reparents to IT instead of init.
    discard prctl(PR_SET_CHILD_SUBREAPER, 1.culong, 0.culong, 0.culong, 0.culong)

  proc isolateOwnProcessGroup*(pid: Pid) =
    ## RFC-fuzzer-nextgen E-cleanup C3: the orchestrator-INITIATED
    ## counterpart to `armParentDeathSignal`'s kernel-enforced one. Called
    ## by the ORCHESTRATOR right after spawning `pid` — puts that worker
    ## into its OWN process group, led by itself (`setpgid(pid, pid)`). Any
    ## FURTHER descendant the worker itself forks inherits this SAME pgid
    ## automatically (ordinary POSIX fork semantics), so a single
    ## `killWorkerGroup(pid)` later reaches the worker's entire process
    ## subtree, not just the worker's own pid — and deliberately does NOT
    ## touch the calling (orchestrator) process's own group, unlike a
    ## shared `setpgid(0, 0)` campaign-wide group would (which would put
    ## the orchestrator itself in the blast radius of its own group-kill).
    ## Each worker gets its own single-worker group rather than one shared
    ## campaign-wide group, so an N=1-recycle-per-input policy (E2a's
    ## shipped default) never depends on a group whose sole member has
    ## already been reaped staying valid for the NEXT worker to join.
    discard setpgid(pid, pid)

  proc killWorkerGroup*(pid: Pid; sig: cint = SIGKILL) =
    ## Orchestrator-shutdown backstop: kills `pid`'s entire process group
    ## (see `isolateOwnProcessGroup`) — the worker itself plus any
    ## descendant it forked — in one call. Complements
    ## `PR_SET_PDEATHSIG` (the worker's own kernel-enforced "die when MY
    ## parent dies" defense, `armParentDeathSignal`): this is for the
    ## orchestrator's OWN clean-shutdown path (e.g. a caught `SIGINT`),
    ## reaching a worker's whole subtree in one call rather than relying on
    ## each descendant's individual `PR_SET_PDEATHSIG` (which only a
    ## `spawnWorkerProcess`/`newForkWorker` child arms — a worker's own
    ## further-forked descendant, e.g. an externally-fuzzed target process,
    ## may not). A no-op (`ESRCH`, discarded) if the group has already
    ## dissolved — the worker (and everything in its group) already exited.
    discard killpg(pid, sig)   # `pid` doubles as its own pgid — see above

  # --- genuine fork+exec worker spawn -----------------------------------------

  const
    nelliWorkerInFd* = 3.cint    ## child's read end of the input pipe (parent -> child)
    nelliWorkerOutFd* = 4.cint   ## child's write end of the result pipe (child -> parent)

  proc relocateIfClaimed(fd: var cint; claimed: cint) =
    ## If `fd` currently sits at the fd number a DIFFERENT source still needs
    ## to end up at, move it out of the way first (`fcntl(F_DUPFD)`, which
    ## allocates the lowest free fd at or above the given floor) so the later
    ## `dup2` onto `claimed` doesn't clobber it before it's consumed. In the
    ## common case (a fresh process with no other fds open) the two pipes
    ## land outside {3,4} and this is a no-op; it exists for the general
    ## case where some other already-open fd occupies 3 or 4.
    if fd == claimed:
      let moved = fcntl(fd, F_DUPFD, 16.cint)
      discard close(fd)
      fd = moved

  proc spawnWorkerProcess*(id: string; covFile: string; covShm: string = "";
                            cmpShm: string = ""): tuple[pid: Pid, inFd, outFd: cint] =
    ## fork+exec a FRESH copy of `getAppFilename()` in `--nelli-worker=<id>`
    ## mode, wired to two pipes on fixed fds 3/4 in the child. Mirrors
    ## `fuzz.nim`'s `runChild` discipline exactly: argv/env are allocated
    ## BEFORE `fork()`; the child does nothing but raw `dup2`/`close`/
    ## `execvpe` between `fork()` and exec — no Nim string/seq
    ## allocation (hence no GC) runs in the child's not-yet-replaced,
    ## COW-shared address space. `covFile` (may be "") is exported to the
    ## child as `$NELLI_COV_FILE` (E2a C2: the interim, N=1-only coverage-dump
    ## transport). `covShm` (may be "") is exported as `$NELLI_COV_SHM` (E2b
    ## C3: the shm transport a persistent worker uses to publish PER-INPUT,
    ## valid for N>1 — see `runWorkerLoopAndExit`). A caller sets at most one;
    ## setting both is not a supported combination (the worker loop prefers
    ## shm when present — see there). `cmpShm` (may be "") is exported as
    ## `$NELLI_CMP_SHM` (RFC-fuzzer-nextgen G4 C2: the cmp-log's own,
    ## independent shm channel — orthogonal to `covShm`, a caller may set
    ## either, neither, or both).
    var inPipe, outPipe: array[2, cint]
    if posix.pipe(inPipe) != 0: raiseOSError(osLastError(), "pipe (worker input) failed")
    if posix.pipe(outPipe) != 0: raiseOSError(osLastError(), "pipe (worker output) failed")
    let selfPath = getAppFilename()
    # Argv/env construction is `workerproto`'s platform-independent policy
    # (RFC-fuzzer-nextgen E4a C1) — the drop-inherited-transport-then-add
    # logic lives there once, shared with the future Windows `CreateProcess`
    # glue instead of duplicated for it.
    var argv = workerArgv(selfPath, id)
    var inherited: seq[(string, string)]
    for k, v in envPairs(): inherited.add (k, v)
    var envv = workerEnv(inherited, covFile, covShm, cmpShm)
    let ca = allocCStringArray(argv)
    let ce = allocCStringArray(envv)
    let pid = fork()
    if pid < 0:
      deallocCStringArray(ca); deallocCStringArray(ce)
      raiseOSError(osLastError(), "fork failed")
    if pid == 0:
      armParentDeathSignal()
      var r = inPipe[0]
      var w = outPipe[1]
      relocateIfClaimed(r, nelliWorkerOutFd)
      relocateIfClaimed(w, nelliWorkerInFd)
      discard close(inPipe[1])
      discard close(outPipe[0])
      discard dup2(r, nelliWorkerInFd)
      discard dup2(w, nelliWorkerOutFd)
      if r != nelliWorkerInFd: discard close(r)
      if w != nelliWorkerOutFd: discard close(w)
      discard execvpe(selfPath.cstring, ca, ce)
      exitnow(127)                              # exec failed
    deallocCStringArray(ca); deallocCStringArray(ce)
    discard close(inPipe[0])                     # parent doesn't read its own input pipe
    discard close(outPipe[1])                    # parent doesn't write its own output pipe
    isolateOwnProcessGroup(pid)                  # E-cleanup C3: shutdown-time killWorkerGroup backstop
    (pid, inPipe[1], outPipe[0])

  proc reapWorker*(pid: Pid): tuple[exitCode: int, signal: int] =
    ## Block for `pid`'s exit and decode its status precisely (signal vs
    ## exit code) — the same `WIFSIGNALED`/`WTERMSIG`/`WEXITSTATUS` decode
    ## `runChild` uses. A process `Worker[T]` (C4) uses this to classify a
    ## worker that died without writing a result frame as `vCrashed`.
    var status: cint = 0
    discard waitpid(pid, status, cint(0))
    if WIFSIGNALED(status):
      (exitCode: -1, signal: int(WTERMSIG(status)))
    else:
      (exitCode: int(WEXITSTATUS(status)), signal: 0)

  # --- coverage: interim file-dump transport (C2) -----------------------------
  #
  # `runWorkerReentry` runs the property THROUGH the in-process `{.cover.}`
  # bitmap (`observeInProcess`/`inProcessProbe`), not the external
  # sancov/`nelli_cov.c` C runtime — there is no instrumented external child
  # here, the "target" is a Nim in-process property running INSIDE the
  # worker. So the worker itself must publish that in-process bitmap to
  # `$NELLI_COV_FILE`, in the SAME wire format `nelli_cov.c` already uses
  # (`parseCoverageMap`, fuzz.nim) so the orchestrator reads a worker's
  # coverage with the exact same reader it already has for an external C
  # target — no second coverage reader to build or keep in sync.
  #
  # `nelliCovDumped` mirrors `nelli_cov.c`'s `pt_dumped`: gated to fire
  # AT MOST ONCE per process. This is NOT an accident of the C runtime we're
  # imitating — it's the reason E2a's shipped policy is "recycle every
  # input" (N=1, DoD #5): a worker process that services a SECOND input
  # (the `NELLI_WORKER_MAX_INPUTS` knob, off by default) finds this gate
  # already closed, so its coverage is silently NOT published — stale/absent,
  # not wrong-but-plausible. `tests/tfuzzworkerprocess.nim` pins this exact
  # staleness as a characterization test, not just describes it in prose.
  var nelliCovDumped = false

  proc covChecksum(counters: seq[uint8]): uint32 =
    for c in counters: result += uint32(c)

  proc dumpCoverageOnce*(cov: Coverage) =
    ## Publish `cov` to `$NELLI_COV_FILE` in the `nelli_cov.c` PCOV wire
    ## format (`"PCOV" | u32 version | u32 targetId | u32 len | bytes | u32
    ## checksum`, little-endian) — a NO-OP if the env var is unset (no
    ## orchestrator-assigned dump path; matches `nelli_cov.c`'s own
    ## behavior) or if this process has already dumped once. Writes to
    ## `<path>.tmp` then renames (atomic; no reader ever observes a torn
    ## write), mirroring `nelli_cov.c`'s own dump discipline.
    if nelliCovDumped: return
    nelliCovDumped = true
    let path = getEnv("NELLI_COV_FILE", "")
    if path.len == 0: return
    var buf: seq[byte]
    buf.putU32(0x564F4350'u32)          # "PCOV", little-endian byte order
    buf.putU32(1'u32)                   # version
    buf.putU32(0'u32)                   # targetId (unused by a Nim in-process worker)
    buf.putU32(uint32(cov.counters.len))
    for c in cov.counters: buf.putU8(c)
    buf.putU32(covChecksum(cov.counters))
    let tmp = path & ".tmp"
    writeFile(tmp, buf)
    moveFile(tmp, path)

  # --- crash isolation: a worker that died without answering (C3, DoD #4) ----

  proc observationForDeath*[T](exitCode, signal: int): Observation[T] =
    ## RFC-fuzzer-nextgen E2a (C3): a worker process is dead (it closed its
    ## end of the result pipe without writing a full frame — a segfault, an
    ## uncatchable signal, ...) — NOT a run the in-process oracle ever got to
    ## judge. Mapped to `vCrashed` (E1's `CrashKind` taxonomy already carries
    ## this case, unused until now) rather than propagated as an exception
    ## that would abort the whole campaign: DoD #4's "crash verdict instead
    ## of aborting the run", for the half of it (b) `observeInProcess`'s
    ## try/except can't reach — an actual process death, not a catchable
    ## Nim `Defect`/`CatchableError`. A process `Worker[T]` (C4) calls this
    ## after `reapWorker` when `readFrame` came back empty/truncated.
    let msg =
      if signal != 0: "worker died on signal " & $signal
      else: "worker exited " & $exitCode & " without a result frame"
    let crash =
      if signal != 0: CrashInfo(kind: ckSignal, signal: signal, message: msg)
      else: CrashInfo(kind: ckExitCode, exitCode: exitCode, message: msg)
    Observation[T](verdict: vCrashed, crash: some(crash), message: msg)

  # --- the worker loop (runs INSIDE the re-exec'd child) ----------------------

  proc runWorkerLoopAndExit*(id: string;
                              dispatch: proc(input: ChoiceSeq): Observation[void] {.closure.}) {.noreturn.} =
    ## RFC-fuzzer-nextgen E2a: the child-process side of worker-mode
    ## dispatch. Called from `fuzzmacro.nim`'s generated code in place of the
    ## normal front door when `nelliWorkerModeId` matches this call site.
    ## Reads framed inputs from `nelliWorkerInFd`, runs each through
    ## `dispatch` (bound by the caller to `runWorkerReentry(id, _)` — the
    ## SAME in-process reconstruction E1 proved, now reached via a genuine
    ## fork+exec instead of an in-process call), and writes a framed result
    ## back. Always exits the process (`quit`) — this is a dedicated worker
    ## entry, it never falls through to any other code in the binary.
    var served = 0
    let maxInputs = try: parseInt(getEnv("NELLI_WORKER_MAX_INPUTS", "1"))
                    except ValueError: 1
      ## N=1 by default — a fresh worker process per input, still the safe
      ## choice when NEITHER transport below is explicitly configured for
      ## multi-input use (a caller that sets `$NELLI_COV_SHM` and raises
      ## this opts into E2b's now-valid N>1 path; `0` means unbounded,
      ## test-only, for exercising crash-loop geometry where coverage
      ## validity is moot).
    let shmName = getEnv("NELLI_COV_SHM", "")
      ## RFC-fuzzer-nextgen E2b (C3): when set, coverage rides the shm
      ## transport with a genuine per-input reset/republish cycle — VALID
      ## for N>1 inputs in this same process (`shmResetCoverage`/
      ## `shmPublishCoverage`, coverage.nim). When unset, behavior is
      ## UNCHANGED from E2a: `dumpCoverageOnce`'s file-dump, valid for the
      ## first input only (still the right choice for a single-input,
      ## fresh-exec-per-input worker — the shipped default above).
    let cmpShmName = getEnv("NELLI_CMP_SHM", "")
      ## RFC-fuzzer-nextgen G4 C2: the cmp-log's OWN shm transport, wired at
      ## the SAME per-input boundary as coverage's — orthogonal to
      ## `shmName` above (a caller may set either, neither, or both). No
      ## file-dump fallback: unlike coverage (which predates shm and keeps
      ## E2a's transport for compatibility), the cmp log is new in this
      ## slice with no prior transport to preserve, so it is shm-only —
      ## unset means "not logged", not "logged some other way".
    while maxInputs == 0 or served < maxInputs:
      let frameOpt =
        try: readFrame(nelliWorkerInFd)
        except FrameError: break
      if frameOpt.isNone: break
      let input =
        try: fromBytes(frameOpt.get)
        except DbCorrupt: break
      if shmName.len > 0: shmResetCoverage(shmName)   # per-input reset — BEFORE the run (E2b pin #4)
      if cmpShmName.len > 0: shmResetCmpLog(cmpShmName)
      let obs = dispatch(input)
      if shmName.len > 0: shmPublishCoverage(shmName, obs.coverage)
      else: dumpCoverageOnce(obs.coverage)             # E2a file-dump fallback, unchanged
      if cmpShmName.len > 0: shmPublishCmpLog(cmpShmName)
      let resultBytes = encodeObservationLite(obs)
      try: writeFrame(nelliWorkerOutFd, resultBytes)
      except FrameError: break
      inc served
    quit(0)

  # --- the process Worker[T] (C4) ---------------------------------------------

  proc newProcessWorker*[T](id: string): Worker[T] =
    ## RFC-fuzzer-nextgen E2a (C4): a real, isolated `Worker[T]` — every
    ## `submit` spawns a FRESH worker process (`spawnWorkerProcess`), the
    ## shipped N=1 recycle policy (DoD #5: `dumpCoverageOnce`'s once-per-
    ## process gate makes a fresh process per input the only way this
    ## interim coverage path stays valid). An `Orchestrator[T]` built over
    ## this `Worker` (via `newOrchestrator(worker, frontier)`, fuzz.nim)
    ## drives it exactly like E1's in-process `Worker` — same `submit`/
    ## `run`/`admit` seam, same `Observation[T]` shape.
    ##
    ## `submit`: write one input frame, read one result frame. A clean or
    ## truncated pipe failure (the worker died before answering — DoD #4b's
    ## "fails cleanly, not a hang") is NOT propagated as an exception; it is
    ## mapped to a `vCrashed` `Observation` via `observationForDeath`, using
    ## `reapWorker`'s precise exit-status decode — so a crashing input is a
    ## FINDING the campaign continues past, not an abort. Coverage rides the
    ## interim file-dump transport (C2): read back from the per-submit
    ## unique `$NELLI_COV_FILE` after the worker exits, then the temp file
    ## is removed.
    var spawnCtr = 0
    newWorker(proc(input: ChoiceSeq): Observation[T] =
      inc spawnCtr
      let covPath = getTempDir() / ("nelli_worker_cov_" & $getCurrentProcessId() &
                                     "_" & $spawnCtr & ".bin")
      let (pid, inFd, outFd) = spawnWorkerProcess(id, covPath)
      var frameOpt = none(seq[byte])
      try:
        writeFrame(inFd, toBytes(input))
        frameOpt = readFrame(outFd)
      except FrameError:
        discard   # broken pipe / truncated / bad frame -> a dead worker, handled below
      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      result =
        if frameOpt.isSome: decodeObservationLite[T](frameOpt.get)
        else: observationForDeath[T](exitCode, signal)
      if fileExists(covPath):
        try: result.coverage = parseCoverageMap(readFile(covPath))
        except ValueError: discard
        removeFile(covPath))

  # --- fork-per-input recycling (RFC-fuzzer-nextgen E3a C4) -------------------

  proc newForkWorker*[T](dispatch: proc(input: ChoiceSeq): Observation[void] {.closure.}): Worker[T] =
    ## RFC-fuzzer-nextgen E3a (C4): fork-per-input recycling. POSIX only, and
    ## only safe when the calling process has not itself spawned other OS
    ## threads before the first call — a real POSIX `fork()` precondition
    ## (only the calling thread survives into the child; a live sibling
    ## thread's held lock can wedge or corrupt the child). This library never
    ## calls `createThread`, so an ordinary nelli binary satisfies this by
    ## construction; embedding nelli inside a caller's OWN multi-threaded
    ## process must not use this worker.
    ##
    ## Unlike `newProcessWorker` (E2a: fork+exec, which RE-RUNS the whole
    ## binary's top-level init plus the macro's reconstruction closure for
    ## every input), every `submit` here forks THIS SAME, already-running
    ## process directly — NEVER from a previously-forked child. Every child
    ## therefore inherits the EXACT same "parked", post-init,
    ## pre-any-input-execution memory snapshot: this process's own state at
    ## whatever point its caller finished one-time setup (e.g. the macro's
    ## single front-door construction) and started calling `submit` —
    ## captured implicitly, EXACTLY ONCE, because this process itself never
    ## executes an input through `dispatch` directly; only its
    ## (always-freshly-forked) children do. This is what makes the "captured
    ## once, never re-parked from post-execution state" invariant hold BY
    ## CONSTRUCTION rather than by convention: there is no code path that
    ## could "re-park" from a post-execution state, because there is no
    ## second parking point — see `tests/tfuzzforkworker.nim` for the
    ## characterization test that pins this.
    ##
    ## The child runs exactly one input through `dispatch`, writes one result
    ## frame back over a pipe, and `quit`s — it never returns to any other
    ## code in the binary. Cheaper than `newProcessWorker`'s fork+exec (no
    ## re-exec, no re-parsed argv, no re-run construction) at the cost of
    ## relying on the COW-sharing assumption fork+exec sidesteps.
    newWorker(proc(input: ChoiceSeq): Observation[T] =
      var outPipe: array[2, cint]
      if posix.pipe(outPipe) != 0: raiseOSError(osLastError(), "pipe (fork worker) failed")
      let pid = fork()
      if pid < 0:
        raiseOSError(osLastError(), "fork failed")
      if pid == 0:
        armParentDeathSignal()
        discard close(outPipe[0])
        let obs = dispatch(input)
        let resultBytes = encodeObservationLite(obs)
        try: writeFrame(outPipe[1], resultBytes)
        except FrameError: discard
        quit(0)
      isolateOwnProcessGroup(pid)                # E-cleanup C3: shutdown-time killWorkerGroup backstop
      discard close(outPipe[1])
      var frameOpt = none(seq[byte])
      try: frameOpt = readFrame(outPipe[0])
      except FrameError: discard
      discard close(outPipe[0])
      let (exitCode, signal) = reapWorker(pid)
      if frameOpt.isSome: decodeObservationLite[T](frameOpt.get)
      else: observationForDeath[T](exitCode, signal))

when defined(windows):
  import std/[winlean, widestrs, tables]

  # `SetHandleInformation` has no `winlean` wrapper (unlike `CreateProcessW`/
  # `CreatePipe`/`ReadFile`/`WriteFile`/`GetExitCodeProcess`, all present
  # there) — declared directly here, matching the POSIX side's own `prctl`
  # precedent (a raw FFI import for the one syscall the stdlib doesn't
  # already wrap).
  proc setHandleInformation(hObject: Handle; dwMask, dwFlags: int32): WINBOOL
    {.stdcall, dynlib: "kernel32", importc: "SetHandleInformation".}

  const
    ERROR_BROKEN_PIPE = 109'i32
    ERROR_HANDLE_EOF = 38'i32
    nelliWorkerInHandleEnv = "NELLI_WORKER_IN_HANDLE"
    nelliWorkerOutHandleEnv = "NELLI_WORKER_OUT_HANDLE"
      ## The Windows analog of POSIX's fixed fds 3/4 — see the module doc
      ## comment's transport-equivalence decision. A pipe handle's numeric
      ## value is only known once `CreatePipe` allocates it (unlike a POSIX
      ## fd number, agreed on at compile time), so the parent hands it to
      ## the child via these two inherited environment variables instead.

  # --- Job Objects (RFC-fuzzer-nextgen E4c) -----------------------------------
  #
  # `winlean` already wraps `resumeThread`/`waitForSingleObject`/
  # `getExitCodeProcess`/`closeHandle`/`createIoCompletionPort`/
  # `getQueuedCompletionStatus`/`WAIT_OBJECT_0`/`WAIT_TIMEOUT` (used below
  # unchanged) — but Job Objects themselves have no `winlean` wrapper at all,
  # so every Job Object API and struct is declared here, matching the
  # existing `setHandleInformation` raw-FFI precedent immediately above.
  #
  # Mechanism (per `workerproto.JobLimitKind`'s own doc comment, which
  # already commits to this design): every worker spawn gets its OWN Job
  # Object AND its own dedicated I/O completion port, associated
  # 1:1 (`jicAssociateCompletionPort`) — a fresh pair per
  # spawn (mirroring the POSIX tier's own per-submit `spawnWorkerProcess`
  # cost profile; not a shared campaign-wide port needing a completion-key
  # dispatch table). `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE` is applied
  # UNCONDITIONALLY, independent of whether any resource limit is set — the
  # E-cleanup Windows analog of `PR_SET_PDEATHSIG`: this process's own job
  # HANDLE lives only in `pt_workerJobs` (below), so however THIS process
  # dies (clean exit, crash, hard kill), the OS closes that handle as part of
  # its own teardown, and `KILL_ON_JOB_CLOSE` reaches into the job and kills
  # the worker (and, by ordinary Windows job-object inheritance, any further
  # descendant the worker itself spawned) — no cooperating code needed in the
  # child at all, unlike POSIX's `armParentDeathSignal`, which the CHILD must
  # arm itself.
  type
    JOBOBJECT_BASIC_LIMIT_INFORMATION = object
      perProcessUserTimeLimit: int64
      perJobUserTimeLimit: int64
      limitFlags: int32
      minimumWorkingSetSize: uint
      maximumWorkingSetSize: uint
      activeProcessLimit: int32
      affinity: uint
      priorityClass: int32
      schedulingClass: int32

    IO_COUNTERS = object
      readOperationCount, writeOperationCount, otherOperationCount: uint64
      readTransferCount, writeTransferCount, otherTransferCount: uint64

    JOBOBJECT_EXTENDED_LIMIT_INFORMATION = object
      basicLimitInformation: JOBOBJECT_BASIC_LIMIT_INFORMATION
      ioInfo: IO_COUNTERS
      processMemoryLimit: uint
      jobMemoryLimit: uint
      peakProcessMemoryUsed: uint
      peakJobMemoryUsed: uint

    JOBOBJECT_ASSOCIATE_COMPLETION_PORT = object
      completionKey: pointer
      completionPort: Handle

  const
    JOB_OBJECT_LIMIT_PROCESS_TIME = 0x00000002'i32
    JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x00000100'i32
    JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000'i32
    jicAssociateCompletionPort = 7'i32
    jicExtendedLimit = 9'i32
    JOB_OBJECT_MSG_END_OF_PROCESS_TIME = 2'i32
    JOB_OBJECT_MSG_PROCESS_MEMORY_LIMIT = 9'i32
    FILETIME_TICKS_PER_SECOND = 10_000_000'i64
      ## `PerProcessUserTimeLimit` is a `LARGE_INTEGER` of 100-nanosecond
      ## ticks (the same unit as a `FILETIME`), not seconds.
    CREATE_SUSPENDED = 0x00000004'i32
      ## Spawn suspended so the job assignment below (`AssignProcessToJobObject`)
      ## lands before the process's first instruction ever runs — closing the
      ## race a non-suspended spawn would have (a very-fast-exiting child
      ## could exit, or itself spawn a not-yet-job-scoped grandchild, before
      ## `AssignProcessToJobObject` gets a chance to run at all).

    ptWinJobLimitGrace = 200'i32
      ## Milliseconds to wait, after the process itself is confirmed dead,
      ## for its Job Object's completion port to deliver a limit-violation
      ## message — the OS queues that notification asynchronously, so it can
      ## trail the process's own termination slightly. Mirrors the POSIX
      ## `runChild` SIGTERM grace window's role (a bounded wait for an
      ## asynchronous OS signal), not its value.

  proc createJobObjectW(lpJobAttributes: pointer; lpName: WideCString): Handle
    {.stdcall, dynlib: "kernel32", importc: "CreateJobObjectW".}
  proc setInformationJobObject(hJob: Handle; jobInfoClass: int32;
                                lpJobObjectInfo: pointer; cbJobObjectInfoLength: int32): WINBOOL
    {.stdcall, dynlib: "kernel32", importc: "SetInformationJobObject".}
  proc assignProcessToJobObject(hJob, hProcess: Handle): WINBOOL
    {.stdcall, dynlib: "kernel32", importc: "AssignProcessToJobObject".}
  proc terminateJobObject(hJob: Handle; uExitCode: int32): WINBOOL
    {.stdcall, dynlib: "kernel32", importc: "TerminateJobObject".}

  proc setErrorMode(uMode: int32): int32
    {.stdcall, dynlib: "kernel32", importc: "SetErrorMode".}
  const
    SEM_FAILCRITICALERRORS = 0x0001'i32
    SEM_NOGPFAULTERRORBOX = 0x0002'i32

  type
    WorkerJobRecord = object
      job, port: Handle
      limits: ResourceLimits

  var pt_workerJobs: Table[Handle, WorkerJobRecord]
    ## Keyed by `procHandle` (unique for the handle's lifetime — never reused
    ## while still a live key here, since every entry is removed by
    ## `reapWorker`/`reapWorkerWithLimits` in the same call that closes it).
    ## Exists so `spawnWorkerProcess` can keep returning the SAME 4-field
    ## tuple every existing caller (including every pre-E4c test) already
    ## destructures — the job/port handles ride along out-of-band instead of
    ## widening that tuple and breaking every `let (a, b, c, d) = ...` call
    ## site in this codebase.

  proc newWorkerJob(policy: JobLimitPolicy): tuple[job, port: Handle] =
    ## Create a fresh Job Object + a dedicated I/O completion port associated
    ## with it 1:1, and apply `policy`'s thresholds (E4c: consumes E4a C1's
    ## already-tested `workerproto.JobLimitPolicy`). `KILL_ON_JOB_CLOSE` is
    ## always set; the memory/CPU limits are set only when their policy field
    ## is non-zero (mirroring `ResourceLimits`'s own 0-means-unset
    ## convention — an unset limit must not silently become "limit to 0
    ## bytes/0 seconds").
    let job = createJobObjectW(nil, nil)
    doAssert job != 0, "CreateJobObject failed"
    let port = createIoCompletionPort(INVALID_HANDLE_VALUE, 0, ULONG_PTR(0), 1)
    doAssert port != 0, "CreateIoCompletionPort (job) failed"
    var assoc = JOBOBJECT_ASSOCIATE_COMPLETION_PORT(completionKey: nil, completionPort: port)
    discard setInformationJobObject(job, jicAssociateCompletionPort,
                                     addr assoc, int32(sizeof(assoc)))
    var info: JOBOBJECT_EXTENDED_LIMIT_INFORMATION
    var flags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
    if policy.memoryBytes > 0:
      flags = flags or JOB_OBJECT_LIMIT_PROCESS_MEMORY
      info.processMemoryLimit = uint(policy.memoryBytes)
    if policy.cpuSeconds > 0:
      flags = flags or JOB_OBJECT_LIMIT_PROCESS_TIME
      info.basicLimitInformation.perProcessUserTimeLimit =
        int64(policy.cpuSeconds) * FILETIME_TICKS_PER_SECOND
    info.basicLimitInformation.limitFlags = flags
    discard setInformationJobObject(job, jicExtendedLimit,
                                     addr info, int32(sizeof(info)))
    (job, port)

  proc killWorkerJob*(procHandle: Handle) =
    ## RFC-fuzzer-nextgen E4c: the Windows counterpart to the POSIX
    ## `killWorkerGroup` clean-shutdown backstop (E-cleanup C3) — reaches a
    ## worker's WHOLE process subtree in one call via `TerminateJobObject`.
    ## Windows job-object membership is inherited by default (a process
    ## created by a job member joins the SAME job unless it explicitly opts
    ## out), so this reaches a further descendant the worker itself spawned
    ## (e.g. an externally-fuzzed target) exactly like `killWorkerGroup`'s
    ## process-group kill reaches a POSIX worker's forked descendants. A
    ## no-op if `procHandle` has no registered job (never spawned via
    ## `spawnWorkerProcess`, or already reaped).
    if pt_workerJobs.hasKey(procHandle):
      discard terminateJobObject(pt_workerJobs[procHandle].job, 1'i32)

  proc readN(h: Handle; n: int): seq[byte] =
    ## Windows counterpart to the POSIX `readN`: read up to exactly `n`
    ## bytes via `ReadFile`, retrying on a short read. `result.len == 0` is
    ## a clean boundary EOF (`ERROR_BROKEN_PIPE`/`ERROR_HANDLE_EOF` — the
    ## peer closed its write end before writing anything); a SHORT-of-`n`,
    ## NON-zero result is a genuine truncation the caller treats as a
    ## protocol error, exactly like the POSIX side.
    result = newSeq[byte](n)
    var off = 0
    while off < n:
      var got: int32 = 0
      let ok = readFile(h, addr result[off], int32(n - off), addr got, nil)
      if ok == 0:
        let err = getLastError()
        if err != ERROR_BROKEN_PIPE and err != ERROR_HANDLE_EOF:
          discard err   # any other ReadFile failure: still surfaces as a
                         # truncated/EOF read to the caller below — the frame
                         # decoders (workerproto) turn a short body into
                         # `FrameError`, which is the right outcome either way.
        result.setLen(off)
        return
      if got == 0:
        result.setLen(off)
        return
      off += int(got)

  proc writeAll(h: Handle; data: seq[byte]): bool =
    ## Windows counterpart to the POSIX `writeAll`: write every byte,
    ## retrying on a short write. `false` on a hard failure (the peer closed
    ## its read end — `ERROR_BROKEN_PIPE` — DoD #4b's clean write-side
    ## failure signal, same as POSIX `EPIPE`).
    var off = 0
    while off < data.len:
      var wrote: int32 = 0
      let ok = writeFile(h, unsafeAddr data[off], int32(data.len - off), addr wrote, nil)
      if ok == 0 or wrote == 0:
        return false
      off += int(wrote)
    true

  proc readFrame*(h: Handle): Option[seq[byte]] =
    ## Read one framed message over a Windows pipe `Handle`. Identical
    ## contract to the POSIX `readFrame` (`none` on clean EOF, `FrameError`
    ## on anything else) — only the underlying I/O primitive differs.
    let hdr = readN(h, 12)
    if hdr.len == 0: return none(seq[byte])
    let length = decodeFrameHeader(hdr)
    let body = readN(h, length + 4)
    some(decodeFrameBody(length, body))

  proc writeFrame*(h: Handle; payload: seq[byte]) =
    ## Write one framed message over a Windows pipe `Handle`. Identical
    ## contract to the POSIX `writeFrame`.
    if not writeAll(h, encodeFrame(payload)):
      raise newException(FrameError, "frame: write failed (broken pipe)")

  # --- CreateProcess worker spawn ---------------------------------------------

  proc spawnWorkerProcess*(id: string; covFile: string; covShm: string = "";
                            cmpShm: string = ""; limits = ResourceLimits()):
      tuple[procHandle, threadHandle, inHandle, outHandle: Handle] =
    ## `CreateProcess`-based counterpart to the POSIX `spawnWorkerProcess`
    ## (E4a C2): no `fork` exists on Windows, so this always launches a
    ## FRESH `CreateProcess` of `getAppFilename()` in `--nelli-worker=<id>`
    ## mode — there is no COW-sharing shortcut to avoid here (unlike the
    ## POSIX fork+exec discipline, which is careful about what runs between
    ## `fork()` and `execvpe()`); reconstruction ALWAYS runs from a
    ## genuinely fresh process image. Two anonymous, INHERITABLE pipes carry
    ## the framed protocol — see the module doc comment's transport-
    ## equivalence decision for why not named pipes and why not the
    ## process's own stdin/stdout. `covFile`/`covShm`/`cmpShm` are forwarded
    ## into the child's environment via `workerproto.workerEnv`; `covFile`
    ## still goes unread on this platform (no file-dump transport ever
    ## existed here), but `covShm`/`cmpShm` are now consumed LIVE by
    ## `runWorkerLoopAndExit` (E4b) via `$NELLI_COV_SHM`/`$NELLI_CMP_SHM`.
    ##
    ## RFC-fuzzer-nextgen E4c: every spawn now also gets a dedicated Job
    ## Object (`newWorkerJob`, applying `limits` via `workerproto.
    ## jobLimitPolicy`) — spawned `CREATE_SUSPENDED` so `AssignProcessToJobObject`
    ## lands before the child ever runs an instruction, then resumed. The job
    ## is tracked in `pt_workerJobs` (keyed by the returned `procHandle`) for
    ## `reapWorker`/`reapWorkerWithLimits`/`killWorkerJob` to consume — the
    ## return TUPLE stays the SAME 4 fields every existing caller (including
    ## every pre-E4c test) already destructures. `limits`'s default
    ## (`ResourceLimits()`, every field 0/unset) still creates a job — for
    ## `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE` alone, unconditionally applied —
    ## but installs no memory/CPU threshold, so a caller that never asked for
    ## limits observes no behavior change from before E4c.
    var sa = SECURITY_ATTRIBUTES(nLength: int32(sizeof(SECURITY_ATTRIBUTES)),
                                  lpSecurityDescriptor: nil, bInheritHandle: 1'i32)
    var inRead, inWrite, outRead, outWrite: Handle
    if createPipe(inRead, inWrite, sa, 0'i32) == 0:
      raiseOSError(osLastError(), "CreatePipe (worker input) failed")
    if createPipe(outRead, outWrite, sa, 0'i32) == 0:
      raiseOSError(osLastError(), "CreatePipe (worker output) failed")
    # The PARENT's own retained ends must never be inherited — by this
    # child or any later one `bInheritHandles: TRUE` implicitly exposes
    # every still-inheritable handle to. Only the two ends handed to THIS
    # child (inRead, outWrite) stay inheritable.
    discard setHandleInformation(inWrite, HANDLE_FLAG_INHERIT, 0'i32)
    discard setHandleInformation(outRead, HANDLE_FLAG_INHERIT, 0'i32)

    let selfPath = getAppFilename()
    let argv = workerArgv(selfPath, id)
    var inherited: seq[(string, string)]
    for k, v in envPairs(): inherited.add (k, v)
    var envv = workerEnv(inherited, covFile, covShm, cmpShm)
    envv.add nelliWorkerInHandleEnv & "=" & $inRead
    envv.add nelliWorkerOutHandleEnv & "=" & $outWrite

    let cmdLine = quoteShellCommand(argv)
    var envBlock = ""
    for kv in envv:
      envBlock.add kv
      envBlock.add '\0'
    envBlock.add '\0'

    let (job, port) = newWorkerJob(jobLimitPolicy(limits))

    var si: STARTUPINFO
    si.cb = int32(sizeof(STARTUPINFO))
    var pi: PROCESS_INFORMATION
    let ok = createProcessW(nil, newWideCString(cmdLine), nil, nil, 1'i32,
                             CREATE_UNICODE_ENVIRONMENT or CREATE_NO_WINDOW or CREATE_SUSPENDED,
                             newWideCString(envBlock), nil, si, pi)
    # The child-owned ends were duplicated into the child by inheritance;
    # the parent's own copy must close regardless of outcome so the
    # child's eventual close of ITS copy is observable as EOF, and so a
    # failed spawn doesn't leak them.
    discard closeHandle(inRead)
    discard closeHandle(outWrite)
    if ok == 0:
      discard closeHandle(inWrite); discard closeHandle(outRead)
      discard closeHandle(port); discard closeHandle(job)
      raiseOSError(osLastError(), "CreateProcess failed")
    discard assignProcessToJobObject(job, pi.hProcess)
    discard resumeThread(pi.hThread)
    pt_workerJobs[pi.hProcess] = WorkerJobRecord(job: job, port: port, limits: limits)
    (pi.hProcess, pi.hThread, inWrite, outRead)

  proc reapWorker*(procHandle, threadHandle: Handle): tuple[exitCode: int; signal: int] =
    ## Windows counterpart to the POSIX `reapWorker`: block for the worker's
    ## exit and decode its exit code (`GetExitCodeProcess`). `signal` is
    ## always `0` — Windows has no signal taxonomy; `observationForDeath`
    ## below never constructs `ckSignal`, only `ckWinException`. Closes both
    ## handles `CreateProcess` opened (`hProcess`/`hThread`) — the Windows
    ## analog of POSIX's `waitpid` reaping.
    ##
    ## RFC-fuzzer-nextgen E4c: every process `spawnWorkerProcess` starts now
    ## also owns a Job Object + completion port (`pt_workerJobs`) that this
    ## proc's SIGNATURE cannot grow to expose (every existing caller
    ## destructures its 2-field return) — this plain `reapWorker` stays a
    ## THIN wait+decode, unaware of limits, and just closes those two
    ## handles here so a caller that never asked for limit enforcement
    ## doesn't leak them. `reapWorkerWithLimits` (below) is the
    ## limits-enforcing, Job-Object-decoding sibling `newProcessWorker` uses.
    discard waitForSingleObject(procHandle, INFINITE)
    var code: int32 = 0
    discard getExitCodeProcess(procHandle, code)
    discard closeHandle(threadHandle)
    discard closeHandle(procHandle)
    if pt_workerJobs.hasKey(procHandle):
      let rec = pt_workerJobs[procHandle]
      pt_workerJobs.del(procHandle)
      discard closeHandle(rec.port)
      discard closeHandle(rec.job)
    (exitCode: int(code), signal: 0)

  proc reapWorkerWithLimits*(procHandle, threadHandle: Handle):
      tuple[exitCode: int; signal: int; jobLimit: JobLimitKind; hadJobLimit: bool] =
    ## RFC-fuzzer-nextgen E4c: the Job-Object-aware counterpart to
    ## `reapWorker`, used by `newProcessWorker`'s submit closure (which
    ## always spawns through a limits-bearing job — see `spawnWorkerProcess`).
    ##
    ## Wall-clock enforcement: Job Objects have no wall-clock PRIMITIVE (only
    ## per-process/per-job CPU-TIME accounting — see `workerproto.
    ## JobLimitPolicy`'s own doc), so `limits.perRunTimeout` is enforced HERE,
    ## orchestrator-side, mirroring how POSIX's `runChild` enforces its own
    ## `perRunTimeout`: poll `waitForSingleObject` with a timeout instead of
    ## blocking `INFINITE`, and `TerminateJobObject` (E4c's "clean kill",
    ## reaching the worker's whole subtree, not just the one process) if the
    ## deadline passes first.
    ##
    ## Limit decode: once the process is gone (on its own, or via the
    ## wall-clock kill above), drain this spawn's DEDICATED completion port
    ## for up to `ptWinJobLimitGrace`ms — the OS's own documented
    ## notification path for a per-process memory/CPU-time job-limit kill
    ## (`JOB_OBJECT_MSG_PROCESS_MEMORY_LIMIT`/`JOB_OBJECT_MSG_END_OF_PROCESS_TIME`).
    ## A wall-clock timeout this proc itself declared is reported directly
    ## (`hadJobLimit: true`, `jobLimit: jlkWallClock`) without consulting the
    ## port — TerminateJobObject's own kill would not itself generate one of
    ## these two messages (it maps to an ordinary process-exit notification,
    ## not a limit-violation one).
    if not pt_workerJobs.hasKey(procHandle):
      let (ec, sig) = reapWorker(procHandle, threadHandle)
      return (ec, sig, jlkMemory, false)
    let rec = pt_workerJobs[procHandle]
    pt_workerJobs.del(procHandle)
    var wallClockKilled = false
    let wallClockMs = int(rec.limits.perRunTimeout.inMilliseconds)
    if wallClockMs > 0:
      if waitForSingleObject(procHandle, int32(wallClockMs)) != WAIT_OBJECT_0:
        discard terminateJobObject(rec.job, 1'i32)
        discard waitForSingleObject(procHandle, INFINITE)
        wallClockKilled = true
    else:
      discard waitForSingleObject(procHandle, INFINITE)
    var code: int32 = 0
    discard getExitCodeProcess(procHandle, code)
    discard closeHandle(threadHandle)
    discard closeHandle(procHandle)

    var jobLimit = jlkWallClock
    var hadJobLimit = wallClockKilled
    if not wallClockKilled:
      var bytes: DWORD
      var key: ULONG_PTR
      var ov: POVERLAPPED
      if getQueuedCompletionStatus(rec.port, addr bytes, addr key, addr ov, ptWinJobLimitGrace) != 0:
        case bytes
        of JOB_OBJECT_MSG_PROCESS_MEMORY_LIMIT: jobLimit = jlkMemory; hadJobLimit = true
        of JOB_OBJECT_MSG_END_OF_PROCESS_TIME: jobLimit = jlkCpu; hadJobLimit = true
        else: discard
    discard closeHandle(rec.port)
    discard closeHandle(rec.job)
    (exitCode: int(code), signal: 0, jobLimit: jobLimit, hadJobLimit: hadJobLimit)

  proc observationForDeath*[T](exitCode: int): Observation[T] =
    ## RFC-fuzzer-nextgen E4a (C2): Windows counterpart to the POSIX
    ## `observationForDeath` — the worker process is dead without ever
    ## answering its result-pipe read. Windows has no signal taxonomy: an
    ## abnormal termination (an unhandled structured exception, e.g. an
    ## access violation) surfaces as an NTSTATUS-coded exit status via
    ## `GetExitCodeProcess` (`0xC0000005` = `STATUS_ACCESS_VIOLATION`),
    ## decoded here into a `ckWinException` `CrashInfo` naming the code —
    ## the direct Windows analog of the POSIX side's `ckSignal` decode.
    let codeU32 = cast[uint32](int32(exitCode))
    let msg = "worker process exited 0x" & toHex(codeU32) & " without a result frame"
    let crash = CrashInfo(kind: ckWinException, code: codeU32, message: msg)
    Observation[T](verdict: vCrashed, crash: some(crash), message: msg)

  # --- the worker loop (runs INSIDE the CreateProcess'd child) ---------------

  proc runWorkerLoopAndExit*(id: string;
                              dispatch: proc(input: ChoiceSeq): Observation[void] {.closure.}) {.noreturn.} =
    ## RFC-fuzzer-nextgen E4a (C2): the Windows child-process side of
    ## worker-mode dispatch — the direct counterpart to the POSIX
    ## `runWorkerLoopAndExit`. Called from `fuzzmacro.nim`'s generated code
    ## in place of the normal front door when `nelliWorkerModeId` matches
    ## this call site (now reachable on Windows too — see that macro's
    ## `when defined(posix) or defined(windows)` gate). Reads its pipe
    ## handles from the environment (`NELLI_WORKER_IN_HANDLE`/
    ## `NELLI_WORKER_OUT_HANDLE` — see the module doc comment), runs each
    ## framed input through `dispatch`, and writes a framed result back.
    ## Always exits the process — this is a dedicated worker entry, it
    ## never falls through to any other code in the binary.
    ##
    ## RFC-fuzzer-nextgen E4b: coverage now rides the SAME shm transport the
    ## POSIX loop uses (`coverage.nim`'s `shmResetCoverage`/
    ## `shmPublishCoverage`/`shmResetCmpLog`/`shmPublishCmpLog`, now portable
    ## — see that module's widened `when defined(posix) or defined(windows)`
    ## gate) — byte-identical per-input reset-before/publish-after wiring at
    ## the SAME call-site boundary as the POSIX loop. Unlike POSIX (which
    ## falls back to a file-dump transport when `$NELLI_COV_SHM` is unset —
    ## an E2a interim this platform never had), an unset `$NELLI_COV_SHM`
    ## here simply leaves `dispatch`'s returned coverage unpublished, exactly
    ## E4a's prior zero-value-default behavior — no NEW fallback mechanism
    ## invented for a transport this platform never shipped.
    ##
    ## RFC-fuzzer-nextgen E4c: `SetErrorMode` is set FIRST, before anything
    ## else in this proc — a crashing worker (an unhandled structured
    ## exception: an access violation, a stack overflow, ...) would otherwise
    ## trigger the system's Windows Error Reporting dialog, which blocks
    ## indefinitely waiting for a human to dismiss it. On an unattended CI
    ## runner that turns one crashing input into a hang until the whole job
    ## times out, defeating the entire point of a crash-isolating worker.
    ## `SEM_NOGPFAULTERRORBOX` suppresses that dialog; `SEM_FAILCRITICALERRORS`
    ## does the same for the older hard-error popup (e.g. a missing DLL) —
    ## together they make a crashing worker exit PROMPTLY with its NTSTATUS
    ## exit code, exactly what `observationForDeath`/`GetExitCodeProcess`
    ## below already expects to decode.
    discard setErrorMode(SEM_NOGPFAULTERRORBOX or SEM_FAILCRITICALERRORS)
    let inH = Handle(parseInt(getEnv(nelliWorkerInHandleEnv, "0")))
    let outH = Handle(parseInt(getEnv(nelliWorkerOutHandleEnv, "0")))
    var served = 0
    let maxInputs = try: parseInt(getEnv("NELLI_WORKER_MAX_INPUTS", "1"))
                    except ValueError: 1
      ## Same N=1-by-default convention as the POSIX side (E2a) — see that
      ## proc's doc for the rationale. `NELLI_WORKER_MAX_INPUTS > 1` is now
      ## production-valid here too (E4b) whenever `$NELLI_COV_SHM` is set,
      ## the same N>1-requires-shm condition E2b established for POSIX.
    let shmName = getEnv("NELLI_COV_SHM", "")
    let cmpShmName = getEnv("NELLI_CMP_SHM", "")
    while maxInputs == 0 or served < maxInputs:
      let frameOpt =
        try: readFrame(inH)
        except FrameError: break
      if frameOpt.isNone: break
      let input =
        try: fromBytes(frameOpt.get)
        except DbCorrupt: break
      if shmName.len > 0: shmResetCoverage(shmName)   # per-input reset — BEFORE the run (E2b pin #4)
      if cmpShmName.len > 0: shmResetCmpLog(cmpShmName)
      let obs = dispatch(input)
      if shmName.len > 0: shmPublishCoverage(shmName, obs.coverage)
      if cmpShmName.len > 0: shmPublishCmpLog(cmpShmName)
      let resultBytes = encodeObservationLite(obs)
      try: writeFrame(outH, resultBytes)
      except FrameError: break
      inc served
    quit(0)

  # --- the process Worker[T] --------------------------------------------------

  proc newProcessWorker*[T](id: string; limits = ResourceLimits()): Worker[T] =
    ## RFC-fuzzer-nextgen E4a (C2): the Windows counterpart to the POSIX
    ## `newProcessWorker` — every `submit` spawns a FRESH worker process via
    ## `CreateProcess`. A clean or truncated pipe failure (the worker died
    ## before answering) is mapped to `vCrashed` via `observationForDeath`,
    ## using `reapWorker`'s exit-code decode — a crashing input is a FINDING
    ## the campaign continues past, not an abort.
    ##
    ## RFC-fuzzer-nextgen E4b: coverage is no longer the zero-value default
    ## E4a shipped (module doc comment). Windows has no file-dump transport
    ## to fall back to (POSIX's `newProcessWorker` reads `$NELLI_COV_FILE`
    ## back; this platform never had that), so this uses the ONLY transport
    ## it has — a fresh, per-submit-unique shm segment name (mirroring the
    ## POSIX side's own per-submit-unique `covPath` naming), published by
    ## the worker via `$NELLI_COV_SHM` and read back here via `shmProbe`,
    ## AFTER the result frame arrives (E2b's read-before-redispatch
    ## invariant: the worker's publish, if it got that far, already
    ## completed before it could write the frame) but before the process is
    ## reaped. A worker that crashes before publishing leaves this
    ## generation's shm segment unpublished, so `probe.read()` naturally
    ## reads back empty coverage — absent, never stale, the same contract
    ## `shmProbe`'s own doc comment establishes.
    ##
    ## RFC-fuzzer-nextgen E4c: `limits` (default `ResourceLimits()`, every
    ## field unset — backward compatible with every pre-E4c caller) rides
    ## through to `spawnWorkerProcess`'s Job Object and is decoded via
    ## `reapWorkerWithLimits` — a memory/CPU/wall-clock job kill maps through
    ## `workerproto.verdictForJobLimit` to `vResourceExceeded`, checked ONLY
    ## when the worker never answered (`frameOpt.isNone`): a worker that DID
    ## answer before any limit fired is trusted as the primary signal, the
    ## same precedence `observationForDeath`'s ordinary crash-decode already
    ## has relative to a successful frame.
    var spawnCtr = 0
    newWorker(proc(input: ChoiceSeq): Observation[T] =
      inc spawnCtr
      let shmName = "/nelli_worker_cov_" & $getCurrentProcessId() & "_" & $spawnCtr
      let probe = shmProbe(shmName)
      let (procH, threadH, inH, outH) = spawnWorkerProcess(id, "", shmName, "", limits)
      var frameOpt = none(seq[byte])
      try:
        writeFrame(inH, toBytes(input))
        frameOpt = readFrame(outH)
      except FrameError:
        discard   # broken pipe / truncated / bad frame -> a dead worker, handled below
      let cov = probe.read()
      discard closeHandle(inH); discard closeHandle(outH)
      let (exitCode, _, jobLimit, hadJobLimit) = reapWorkerWithLimits(procH, threadH)
      result =
        if frameOpt.isSome: decodeObservationLite[T](frameOpt.get)
        elif hadJobLimit:
          let (verdict, crash) = verdictForJobLimit(jobLimit)
          Observation[T](verdict: verdict, crash: some(crash), message: crash.message)
        else: observationForDeath[T](exitCode)
      result.coverage = cov)
