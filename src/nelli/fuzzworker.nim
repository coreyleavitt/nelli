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

import std/[os, options, strutils]
import ./fuzz, ./binaryio, ./serialize

# --- worker-mode argv dispatch ------------------------------------------------

const nelliWorkerFlagPrefix* = "--nelli-worker="

proc parseWorkerModeId(): string =
  for i in 1..paramCount():
    let p = paramStr(i)
    if p.startsWith(nelliWorkerFlagPrefix):
      return p[nelliWorkerFlagPrefix.len .. ^1]
  ""

let nelliWorkerModeId* = parseWorkerModeId()
  ## Non-empty iff this process was launched with `--nelli-worker=<id>`.
  ## Parsed at MODULE LOAD (this `let`'s initializer runs as part of this
  ## module's top-level init, which — being a dependency of `fuzzmacro.nim`,
  ## which is a dependency of any `import nelli` — completes before the
  ## importing (test/application) module's own top-level code, including
  ## every `fuzz(...)` call site, runs. `fuzzmacro.nim`'s generated code
  ## compares this against its OWN call-site id and branches into
  ## `runWorkerLoopAndExit` instead of the normal front door — the dispatch
  ## the RFC calls "argv call-site ID", not an inherited env var.

# --- versioned framed protocol ------------------------------------------------

type
  FrameError* = object of CatchableError
    ## Raised for anything that is NOT a clean frame-boundary EOF: a
    ## truncated frame, a bad magic, an unsupported version, a checksum
    ## mismatch, an oversized length prefix, or a broken-pipe write. A clean
    ## EOF (the peer closed its write end before sending anything) is NOT an
    ## error — `readFrame` returns `none` for that (the ordinary "no more
    ## input"/"worker died before responding" signal, DoD #4b).

const
  nelliFrameMagic = 0x464C454E'u32     ## "NELF", little-endian byte order
  nelliFrameVersion* = 1'u32
  nelliMaxFrameBytes* = 16 * 1024 * 1024
    ## Hard cap on one frame's payload. Checked against the length prefix
    ## BEFORE attempting to read that many bytes — an unbounded/recursive
    ## strategy that would try to send an enormous choice-sequence frame
    ## fails LOUDLY (`FrameError`) here rather than wedging the pipe in an
    ## indefinite blocking read.

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
    ## mismatch.
    let hdr = readN(fd, 12)
    if hdr.len == 0: return none(seq[byte])
    if hdr.len < 12:
      raise newException(FrameError,
        "frame header truncated: got " & $hdr.len & "/12 bytes")
    var pos = 0
    let magic = getU32(hdr, pos)
    if magic != nelliFrameMagic:
      raise newException(FrameError, "frame: bad magic")
    let version = getU32(hdr, pos)
    if version != nelliFrameVersion:
      raise newException(FrameError,
        "frame: unsupported version " & $version & " (expected " & $nelliFrameVersion & ")")
    let length = getU32(hdr, pos)
    if length > uint32(nelliMaxFrameBytes):
      raise newException(FrameError,
        "frame: length " & $length & " exceeds max " & $nelliMaxFrameBytes & " bytes")
    let bodyLen = int(length) + 4
    let body = readN(fd, bodyLen)
    if body.len != bodyLen:
      raise newException(FrameError,
        "frame body truncated: got " & $body.len & "/" & $bodyLen & " bytes")
    var sum = 0'u32
    for i in 0 ..< int(length): sum += uint32(body[i])
    var pos2 = int(length)
    let checksum = getU32(body, pos2)
    if checksum != sum:
      raise newException(FrameError, "frame: checksum mismatch")
    some(body[0 ..< int(length)])

  proc writeFrame*(fd: cint; payload: seq[byte]) =
    ## Write one framed message. Raises `FrameError` if `payload` exceeds
    ## `nelliMaxFrameBytes` (never emit a frame a well-behaved reader would
    ## have to reject) or the underlying pipe write fails (broken pipe).
    if payload.len > nelliMaxFrameBytes:
      raise newException(FrameError,
        "frame: payload " & $payload.len & " exceeds max " & $nelliMaxFrameBytes & " bytes")
    var buf: seq[byte]
    buf.putU32(nelliFrameMagic)
    buf.putU32(nelliFrameVersion)
    buf.putU32(uint32(payload.len))
    buf.add payload
    var sum = 0'u32
    for b in payload: sum += uint32(b)
    buf.putU32(sum)
    if not writeAll(fd, buf):
      raise newException(FrameError, "frame: write failed (broken pipe)")

  # --- Observation (lite) codec: verdict + Option[CrashInfo] + message -------
  # Coverage deliberately excluded (module doc: rides the file-dump path);
  # `RunResult` deliberately excluded (external-target-only; not meaningful
  # for a worker running a Nim in-process property).

  proc encodeObservationLite*(obs: Observation[void]): seq[byte] =
    result.putU8(uint8(ord(obs.verdict)))
    result.putBool(obs.crash.isSome)
    if obs.crash.isSome:
      let c = obs.crash.get
      result.putU8(uint8(ord(c.kind)))
      result.putRawStr(c.message)
      case c.kind
      of ckException: result.putRawStr(c.defect)
      of ckSignal: result.putI32(int32(c.signal))
      of ckExitCode: result.putI32(int32(c.exitCode))
      of ckWinException: result.putU32(c.code)
    result.putRawStr(obs.message)

  proc decodeObservationLite*[T](data: seq[byte]): Observation[T] =
    var pos = 0
    let verdict = Verdict(getU8(data, pos))
    let hasCrash = getBool(data, pos)
    var crash = none(CrashInfo)
    if hasCrash:
      let kind = CrashKind(getU8(data, pos))
      let message = getRawStr(data, pos)
      case kind
      of ckException:
        let defect = getRawStr(data, pos)
        crash = some(CrashInfo(kind: ckException, defect: defect, message: message))
      of ckSignal:
        let signal = int(getI32(data, pos))
        crash = some(CrashInfo(kind: ckSignal, signal: signal, message: message))
      of ckExitCode:
        let exitCode = int(getI32(data, pos))
        crash = some(CrashInfo(kind: ckExitCode, exitCode: exitCode, message: message))
      of ckWinException:
        let code = getU32(data, pos)
        crash = some(CrashInfo(kind: ckWinException, code: code, message: message))
    let message = getRawStr(data, pos)
    Observation[T](verdict: verdict, crash: crash, message: message)

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
    var argv = @[selfPath, nelliWorkerFlagPrefix & id]
    var envv: seq[string]
    # Explicitly drop any INHERITED `NELLI_COV_FILE`/`NELLI_COV_SHM`/
    # `NELLI_CMP_SHM` before deciding what the CHILD's should be — this
    # process may itself be a worker launched with one (e.g. a worker whose
    # own reconstructed code path spawns a further worker), and blindly
    # forwarding `envPairs()` would leak that STALE value into a child
    # whose caller asked for a DIFFERENT (or no) transport.
    for k, v in envPairs():
      if k notin ["NELLI_COV_FILE", "NELLI_COV_SHM", "NELLI_CMP_SHM"]: envv.add k & "=" & v
    if covFile.len > 0: envv.add "NELLI_COV_FILE=" & covFile
    if covShm.len > 0: envv.add "NELLI_COV_SHM=" & covShm
    if cmpShm.len > 0: envv.add "NELLI_CMP_SHM=" & cmpShm
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
