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

import std/[os, options, strutils, times, sysrand]
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

proc unpredictableSuffix(): string =
  ## RFC-fuzzer-nextgen R20: an unguessable per-spawn tag, layered on top of
  ## the existing pid+counter naming (`newProcessWorker`'s `covPath`) — that
  ## naming alone is fully predictable to a local attacker (the pid is
  ## visible via `ps`; the counter starts at 1), which is the root cause the
  ## finding names. `urandom` (`std/sysrand`) draws from the OS's secure
  ## entropy source; 8 bytes (64 bits) is far more than enough to make
  ## pre-placing a symlink at the right path before a campaign starts
  ## infeasible. This is defense IN ADDITION TO, not instead of, the
  ## `O_CREAT|O_EXCL` atomic-create in `writeFileNoFollow` below — even a
  ## correctly guessed name is refused there if anything already occupies
  ## the path.
  for b in urandom(8): result.add toHex(b)

proc decodeObservationLiteSafe*[T](data: seq[byte]): Observation[T] =
  ## RFC-fuzzer-nextgen R16: `newProcessWorker`'s own doc commits to "a
  ## dead/misbehaving worker is mapped to a `vCrashed` `Observation` ... not
  ## propagated as an exception." Frame checksum validation
  ## (`decodeFrameBody`, workerproto.nim) proves the BYTES a worker sent
  ## crossed the pipe intact — it does NOT prove they DECODE to a valid
  ## `Observation`. A version-skewed re-exec (the orchestrator binary
  ## replaced on disk mid-campaign, so a freshly exec'd worker runs a
  ## DIFFERENT `encodeObservationLite` layout than this process's own
  ## decoder expects) or a corrupted/misbehaving worker can produce
  ## checksum-valid bytes that are still semantically invalid:
  ## `decodeObservationLite`'s `Verdict(getU8(...))`/`CrashKind(getU8(...))`
  ## casts raise `RangeDefect` for an out-of-range ordinal, and a truncated
  ## length-prefixed string (`getRawStr`) raises `DbCorrupt` (binaryio.nim).
  ## Both are data-shape problems in bytes that already crossed a pipe from
  ## a SEPARATE OS process — not a bug in THIS process — so both fold into
  ## `vCrashed` here, exactly like `observationForDeath`'s outright-death
  ## case, instead of taking down the whole orchestrator.
  ##
  ## Deliberately narrow: catches ONLY `DbCorrupt` and `RangeDefect`. A
  ## bare `except CatchableError` or `except Defect` would ALSO swallow a
  ## genuine bug in this process's OWN code (e.g. an `OutOfMemDefect` from a
  ## huge-but-in-cap allocation, or an `AssertionDefect` from a real broken
  ## invariant), silently relabeling a real programming error as a spurious
  ## worker crash instead of surfacing it. Nim's default build (this project
  ## never passes `--panics:on` — see `nim.cfg`) keeps `Defect` catchable
  ## like any other exception, so catching `RangeDefect` specifically here
  ## is safe and does not risk undefined behavior.
  try:
    decodeObservationLite[T](data)
  except DbCorrupt, RangeDefect:
    let msg = "worker result frame failed to decode: " & getCurrentExceptionMsg()
    Observation[T](verdict: vCrashed,
                    crash: some(CrashInfo(kind: ckException, defect: "DecodeError",
                                           message: msg)),
                    message: msg)

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

  proc armParentDeathSignal(expectedParent: Pid) =
    ## Called by a freshly forked CHILD, as early as possible (before any
    ## other syscall) — arms `SIGKILL` to be delivered by the kernel the
    ## moment THIS process's parent dies. `expectedParent` is the forking
    ## PARENT's own `getpid()`, read by the PARENT itself immediately before
    ## calling `fork()` (see each call site) — NOT re-derived here via the
    ## child's own `getppid()`. That distinction is load-bearing, not
    ## cosmetic: under real scheduling contention, a freshly forked child can
    ## go completely unscheduled — not even its first instruction runs —
    ## until well after its true parent has died AND been reaped by a
    ## subreaper. If this proc instead read `getppid()` itself as its
    ## "expected parent" baseline (a PRIOR revision of this code did exactly
    ## that), that very first read already observes the POST-reparent state:
    ## `getppid()` at that point returns the subreaper, not the dead
    ## original parent, so the child's own self-consistency check compares
    ## the reparented value against itself and finds no mismatch — `prctl`
    ## then arms `PDEATHSIG` against the WRONG (subreaper) process, and the
    ## worker survives indefinitely, only dying whenever the SUBREAPER
    ## itself later happens to exit, rather than when its actual orchestrator
    ## died. Reproduced directly: 7/16 concurrent
    ## `tests/tfuzzworkerlifecycle` runs hung this way under load, each one's
    ## worker sitting in `pipe_read`, PPid already reparented to the test
    ## process (itself parked in `do_wait`) — `kill`ing that test process
    ## alone (not the long-dead orchestrator) killed the "stuck" worker
    ## within ~2ms, proving `PDEATHSIG` had been armed against it. Taking
    ## `expectedParent` from the PARENT's pre-`fork()` read closes this: that
    ## read can never itself be post-race (the parent computes it about
    ## itself, synchronously, before `fork()` exists), so comparing against
    ## it after `prctl` correctly detects a reparent that happened at ANY
    ## point up to and including this call, no matter how long the child sat
    ## unscheduled.
    discard prctl(PR_SET_PDEATHSIG, SIGKILL.culong, 0.culong, 0.culong, 0.culong)
    if getppid() != expectedParent:
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

  proc closeFds(fds: varargs[cint]) =
    ## RFC-fuzzer-nextgen R17: close every fd already opened on an
    ## early-failure path, in one call per branch instead of a hand-written
    ## `discard close(...)` per fd duplicated at every raise site (easy to
    ## forget one, especially as a proc grows more failure branches over
    ## time). Every caller below passes exactly the fds that are STILL open
    ## at that point in the sequence — see each call site's own comment.
    for fd in fds: discard close(fd)

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
    if posix.pipe(outPipe) != 0:
      let err = osLastError()
      closeFds(inPipe[0], inPipe[1])   # R17: the first pipe already succeeded -- don't leak it
      raiseOSError(err, "pipe (worker output) failed")
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
    let selfPidBeforeFork = getpid()   # see armParentDeathSignal's doc -- must be read HERE, by
                                        # the parent, before fork(), not re-derived by the child
    let pid = fork()
    if pid < 0:
      let err = osLastError()
      deallocCStringArray(ca); deallocCStringArray(ce)
      closeFds(inPipe[0], inPipe[1], outPipe[0], outPipe[1])   # R17: both pipes are still fully open here
      raiseOSError(err, "fork failed")
    if pid == 0:
      armParentDeathSignal(selfPidBeforeFork)
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

  const O_NOFOLLOW = 0o400000.cint
    ## Not exposed by Nim's `std/posix` for this target (`asm-generic/
    ## fcntl.h`'s fixed Linux value) — declared directly here, matching this
    ## file's `prctl`/(Windows) `SetHandleInformation` precedent for the one
    ## constant/syscall the stdlib wrapper doesn't already carry.

  proc writeFileNoFollow(path: string; buf: seq[byte]) =
    ## RFC-fuzzer-nextgen R20: write `buf` to `path` WITHOUT ever following
    ## a pre-existing symlink there. `path` is `dumpCoverageOnce`'s `.tmp`
    ## staging file, derived from `$NELLI_COV_FILE` — which is itself
    ## derived, orchestrator-side, from the orchestrator's OWN pid (visible
    ## to any local user via `ps`) and a spawn counter starting at 1 (see
    ## `newProcessWorker`'s `covPath`, now ALSO salted with an unpredictable
    ## suffix — the two defenses are independent and both apply). Plain
    ## `writeFile` opens like `fopen(path, "wb")` — `O_CREAT|O_TRUNC`
    ## WITHOUT `O_EXCL` — which follows a symlink already sitting at `path`
    ## and truncates-and-overwrites whatever it points at: a local attacker
    ## on a shared host who guesses (or, pre-salt, computed) the next dump
    ## path can pre-place a symlink aimed at any file this process can
    ## write, and an ordinary `writeFile` follows it (CWE-377/CWE-59).
    ## `O_CREAT|O_EXCL` is POSIX-atomic against exactly this: if ANY
    ## directory entry — file or symlink — already sits at `path`, the open
    ## fails with `EEXIST` and nothing is ever written through it; `O_NOFOLLOW`
    ## is belt-and-suspenders on top of `O_EXCL` (both refuse a pre-existing
    ## symlink; kept in case some platform/libc's `O_EXCL` symlink handling
    ## ever proves looser than POSIX requires), not a substitute for it —
    ## `O_NOFOLLOW` alone would still happily `O_TRUNC` an attacker's
    ## PRE-EXISTING ordinary file at `path`. `0o600` (owner-only) is tighter
    ## than `writeFile`'s default `0o644`: no reason for another local user
    ## to even read this process's coverage dump. The final rename into
    ## place (`moveFile(tmp, path)`, `dumpCoverageOnce` below) needs no
    ## matching change: POSIX `rename()` replaces the DIRECTORY ENTRY at its
    ## destination atomically — it never dereferences a symlink sitting
    ## there — so it was already symlink-safe as a destination.
    let fd = posix.open(path.cstring,
                         O_WRONLY or O_CREAT or O_EXCL or O_NOFOLLOW, 0o600.Mode)
    if fd < 0:
      raiseOSError(osLastError(), "open (coverage dump, O_EXCL) failed: " & path)
    try:
      if not writeAll(fd, buf):
        raiseOSError(osLastError(), "write (coverage dump) failed: " & path)
    finally:
      discard close(fd)

  proc dumpCoverageOnce*(cov: Coverage) =
    ## Publish `cov` to `$NELLI_COV_FILE` in the `nelli_cov.c` PCOV wire
    ## format (`"PCOV" | u32 version | u32 targetId | u32 len | bytes | u32
    ## checksum`, little-endian) — a NO-OP if the env var is unset (no
    ## orchestrator-assigned dump path; matches `nelli_cov.c`'s own
    ## behavior) or if this process has already dumped once. Writes to
    ## `<path>.tmp` via `writeFileNoFollow` (R20: symlink-safe, unlike plain
    ## `writeFile`) then renames (atomic; no reader ever observes a torn
    ## write; already symlink-safe as a destination — see that proc's own
    ## doc), mirroring `nelli_cov.c`'s own dump discipline.
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
    writeFileNoFollow(tmp, buf)
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
      else:
        try: dumpCoverageOnce(obs.coverage)            # E2a file-dump fallback, unchanged
        except OSError:
          ## R20: `writeFileNoFollow`'s `O_CREAT|O_EXCL` open can now
          ## legitimately fail -- a refused symlink attack, but also an
          ## ordinary disk-full/permission error the old unconditional
          ## `writeFile` could already hit. Either way this proc's OWN
          ## contract (module doc: "Always exits the process -- ... it never
          ## falls through to any other code in the binary") must hold: an
          ## uncaught exception here would propagate OUT of this
          ## `{.noreturn.}` proc, defeating that guarantee. Losing this
          ## round's coverage is the same acceptable degradation
          ## `dumpCoverageOnce`'s own once-per-process gate already accepts
          ## for a SECOND input (module doc, `nelliCovDumped`) -- silently
          ## absent, not wrong-but-plausible, and the campaign continues via
          ## the result frame below exactly as it would for a clean run.
          discard
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
    ##
    ## RFC-fuzzer-nextgen R12 (code review): also requests the cmp-log's OWN
    ## shm channel (`$NELLI_CMP_SHM`), so `fuzz*[T]`'s G5 I2S mutation gets
    ## real cross-process operand guidance when `settings.processIsolation`
    ## is on, not just the in-process path — see `Observation.cmpLog`'s doc
    ## (fuzz.nim). `cmpShmName` is a FRESH, per-spawn-unique name — like
    ## `covPath` — NOT one segment reused across every spawn: `nelli_shm.c`'s
    ## `generation` word only ever INCREMENTS once a channel has published at
    ## least once (`pt_shm_ch_reset_buffer` clears only the STAGING half,
    ## never `published`/`generation`), so a LATER spawn whose own run logs
    ## no comparisons (`shmPublishCmpLog` is a documented no-op when nothing
    ## was logged) would read back an EARLIER spawn's STALE entries off a
    ## reused segment — actively wrong data reaching `mutateIRI2SReplace`,
    ## worse than the empty-when-unpublished contract `shmReadCmpLog`
    ## otherwise guarantees. A fresh, never-before-published segment per
    ## spawn is the only way an unpublished run reads back genuinely empty.
    ## `shmHoldCmpLog` is called BEFORE each spawn (mirroring the Windows
    ## coverage probe's identical per-spawn hold below) — harmless on POSIX
    ## (idempotent create-or-open; segments persist past `munmap` regardless
    ## of hold) but establishes the SAME pre-attach-before-producer-exists
    ## discipline uniformly. RECLAIMED via `shmUnlinkCmpLog` (coverage.nim,
    ## POSIX-only) right after this spawn's `shmReadCmpLog` completes — see
    ## that proc's own doc for why unlinking a still-mapped segment is safe
    ## and why Windows needs no counterpart — so a long process-isolated
    ## campaign does NOT accumulate one segment per iteration in `/dev/shm`;
    ## a hard-killed campaign's leftovers still fall back to `db.nim`'s
    ## `sweepStaleShmSegments` startup backstop. RFC-fuzzer-nextgen R53 (code
    ## review): that guarantee also covers `spawnWorkerProcess` itself
    ## raising -- see the `try`/`except` wrapped around that call below,
    ## the one path between this hold and the success-path unlink above
    ## that R12's original follow-up missed.
    var spawnCtr = 0
    newWorker(proc(input: ChoiceSeq): Observation[T] =
      inc spawnCtr
      # R20: the pid+counter naming alone is fully predictable (pid via
      # `ps`, counter from 1) -- `unpredictableSuffix()` adds an unguessable
      # tag so a local attacker cannot pre-place a symlink at this path
      # before the campaign even starts. `writeFileNoFollow` (this module,
      # the POSIX child side) is the OTHER half of the fix -- refuses to
      # follow a symlink even if the name IS somehow guessed.
      let covPath = getTempDir() / ("nelli_worker_cov_" & $getCurrentProcessId() &
                                     "_" & $spawnCtr & "_" & unpredictableSuffix() & ".bin")
      let cmpShmName = "/nelli_worker_cmp_" & $getCurrentProcessId() & "_" & $spawnCtr
      shmHoldCmpLog(cmpShmName)
      # RFC-fuzzer-nextgen R53 (code review): `shmHoldCmpLog` above has
      # already attached -- and, per its own R47 contract, freshly CREATED
      # -- this spawn's cmp-log segment. If `spawnWorkerProcess` itself
      # raises (pipe()/fork() failure under fd/process pressure -- see
      # `tests/tfuzzworkerprocess.nim`'s R23 suite for how real that is),
      # execution never reaches the success-path `shmUnlinkCmpLog` call
      # below, and this fresh segment would sit in `/dev/shm` for the rest
      # of the campaign -- exactly the per-iteration accumulation this
      # module's own doc comment above says does NOT happen. Catch, reclaim,
      # and re-raise the ORIGINAL exception unchanged: `shmUnlinkCmpLog`
      # never raises on its own (see its doc, coverage.nim), so this can
      # never mask or replace the real spawn failure.
      let (pid, inFd, outFd) =
        try:
          spawnWorkerProcess(id, covPath, cmpShm = cmpShmName)
        except CatchableError:
          shmUnlinkCmpLog(cmpShmName)
          raise
      var frameOpt = none(seq[byte])
      try:
        writeFrame(inFd, toBytes(input))
        frameOpt = readFrame(outFd)
      except FrameError:
        discard   # broken pipe / truncated / bad frame -> a dead worker, handled below
      # E2b's read-before-redispatch invariant (same one the Windows
      # coverage probe below relies on): the worker's per-input publish, if
      # it got that far, already completed BEFORE it wrote the result frame
      # — reading now is race-free regardless of platform.
      let cmpLog = shmReadCmpLog(cmpShmName)
      shmUnlinkCmpLog(cmpShmName)   # R12 follow-up: reclaim now that the read is done
      discard close(inFd); discard close(outFd)
      let (exitCode, signal) = reapWorker(pid)
      result =
        if frameOpt.isSome: decodeObservationLiteSafe[T](frameOpt.get)
        else: observationForDeath[T](exitCode, signal)
      result.cmpLog = some(cmpLog)
      if fileExists(covPath):
        try: result.coverage = parseCoverageMap(readFile(covPath))
        except ValueError: discard
        removeFile(covPath))

  # --- fork-per-input recycling (RFC-fuzzer-nextgen E3a C4) -------------------

  type
    ForkUnsafeError* = object of CatchableError
      ## RFC-fuzzer-nextgen R15: raised by `newForkWorker`'s `submit` when
      ## another OS thread is alive in this process at the moment it would
      ## `fork()` — see `assertForkSafeSingleThreaded` below.

  proc assertForkSafeSingleThreaded() =
    ## RFC-fuzzer-nextgen R15: the ENFORCED form of `newForkWorker`'s own
    ## hazard doc below — a runtime check, not a compile-time one. A
    ## `when compileOption("threads")` gate was considered and rejected:
    ## this project's OWN test runner (`nelli.nimble`'s `task test`, run via
    ## `dt-bounded.sh`) passes `--threads:on` unconditionally, so gating on
    ## THAT flag would make `newForkWorker` permanently unreachable in every
    ## test build — not a safety fix, just a different way to break the
    ## feature. `--threads:on` only means the binary CAN create threads; it
    ## says nothing about whether one is alive RIGHT NOW, which is the
    ## actual `fork()` precondition. So this counts LIVE threads via
    ## `/proc/self/task` (Linux; consistent with this module's existing
    ## Linux-only POSIX assumptions — `prctl`'s `PR_SET_PDEATHSIG`/
    ## `PR_SET_CHILD_SUBREAPER` above are Linux syscalls with no portable
    ## POSIX equivalent already) — each subdirectory there is one live
    ## thread (LWP) of THIS process, main thread included. More than one
    ## means a thread besides the caller is alive at THIS specific moment,
    ## and raises `ForkUnsafeError` rather than risking the deadlock/
    ## corruption a real `fork()` under that condition can cause. Checked on
    ## EVERY `submit`, not once at construction: a caller's threading state
    ## can change between `newForkWorker`'s call and any later `submit`
    ## (e.g. `parallelCheck`, `parallel.nim`, spawning its own worker
    ## threads mid-campaign).
    ##
    ## If `/proc/self/task` cannot be read at all (a POSIX platform without
    ## `/proc`, e.g. macOS/BSD — already outside this module's supported
    ## range, since `prctl` itself only links on Linux), this fails OPEN
    ## (allows the fork): there is no better signal available there, and
    ## this module already commits to Linux-only in practice.
    var threads = 0
    var determined = false
    try:
      for kind, _ in walkDir("/proc/self/task"):
        if kind == pcDir: inc threads
      determined = true
    except OSError:
      discard
    if determined and threads > 1:
      raise newException(ForkUnsafeError,
        "newForkWorker: " & $threads & " OS threads alive in this process " &
        "(fork() only carries the calling thread into the child -- a lock " &
        "held by another thread at fork time can deadlock or corrupt the " &
        "child). Use newProcessWorker (fork+exec) instead, or ensure no " &
        "other thread is alive across this worker's submit calls.")

  proc newForkWorker*[T](dispatch: proc(input: ChoiceSeq): Observation[void] {.closure.}): Worker[T] =
    ## RFC-fuzzer-nextgen E3a (C4): fork-per-input recycling. POSIX only, and
    ## only safe when NO OTHER OS thread is alive in this process at the
    ## moment of `fork()` — a real POSIX precondition (only the calling
    ## thread survives into the child; a live sibling thread's held lock,
    ## e.g. inside libc's malloc arena or the GC, can deadlock or corrupt the
    ## not-yet-exec'd child). A PRIOR REVISION of this comment claimed "this
    ## library never calls `createThread`, so an ordinary nelli binary
    ## satisfies this by construction" — that was FALSE: `parallel.nim`'s
    ## `parallelCheck` calls `createThread` directly, and both modules ship
    ## from the same top-level `nelli` package. The mitigating fact is that
    ## `parallelCheck` always `joinThreads`s before returning, so its threads
    ## are not normally alive concurrently with anything else — but nothing
    ## enforced that invariant here. `assertForkSafeSingleThreaded` (above)
    ## is the enforcement: a RUNTIME thread census immediately before every
    ## `fork()` below, raising `ForkUnsafeError` if more than the calling
    ## thread is alive (see that proc's own doc for why this is a runtime
    ## check, not a compile-time `--threads:on` gate). Embedding nelli inside
    ## a caller's OWN multi-threaded process must still not use this worker
    ## while that other threading is active.
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
      assertForkSafeSingleThreaded()   # R15: enforced immediately before fork(), every submit
      var outPipe: array[2, cint]
      if posix.pipe(outPipe) != 0: raiseOSError(osLastError(), "pipe (fork worker) failed")
      let selfPidBeforeFork = getpid()   # see armParentDeathSignal's doc -- must be read HERE, by
                                          # the parent, before fork(), not re-derived by the child
      let pid = fork()
      if pid < 0:
        let err = osLastError()
        closeFds(outPipe[0], outPipe[1])   # R17: pipe() already succeeded -- don't leak it here
        raiseOSError(err, "fork failed")
      if pid == 0:
        armParentDeathSignal(selfPidBeforeFork)
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
      if frameOpt.isSome: decodeObservationLiteSafe[T](frameOpt.get)
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
  # unchanged). The actual Job Object types/FFI declarations and the
  # create-job-plus-port-and-apply-limits logic (originally landed whole
  # here in E4c C1) now live in `fuzz.nim` (`newLimitJob*`/
  # `checkJobLimitCode*`/`assignProcessToJobObject*`/`terminateJobObject*`)
  # — E4c C3 moved them so the one-shot external tier (`fuzz.nim`'s own
  # Windows `runChild`) could reuse the EXACT same apparatus instead of a
  # second copy; `fuzz.nim` sits at the bottom of this trio's import graph
  # (`workerproto` imports `./fuzz`; this module imports `./fuzz` AND
  # `./workerproto`), so that is the only placement that avoids a circular
  # import. Nothing about THIS module's own observable behavior changed —
  # `newWorkerJob` below is now a one-line wrapper.
  #
  # Mechanism (per `workerproto.JobLimitKind`'s own doc comment, which
  # already commits to this design): every worker spawn gets its OWN Job
  # Object AND its own dedicated I/O completion port, associated 1:1 — a
  # fresh pair per spawn (mirroring the POSIX tier's own per-submit
  # `spawnWorkerProcess` cost profile; not a shared campaign-wide port
  # needing a completion-key dispatch table). `JOB_OBJECT_LIMIT_
  # KILL_ON_JOB_CLOSE` is applied UNCONDITIONALLY, independent of whether
  # any resource limit is set — the E-cleanup Windows analog of
  # `PR_SET_PDEATHSIG`: this process's own job HANDLE lives only in
  # `pt_workerJobs` (below), so however THIS process dies (clean exit,
  # crash, hard kill), the OS closes that handle as part of its own
  # teardown, and `KILL_ON_JOB_CLOSE` reaches into the job and kills the
  # worker (and, by ordinary Windows job-object inheritance, any further
  # descendant the worker itself spawned) — no cooperating code needed in
  # the child at all, unlike POSIX's `armParentDeathSignal`, which the
  # CHILD must arm itself.
  const
    CREATE_SUSPENDED = 0x00000004'i32
      ## Spawn suspended so the job assignment below (`AssignProcessToJobObject`)
      ## lands before the process's first instruction ever runs — closing the
      ## race a non-suspended spawn would have (a very-fast-exiting child
      ## could exit, or itself spawn a not-yet-job-scoped grandchild, before
      ## `AssignProcessToJobObject` gets a chance to run at all). Contrast
      ## with `fuzz.nim`'s one-shot external `runChild` (E4c C3), which has
      ## no `CREATE_SUSPENDED` equivalent available through `osproc` and so
      ## carries a documented, narrower assignment-race window instead.
      ##
      ## The completion-port drain's grace window is `fuzz.jobLimitGraceMs*`
      ## (E4c C3 factored it there too, alongside `checkJobLimitCode` —
      ## one magic number shared by both tiers, not a local copy here).

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
    ## Thin wrapper over `fuzz.newLimitJob` (E4c C3 factored the actual
    ## Job-Object-creation logic there — see the module doc above) — takes
    ## the already-tested `workerproto.JobLimitPolicy` this module's own
    ## callers use, and unpacks it to the plain `(memoryBytes, cpuSeconds)`
    ## ints `newLimitJob` accepts (it cannot import `workerproto`'s type
    ## itself; see that proc's own doc comment for why).
    newLimitJob(policy.memoryBytes, policy.cpuSeconds)

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
      let err = osLastError()
      # R17: the input pipe already succeeded -- don't leak both its handles
      # on the output pipe's failure (mirrors the CreateProcess-failure
      # branch below, which already closes everything it opened by then).
      discard closeHandle(inRead); discard closeHandle(inWrite)
      raiseOSError(err, "CreatePipe (worker output) failed")
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
    let assignOk = assignProcessToJobObject(job, pi.hProcess)
    let assignErr = osLastError()
    if assignOk == 0 and (limits.addressSpaceBytes > 0 or limits.cpuSeconds > 0):
      # RFC-fuzzer-nextgen E4c C3 fix-up: CI push 33017017592's memory-limit
      # test failed with no diagnosable cause, because this result used to
      # be discarded unconditionally -- a real assignment failure would look
      # IDENTICAL to "the limit was applied but never fired". A caller that
      # actually asked for a resource limit must not silently run
      # unconstrained; fail loudly instead. A caller that asked for NO limit
      # (the common case -- KILL_ON_JOB_CLOSE is the only thing riding on
      # this assignment then) is not worth breaking every existing
      # unlimited-spawn test over a defense-in-depth mechanism failing to
      # attach, so this check is scoped to the limited case only.
      #
      # RFC-fuzzer-nextgen R13 fix: checked and handled BEFORE `resumeThread`
      # (below) -- the child is still `CREATE_SUSPENDED` at this point, so
      # the correct move is to never let it run at all rather than resume it
      # and then discover the limit never attached. `TerminateProcess`, not
      # `TerminateJobObject`: job membership is precisely what failed to
      # attach, so the process cannot be assumed to be a member of `job`.
      # Every handle this spawn opened is closed before raising, mirroring
      # the `ok == 0` (CreateProcess failure) branch just above -- without
      # this, the process ran resource-unlimited with `pi.hProcess`/
      # `pi.hThread`/`inWrite`/`outRead`/`port`/`job` all leaked and no
      # `pt_workerJobs` entry for any later reap/kill to find it by.
      discard terminateProcess(pi.hProcess, 1)
      discard closeHandle(pi.hThread)
      discard closeHandle(pi.hProcess)
      discard closeHandle(inWrite); discard closeHandle(outRead)
      discard closeHandle(port); discard closeHandle(job)
      raiseOSError(assignErr, "AssignProcessToJobObject failed for a resource-limited spawn")
    discard resumeThread(pi.hThread)   # always resume -- never leak a permanently-suspended process
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
    ## for up to `fuzz.jobLimitGraceMs`ms — the OS's own documented
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
      # `fuzz.checkJobLimitCode` (E4c C3) is the SAME drain `runChild`'s own
      # Windows arm uses for the one-shot external tier — one implementation
      # of "wait on the completion port, decode the message" for both
      # tiers. It returns the plain `uint32` code
      # `workerproto.verdictForJobLimit` would embed in `CrashInfo.code`
      # (`jlkCodeMemory`/`jlkCodeCpu`, `0`/`1` — the SAME fixed ordinals
      # `JobLimitKind`'s own enum declaration carries), so `JobLimitKind(code)`
      # below is a direct, safe ordinal cast, not a guess.
      let (hit, limitCode) = checkJobLimitCode(rec.port, jobLimitGraceMs)
      if hit:
        jobLimit = JobLimitKind(limitCode)
        hadJobLimit = true
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
    ## `reapWorkerWithLimits`.
    ##
    ## RFC-fuzzer-nextgen E4c C3 round 3 fix-up: the job-limit message wins
    ## UNCONDITIONALLY, checked BEFORE `frameOpt.isSome` — the reverse of
    ## this proc's original precedence (`fuzzer-windows` CI run 33020523296
    ## caught it: `JOB_OBJECT_LIMIT_PROCESS_MEMORY` does NOT terminate a
    ## process by itself, it only fails the COMMIT — Nim's allocator raises
    ## `OutOfMemDefect` on that failure, `observeInProcess` catches it like
    ## any other in-process exception, and the worker answers a completely
    ## ORDINARY result frame, `ckException`/`vInteresting` — while
    ## `JOB_OBJECT_MSG_PROCESS_MEMORY_LIMIT` sits in the port the whole time,
    ## proving what ACTUALLY happened). The port message is the authoritative
    ## cause; a present frame is merely subordinate evidence of how the
    ## worker behaved once the commit failed underneath it — it does NOT
    ## mean the run was clean. A CPU-limit or wall-clock kill (`TerminateJobObject`)
    ## still dies without ever writing a frame, so this same check also
    ## correctly covers that shape (`frameOpt.isNone`) — one precedence rule
    ## for both.
    ##
    ## Attribution window (N>1, documented not solved here): this proc is
    ## ALWAYS spawn-per-submit (a fresh job+port pair every call, N=1 by
    ## construction), so a `hadJobLimit` hit is unambiguously attributable to
    ## THIS submit's input — no cross-submit staleness is possible. A
    ## DIFFERENT caller reusing one worker process across several submits
    ## (`NELLI_WORKER_MAX_INPUTS > 1`, driven directly against
    ## `spawnWorkerProcess`/`reapWorkerWithLimits` — this proc never does
    ## that) would NOT get the same guarantee: `reapWorkerWithLimits`/
    ## `checkJobLimitCode` only drain the completion port ONCE, at final
    ## process reap, so a limit hit on submit K of an N>1 worker cannot be
    ## distinguished from one on submit K+1 without draining the port BETWEEN
    ## submits too — not currently plumbed (the port itself is not exposed
    ## outside `spawnWorkerProcess`'s internal `pt_workerJobs` bookkeeping).
    ## Out of scope for this slice; a future N>1-with-limits caller would
    ## need that added.
    ##
    ## RFC-fuzzer-nextgen R12 (code review): also requests the cmp-log's OWN
    ## shm channel (`$NELLI_CMP_SHM`) — see the POSIX `newProcessWorker`'s
    ## matching R12 doc for the full rationale and `Observation.cmpLog`'s
    ## doc (fuzz.nim). Like coverage's shm name just above, `cmpShmName` is
    ## a FRESH, per-spawn-unique name, NOT one segment reused across every
    ## spawn: `nelli_shm.c`'s `generation` word only ever increments once a
    ## channel has published at least once, so a later spawn whose own run
    ## logs no comparisons (`shmPublishCmpLog` is a no-op when nothing was
    ## logged) would read back an EARLIER spawn's STALE entries off a reused
    ## segment — wrong data reaching `mutateIRI2SReplace`, not the
    ## empty-when-unpublished contract `shmReadCmpLog` otherwise guarantees.
    ## `pt_cmplog_channel` is its own singleton, independent of coverage's
    ## `pt_default_channel` (nelli_shm.c's G4 comment), so per-spawn holding
    ## it here has no interaction with coverage's own per-spawn hold above.
    var spawnCtr = 0
    newWorker(proc(input: ChoiceSeq): Observation[T] =
      inc spawnCtr
      let shmName = "/nelli_worker_cov_" & $getCurrentProcessId() & "_" & $spawnCtr
      # RFC-fuzzer-nextgen E4c C3 round 3: pre-attach BEFORE the worker
      # exists — see `shmHoldCoverage`'s own doc comment (coverage.nim) for
      # why: a Windows named file mapping is destroyed when its LAST handle
      # closes, and this worker (N=1) may publish and exit before this
      # process ever gets a handle of its own if that attach were deferred
      # to AFTER the frame arrives, the way it worked before this fix.
      shmHoldCoverage(shmName)
      let probe = shmProbe(shmName)
      let cmpShmName = "/nelli_worker_cmp_" & $getCurrentProcessId() & "_" & $spawnCtr
      shmHoldCmpLog(cmpShmName)
      # RFC-fuzzer-nextgen R53 (code review): unlike the POSIX arm above,
      # nothing here needs an explicit release if `spawnWorkerProcess`
      # raises next (`CreateProcess` failure, or the R13 job-object-assign
      # failure path) -- even for BOTH held segments on a partial failure
      # (e.g. `shmHoldCoverage` above succeeds but `shmHoldCmpLog` itself
      # raises before this line is ever reached). There is no Windows
      # counterpart to `shmUnlinkCmpLog` to call (see that proc's own doc):
      # a named section dies with its last handle, and this process's own
      # handle for a given channel is only ever released by
      # `pt_shm_ch_init`'s own re-attach-to-a-different-name path
      # (`nelli_shm.c`) -- which runs unconditionally on THIS closure's
      # very next invocation (`shmHoldCoverage`/`shmHoldCmpLog` above,
      # called again with `spawnCtr` incremented to a fresh name) -- or by
      # this process exiting, if the campaign aborts instead of retrying.
      # Either way a doomed segment from a failed spawn is never held past
      # the next attempt, so there is nothing to invent a release call for.
      let (procH, threadH, inH, outH) = spawnWorkerProcess(id, "", shmName, cmpShmName, limits)
      var frameOpt = none(seq[byte])
      try:
        writeFrame(inH, toBytes(input))
        frameOpt = readFrame(outH)
      except FrameError:
        discard   # broken pipe / truncated / bad frame -> a dead worker, handled below
      let cov = probe.read()
      let cmpLog = shmReadCmpLog(cmpShmName)
      discard closeHandle(inH); discard closeHandle(outH)
      let (exitCode, _, jobLimit, hadJobLimit) = reapWorkerWithLimits(procH, threadH)
      result =
        if hadJobLimit:
          let (verdict, crash) = verdictForJobLimit(jobLimit)
          Observation[T](verdict: verdict, crash: some(crash), message: crash.message)
        elif frameOpt.isSome: decodeObservationLiteSafe[T](frameOpt.get)
        else: observationForDeath[T](exitCode)
      result.coverage = cov
      result.cmpLog = some(cmpLog))
