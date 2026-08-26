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

  proc spawnWorkerProcess*(id: string; covFile: string): tuple[pid: Pid, inFd, outFd: cint] =
    ## fork+exec a FRESH copy of `getAppFilename()` in `--nelli-worker=<id>`
    ## mode, wired to two pipes on fixed fds 3/4 in the child. Mirrors
    ## `fuzz.nim`'s `runChild` discipline exactly: argv/env are allocated
    ## BEFORE `fork()`; the child does nothing but raw `dup2`/`close`/
    ## `execvpe` between `fork()` and exec — no Nim string/seq
    ## allocation (hence no GC) runs in the child's not-yet-replaced,
    ## COW-shared address space. `covFile` (may be "") is exported to the
    ## child as `$NELLI_COV_FILE` (C2: the interim coverage-dump transport).
    var inPipe, outPipe: array[2, cint]
    if posix.pipe(inPipe) != 0: raiseOSError(osLastError(), "pipe (worker input) failed")
    if posix.pipe(outPipe) != 0: raiseOSError(osLastError(), "pipe (worker output) failed")
    let selfPath = getAppFilename()
    var argv = @[selfPath, nelliWorkerFlagPrefix & id]
    var envv: seq[string]
    for k, v in envPairs(): envv.add k & "=" & v
    if covFile.len > 0: envv.add "NELLI_COV_FILE=" & covFile
    let ca = allocCStringArray(argv)
    let ce = allocCStringArray(envv)
    let pid = fork()
    if pid < 0:
      deallocCStringArray(ca); deallocCStringArray(ce)
      raiseOSError(osLastError(), "fork failed")
    if pid == 0:
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
      ## N=1 by default (the shipped policy this slice pins, DoD #5): a
      ## fresh worker process per input, because the interim coverage
      ## file-dump (`nelli_cov.c`'s `pt_dumped`, mirrored here by
      ## `dumpCoverageToFile`'s own once-per-process gate) only ever
      ## produces a VALID dump for the first input a process observes.
      ## `NELLI_WORKER_MAX_INPUTS` is the explicit seam E2b flips once
      ## coverage reset/republish lands; 0 means unbounded (test-only, for
      ## exercising crash-loop geometry where coverage validity is moot).
    while maxInputs == 0 or served < maxInputs:
      let frameOpt =
        try: readFrame(nelliWorkerInFd)
        except FrameError: break
      if frameOpt.isNone: break
      let input =
        try: fromBytes(frameOpt.get)
        except DbCorrupt: break
      let obs = dispatch(input)
      # C2 adds: dump obs.coverage to $NELLI_COV_FILE here (the interim
      # file-dump transport) before replying.
      let resultBytes = encodeObservationLite(obs)
      try: writeFrame(nelliWorkerOutFd, resultBytes)
      except FrameError: break
      inc served
    quit(0)
