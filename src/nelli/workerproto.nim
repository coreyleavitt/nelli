## RFC-fuzzer-nextgen E4a (C1): the platform-INDEPENDENT half of the
## persistent-worker protocol.
##
## `fuzzworker.nim` (POSIX) proved the framed pipe protocol, argv call-site
## dispatch, and fork+exec worker spawn together, all under one
## `when defined(posix)` block. E4a needs the SAME wire protocol and
## dispatch decision to serve a Windows worker too — `CreateProcess` +
## named pipes instead of `fork`/`execvpe` + POSIX pipes — but the actual
## `CreateProcess`/named-pipe/Job-Object syscalls are Windows-only glue that
## cannot be exercised on this (Linux) dev host (see
## `docs/RFC-fuzzer-nextgen.windows-capability.md`). So this module carries
## every piece of that protocol that does NOT touch a raw OS handle:
##
## - frame encode/decode: the `magic|version|len|payload|checksum` wire
##   format itself, as pure `seq[byte] -> seq[byte]` transforms. The actual
##   read/write syscalls stay in the platform-specific worker module
##   (`fuzzworker.nim`'s `readN`/`writeAll`, and the not-yet-written Windows
##   equivalent using `ReadFile`/`WriteFile`) — both wrap THESE functions
##   rather than re-implementing the header/checksum logic.
## - the observation-lite codec (`encodeObservationLite`/
##   `decodeObservationLite`): already pure in `fuzzworker.nim` (no syscalls),
##   just needlessly nested inside its `when defined(posix)` block — moved
##   here unchanged.
## - argv call-site-ID dispatch (`parseWorkerModeId`/`nelliWorkerModeId`):
##   already platform-independent in `fuzzworker.nim` (std/os's
##   `paramCount`/`paramStr` work identically on Windows), just not
##   factored into a function a test can call with a synthetic argv — moved
##   here, plus `workerArgv`/`workerEnv` so the ORCHESTRATOR side of argv/env
##   construction (currently inlined in `spawnWorkerProcess`) is shared too.
## - the bootstrap circuit-breaker POLICY (RFC §Open-items: "N consecutive
##   dead-before-first-read spawns abort the campaign with a
##   construction-not-reentrant diagnostic"). Distinct from
##   `Orchestrator.stormWindow`/`stormBackoff` (fuzz.nim, E-cleanup C4): that
##   one catches a worker that boots fine and then dies systemically on
##   every recycle (a sliding window of same-kind crashes); THIS one catches
##   a worker that never gets far enough to answer its first read at all
##   (broken re-entry, a hosed environment) — a categorically different
##   failure a per-input crash counter can't distinguish from "the fuzzed
##   input was simply the first one down an unlucky pipe." Live-wired into
##   `Orchestrator.run` (fuzz.nim, R29a) via the shared `./bootstrapbreaker`
##   leaf module — see that module's doc for why the fold itself lives
##   there rather than here (this module still re-exports it, so nothing
##   that already imports `workerproto` for `BootstrapBreaker` needs to
##   change).
## - Job-Object limit-threshold POLICY: which `ResourceLimits` values become
##   which Job Object limits, and how a limit-kill notification maps to
##   nelli's `Verdict`/`CrashInfo` taxonomy. The actual
##   `SetInformationJobObject`/`TerminateJobObject` calls are E4c.

import std/[os, strutils, options, times]
import ./binaryio, ./fuzz
import ./bootstrapbreaker
export bootstrapbreaker

# --- versioned framed protocol ------------------------------------------------

type
  FrameError* = object of CatchableError
    ## Raised for anything that is NOT a clean frame-boundary EOF: a
    ## truncated frame, a bad magic, an unsupported version, a checksum
    ## mismatch, an oversized length prefix, or (I/O-layer only) a broken-
    ## pipe write. A clean EOF (the peer closed its write end before sending
    ## anything) is NOT an error — the I/O layer's `readFrame` returns
    ## `none` for that, never reaching these pure decoders at all.

const
  nelliFrameMagic = 0x464C454E'u32     ## "NELF", little-endian byte order
  nelliFrameVersion* = 1'u32
  nelliMaxFrameBytes* = 16 * 1024 * 1024
    ## Hard cap on one frame's payload. `decodeFrameHeader` checks the
    ## length prefix against this BEFORE the I/O layer attempts to read that
    ## many bytes — an unbounded/recursive strategy that would try to send
    ## an enormous choice-sequence frame fails LOUDLY (`FrameError`) here
    ## rather than wedging a fixed-size pipe buffer in an indefinite
    ## blocking read.

proc encodeFrame*(payload: seq[byte]): seq[byte] =
  ## Pure build of one frame's wire bytes:
  ## `magic(u32) | version(u32) | len(u32) | payload | checksum(u32)`.
  ## Raises `FrameError` if `payload` exceeds `nelliMaxFrameBytes` (never
  ## build a frame a well-behaved reader would have to reject). The I/O
  ## layer's `writeFrame` is a thin wrapper: build here, write raw bytes
  ## there.
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
  buf

proc decodeFrameHeader*(hdr: seq[byte]): int =
  ## Pure validate of a frame's 12-byte header (magic, version, length),
  ## already read in full by the I/O layer (a short read there is a clean
  ## EOF, handled BEFORE this is called — this only ever sees either a
  ## complete 12-byte header or a genuinely truncated one). Returns the
  ## validated payload length on success; raises `FrameError` for anything
  ## else: wrong header size, bad magic, an unsupported version, or a
  ## length prefix over `nelliMaxFrameBytes`.
  if hdr.len != 12:
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
  int(length)

proc decodeFrameBody*(payloadLen: int; body: seq[byte]): seq[byte] =
  ## Pure validate+extract of a frame's body (the payload plus its trailing
  ## checksum), already read in full by the I/O layer using the length
  ## `decodeFrameHeader` returned. Raises `FrameError` on a short body (a
  ## truncated frame — the peer died or the pipe closed mid-frame) or a
  ## checksum mismatch.
  let bodyLen = payloadLen + 4
  if body.len != bodyLen:
    raise newException(FrameError,
      "frame body truncated: got " & $body.len & "/" & $bodyLen & " bytes")
  var sum = 0'u32
  for i in 0 ..< payloadLen: sum += uint32(body[i])
  var pos = payloadLen
  let checksum = getU32(body, pos)
  if checksum != sum:
    raise newException(FrameError, "frame: checksum mismatch")
  body[0 ..< payloadLen]

# --- Observation (lite) codec: verdict + Option[CrashInfo] + message -------
# Coverage deliberately excluded (rides the file-dump/shm path); `RunResult`
# deliberately excluded (external-target-only; not meaningful for a worker
# running a Nim in-process property). Already pure in origin (no syscalls) —
# moved here unchanged from `fuzzworker.nim`, which had it needlessly nested
# inside a `when defined(posix)` block.

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

# --- worker-mode argv dispatch ------------------------------------------------

const nelliWorkerFlagPrefix* = "--nelli-worker="

proc parseWorkerModeId*(argv: seq[string]): string =
  ## Pure: does `argv` (NOT including argv[0], the program path — matches
  ## `paramStr(1..paramCount())`'s convention) carry a `--nelli-worker=<id>`
  ## flag, and if so, what id? `""` means "not worker mode." Used both to
  ## parse this process's OWN live argv (`nelliWorkerModeId`, below) and by
  ## a test to check the decision against a synthetic argv without spawning
  ## anything.
  for p in argv:
    if p.startsWith(nelliWorkerFlagPrefix):
      return p[nelliWorkerFlagPrefix.len .. ^1]
  ""

proc workerArgv*(selfPath, id: string): seq[string] =
  ## Pure: the argv a worker spawn (POSIX `execvpe`, or Windows
  ## `CreateProcess`'s command line, E4a cycle 2) launches with — a
  ## self-re-exec of `selfPath` carrying `--nelli-worker=<id>`. The actual
  ## spawn call supplies `selfPath` (`getAppFilename()`) and does the
  ## OS-specific argv/handle wiring around this.
  @[selfPath, nelliWorkerFlagPrefix & id]

proc workerEnv*(inherited: seq[(string, string)];
                covFile = ""; covShm = ""; cmpShm = ""): seq[string] =
  ## Pure: a worker child's `KEY=VALUE` environment list, derived from the
  ## PARENT's `inherited` pairs (typically `envPairs()`) with any INHERITED
  ## `NELLI_COV_FILE`/`NELLI_COV_SHM`/`NELLI_CMP_SHM` dropped first — this
  ## process may itself be a worker launched with one of these, and blindly
  ## forwarding it would leak a STALE transport into a child whose caller
  ## asked for a DIFFERENT (or no) one — then whichever of `covFile`/
  ## `covShm`/`cmpShm` is non-empty appended. A caller sets at most one of
  ## `covFile`/`covShm` (the worker loop prefers shm when both happen to be
  ## set); `cmpShm` is independent of both.
  for kv in inherited:
    if kv[0] notin ["NELLI_COV_FILE", "NELLI_COV_SHM", "NELLI_CMP_SHM"]:
      result.add kv[0] & "=" & kv[1]
  if covFile.len > 0: result.add "NELLI_COV_FILE=" & covFile
  if covShm.len > 0: result.add "NELLI_COV_SHM=" & covShm
  if cmpShm.len > 0: result.add "NELLI_CMP_SHM=" & cmpShm

proc liveWorkerArgv(): seq[string] =
  for i in 1..paramCount(): result.add paramStr(i)

let nelliWorkerModeId* = parseWorkerModeId(liveWorkerArgv())
  ## Non-empty iff this process was launched with `--nelli-worker=<id>`.
  ## Parsed at MODULE LOAD (this `let`'s initializer runs as part of this
  ## module's top-level init, which — being a dependency of `fuzzworker.nim`,
  ## which is a dependency of `fuzzmacro.nim`, which is a dependency of any
  ## `import nelli` — completes before the importing (test/application)
  ## module's own top-level code, including every `fuzz(...)` call site,
  ## runs. `fuzzmacro.nim`'s generated code compares this against its OWN
  ## call-site id and branches into `runWorkerLoopAndExit` instead of the
  ## normal front door. `std/os`'s `paramCount`/`paramStr` are NOT
  ## POSIX-specific (unlike the rest of `fuzzworker.nim`), so this dispatch
  ## decision was already platform-independent before this module existed —
  ## living here just makes that fact structural instead of incidental.

# --- bootstrap circuit-breaker policy ---------------------------------------
#
# `BootstrapBreaker`/`newBootstrapBreaker`/`recordDeadBeforeFirstRead`/
# `recordFirstReadSucceeded` moved to the leaf module `./bootstrapbreaker`
# (R29a) — re-exported above so this remains a pure move, not a breaking
# surface change. See that module's doc comment for why.

# --- Job-Object limit-threshold policy --------------------------------------

type
  JobLimitKind* = enum
    ## Which Job Object limit a kill notification (E4c: delivered via the
    ## job's I/O completion port on `JOB_OBJECT_MSG_*`) fired for.
    jlkMemory, jlkCpu, jlkWallClock

  JobLimitPolicy* = object
    ## Which Job Object limits to apply, and their threshold VALUES —
    ## derived from `ResourceLimits` (fuzz.nim), the same per-run cap record
    ## `externalTarget`'s POSIX `setrlimit` path already consumes. Pure
    ## data: the actual `SetInformationJobObject` calls that install these
    ## are E4c. `0` means "do not apply this limit," mirroring
    ## `ResourceLimits`'s own 0-means-unset convention.
    memoryBytes*: int
    cpuSeconds*: int
    wallClockMs*: int

proc jobLimitPolicy*(limits: ResourceLimits): JobLimitPolicy =
  JobLimitPolicy(memoryBytes: limits.addressSpaceBytes,
                  cpuSeconds: limits.cpuSeconds,
                  wallClockMs: int(limits.perRunTimeout.inMilliseconds))

proc verdictForJobLimit*(kind: JobLimitKind): tuple[verdict: Verdict, crash: CrashInfo] =
  ## Maps a Job Object limit-kill notification to nelli's verdict/crash
  ## taxonomy. Always `vResourceExceeded` — per that `Verdict` case's own
  ## doc comment (fuzz.nim), memory/CPU/wall-clock resource kills are ALL
  ## `vResourceExceeded`, distinct from `vInteresting`/`vCrashed`/
  ## `vTimedOut` so an unbounded-allocation non-bug (or a worker simply
  ## running long) doesn't flood the crash corpus as if it were a found
  ## bug. Carries WHICH limit fired in `ckWinException`'s `code` field
  ## (already the Windows-only `CrashKind` arm — a Job Object limit kill is
  ## a Windows-only phenomenon by construction; POSIX's equivalent goes
  ## through `runChild`'s own SIGTERM/SIGKILL timeout path, mapped through
  ## `RunResult.timedOut`/`ckSignal` instead, not this function).
  let msg =
    case kind
    of jlkMemory: "job object memory limit exceeded"
    of jlkCpu: "job object cpu limit exceeded"
    of jlkWallClock: "job object wall-clock limit exceeded"
  (vResourceExceeded, CrashInfo(kind: ckWinException, code: uint32(ord(kind)), message: msg))
