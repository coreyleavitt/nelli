## RFC-fuzzer-nextgen E4a (C1): the platform-independent worker-protocol
## seam (`nelli/workerproto`) — frame encode/decode, the observation-lite
## codec, argv call-site-ID dispatch, the bootstrap circuit-breaker policy,
## and the Job-Object limit-threshold policy.
##
## Pure algebra, no process spawns, no `when defined(posix)` gating: every
## behavior here is a `seq[byte] -> seq[byte]` transform or a fold over a
## synthetic event sequence (the same "pure algebra over fakes" precedent
## `tests/tfuzzrespawnstorm.nim` uses for the sibling steady-state
## respawn-storm breaker) — this is the whole point of factoring
## `workerproto.nim` out of the POSIX-only `fuzzworker.nim`: it must compile
## and run identically on Linux and (via `dt-crosswin.sh`) cross-compile
## clean for Windows, since the not-yet-written Windows worker glue (E4a
## cycle 2) will consume the exact same module.

import std/[unittest, options, strutils, times]
import nelli
import nelli/binaryio

suite "workerproto: frame encode/decode round-trip":
  test "encodeFrame then decodeFrameHeader/decodeFrameBody recovers the exact payload":
    for payload in @[
      newSeq[byte](0),
      @[1'u8, 2'u8, 3'u8, 255'u8, 0'u8],
      newSeq[byte](4096),
    ]:
      let wire = encodeFrame(payload)
      let hdr = wire[0 ..< 12]
      let length = decodeFrameHeader(hdr)
      check length == payload.len
      let body = wire[12 .. ^1]
      let got = decodeFrameBody(length, body)
      check got == payload

  test "encodeFrame rejects a payload over the max frame size":
    let tooBig = newSeq[byte](nelliMaxFrameBytes + 1)
    expect(FrameError):
      discard encodeFrame(tooBig)

  test "decodeFrameHeader rejects a header of the wrong length":
    expect(FrameError):
      discard decodeFrameHeader(@[1'u8, 2'u8, 3'u8])

  test "decodeFrameHeader rejects a bad magic":
    var hdr: seq[byte]
    hdr.putU32(0xDEADBEEF'u32)
    hdr.putU32(1'u32)
    hdr.putU32(0'u32)
    expect(FrameError):
      discard decodeFrameHeader(hdr)

  test "decodeFrameHeader rejects an unsupported version":
    var hdr: seq[byte]
    hdr.putU32(0x464C454E'u32)
    hdr.putU32(99'u32)
    hdr.putU32(0'u32)
    expect(FrameError):
      discard decodeFrameHeader(hdr)

  test "decodeFrameHeader rejects a length prefix over the max frame size":
    var hdr: seq[byte]
    hdr.putU32(0x464C454E'u32)
    hdr.putU32(1'u32)
    hdr.putU32(uint32(nelliMaxFrameBytes) + 1'u32)
    expect(FrameError):
      discard decodeFrameHeader(hdr)

  test "decodeFrameBody rejects a truncated body":
    let wire = encodeFrame(@[1'u8, 2'u8, 3'u8])
    let length = decodeFrameHeader(wire[0 ..< 12])
    expect(FrameError):
      discard decodeFrameBody(length, wire[12 ..< wire.len - 1])   # drop the last byte

  test "decodeFrameBody rejects a checksum mismatch":
    var wire = encodeFrame(@[1'u8, 2'u8, 3'u8])
    wire[wire.len - 1] = wire[wire.len - 1] xor 0xFF'u8   # corrupt the checksum's last byte
    let length = decodeFrameHeader(wire[0 ..< 12])
    expect(FrameError):
      discard decodeFrameBody(length, wire[12 .. ^1])

suite "workerproto: observation-lite codec round-trip":
  test "vOk with no crash round-trips":
    let obs = Observation[void](verdict: vOk, message: "fine")
    let got = decodeObservationLite[void](encodeObservationLite(obs))
    check got.verdict == vOk
    check got.crash.isNone
    check got.message == "fine"

  test "each CrashKind variant round-trips its typed payload":
    let cases = @[
      CrashInfo(kind: ckException, defect: "AssertionDefect", message: "m1"),
      CrashInfo(kind: ckSignal, signal: 11, message: "m2"),
      CrashInfo(kind: ckExitCode, exitCode: 42, message: "m3"),
      CrashInfo(kind: ckWinException, code: 0xC0000005'u32, message: "m4"),
    ]
    for c in cases:
      let obs = Observation[void](verdict: vCrashed, crash: some(c), message: c.message)
      let got = decodeObservationLite[void](encodeObservationLite(obs))
      check got.verdict == vCrashed
      check got.crash.isSome
      check got.crash.get.kind == c.kind
      check got.crash.get.message == c.message
      case c.kind
      of ckException: check got.crash.get.defect == c.defect
      of ckSignal: check got.crash.get.signal == c.signal
      of ckExitCode: check got.crash.get.exitCode == c.exitCode
      of ckWinException: check got.crash.get.code == c.code

suite "workerproto: argv call-site-ID dispatch":
  test "parseWorkerModeId returns \"\" for ordinary argv (not worker mode)":
    check parseWorkerModeId(@[]) == ""
    check parseWorkerModeId(@["--verbose", "somefile.nim"]) == ""

  test "parseWorkerModeId extracts the id from a --nelli-worker= flag":
    check parseWorkerModeId(@["--nelli-worker=site42"]) == "site42"
    check parseWorkerModeId(@["--other", "--nelli-worker=abc123"]) == "abc123"

  test "parseWorkerModeId does not match a bare/partial prefix":
    check parseWorkerModeId(@["--nelli-worker"]) == ""
    check parseWorkerModeId(@["nelli-worker=x"]) == ""

  test "workerArgv builds the self-re-exec argv":
    check workerArgv("/bin/myapp", "site7") == @["/bin/myapp", "--nelli-worker=site7"]
    # Round-trips through parseWorkerModeId on the tail (argv[1..]):
    let argv = workerArgv("/bin/myapp", "site7")
    check parseWorkerModeId(argv[1 .. ^1]) == "site7"

  test "workerEnv drops inherited transport knobs and adds the requested ones":
    let inherited = @[("PATH", "/usr/bin"), ("NELLI_COV_FILE", "/stale/path"),
                       ("NELLI_COV_SHM", "/stale/shm"), ("NELLI_CMP_SHM", "/stale/cmp")]
    let env = workerEnv(inherited, covFile = "/fresh/cov.bin")
    check "PATH=/usr/bin" in env
    check "NELLI_COV_FILE=/fresh/cov.bin" in env
    for kv in env:
      check not kv.startsWith("NELLI_COV_SHM=")
      check not kv.startsWith("NELLI_CMP_SHM=")

  test "workerEnv with nothing set carries only the filtered inherited pairs":
    let inherited = @[("PATH", "/usr/bin"), ("NELLI_COV_FILE", "/stale")]
    let env = workerEnv(inherited)
    check env == @["PATH=/usr/bin"]

  test "workerEnv can set covShm and cmpShm independently of covFile":
    let env = workerEnv(@[], covShm = "/shm/cov", cmpShm = "/shm/cmp")
    check "NELLI_COV_SHM=/shm/cov" in env
    check "NELLI_CMP_SHM=/shm/cmp" in env
    for kv in env:
      check not kv.startsWith("NELLI_COV_FILE=")

suite "workerproto: bootstrap circuit-breaker policy (RFC §Open-items, E4a)":
  test "threshold <= 0 disables the breaker regardless of consecutive deaths":
    var b = newBootstrapBreaker(0)
    for _ in 0 ..< 100: b.recordDeadBeforeFirstRead()
    check not b.tripped
    check b.diagnostic.len == 0

  test "fewer than N consecutive deaths does not trip":
    var b = newBootstrapBreaker(3)
    b.recordDeadBeforeFirstRead()
    b.recordDeadBeforeFirstRead()
    check not b.tripped
    check b.consecutiveDeaths == 2

  test "N consecutive dead-before-first-read spawns trips with a distinct diagnostic":
    var b = newBootstrapBreaker(3)
    b.recordDeadBeforeFirstRead()
    b.recordDeadBeforeFirstRead()
    check not b.tripped
    b.recordDeadBeforeFirstRead()
    check b.tripped
    check "construction-not-reentrant" in b.diagnostic
    # Distinct from the sibling steady-state respawn-storm breaker's
    # diagnostic wording (fuzz.nim's `RespawnStormError`/`stormDiagnostic`,
    # which reads "respawn-storm: ...") — a caller must be able to tell the
    # two failure modes apart from the message alone.
    check "respawn-storm" notin b.diagnostic

  test "a successful first read resets the consecutive-death streak and un-trips":
    var b = newBootstrapBreaker(2)
    b.recordDeadBeforeFirstRead()
    b.recordDeadBeforeFirstRead()
    check b.tripped
    b.recordFirstReadSucceeded()
    check not b.tripped
    check b.consecutiveDeaths == 0
    check b.diagnostic.len == 0
    # And the count starts fresh — one more death alone must not re-trip a
    # threshold-2 breaker.
    b.recordDeadBeforeFirstRead()
    check not b.tripped

suite "workerproto: Job-Object limit-threshold policy (E4a; syscalls are E4c)":
  test "jobLimitPolicy derives its thresholds from ResourceLimits":
    let limits = ResourceLimits(addressSpaceBytes: 1_000_000, cpuSeconds: 30,
                                 perRunTimeout: initDuration(milliseconds = 5000))
    let policy = jobLimitPolicy(limits)
    check policy.memoryBytes == 1_000_000
    check policy.cpuSeconds == 30
    check policy.wallClockMs == 5000

  test "jobLimitPolicy leaves unset ResourceLimits fields at their 0-means-unset value":
    let policy = jobLimitPolicy(ResourceLimits())
    check policy.memoryBytes == 0
    check policy.cpuSeconds == 0
    check policy.wallClockMs == 0

  test "verdictForJobLimit always maps to vResourceExceeded with a ckWinException crash":
    for kind in [jlkMemory, jlkCpu, jlkWallClock]:
      let (verdict, crash) = verdictForJobLimit(kind)
      check verdict == vResourceExceeded
      check crash.kind == ckWinException
      check crash.code == uint32(ord(kind))
      check crash.message.len > 0

  test "verdictForJobLimit distinguishes each limit kind by its message":
    check "memory" in verdictForJobLimit(jlkMemory).crash.message
    check "cpu" in verdictForJobLimit(jlkCpu).crash.message
    check "wall-clock" in verdictForJobLimit(jlkWallClock).crash.message
