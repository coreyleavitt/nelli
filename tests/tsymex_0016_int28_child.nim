## RFC-0016 INT-28 and INT-29 (0005 review R1-24, R1-31, R1-32, R2-21 to
## R2-27). The replay child's lifecycle, limits and start-up, through the host's
## entry points (`runReplayForked`, `runReplayReexec`):
##
## * INT-28: what the SUT starts dies with the child however the child ends,
##   and with the host; the child runs under memory, CPU, file-size and
##   process limits, and a run a limit stops is undecided, not a crash; the
##   replay count is exact under threads; a program whose file was deleted
##   still re-executes.
## * INT-29: a child that never took its witness (a failed `execve`, a report
##   it could not open) is no run, not a SUT crash; the private directory
##   admits its owner alone; a re-executed child inherits no descriptor the
##   host left open; a host with fd 0-2 closed still reads its report.
##
## Runs on every platform: Windows takes the re-executed path natively.
## `tsymex_0016_int28_child_reexec` runs it under `-d:nelliReplayReexec`.
import std/[unittest, os, osproc, strutils, strtabs, monotimes, times]
import nelli/smt/replayproc
from nelli/smt/canonicalize import symexWalkerVersion
from nelli/smt/admission import cellKey, axConstruct
from ./s8cu_helpers import pinNever
when replayReexecs:
  import std/streams

const posixChild = replayForks or replayExecs
  ## The child is a POSIX process: its descriptors and signals are the host's
  ## to arrange.

when posixChild:
  import std/posix
  proc fdOpen(fd: int): bool = fcntl(cint(fd), F_GETFD) != -1
  proc raiseSignal(n: int) =
    discard kill(getpid(), cint(n))
    sleep(5_000)
else:
  proc fdOpen(fd: int): bool = false
  proc raiseSignal(n: int) = discard

# ---- a grandchild: a process the SUT starts, beating into a file -------------
# First of all, so that a copy of this program started as one does nothing else.
if existsEnv("INT28_SLEEPER"):
  let path = getEnv("INT28_SLEEPER")
  let t0 = getMonoTime()
  while (getMonoTime() - t0).inSeconds < 60:
    try:
      let f = open(path, fmAppend)
      f.write('x')
      f.close()
    except CatchableError:
      discard
    sleep(50)
  quit(0)

proc beats(path: string): int64 =
  try: getFileSize(path) except CatchableError: 0

proc waitBeats(path: string; ms = 20_000): bool =
  let t0 = getMonoTime()
  while (getMonoTime() - t0).inMilliseconds < ms:
    if beats(path) > 0: return true
    sleep(20)
  false

proc stillBeating(path: string): bool =
  sleep(500)   # what was in flight lands
  let a = beats(path)
  sleep(1000)
  beats(path) > a

proc envWith(name, value: string): StringTableRef =
  result = newStringTable(modeCaseSensitive)
  for k, v in envPairs(): result[k] = v
  result[name] = value

proc startSleeper(path: string) =
  discard startProcess(getAppFilename(), env = envWith("INT28_SLEEPER", path),
                       options = {poParentStreams})

var nowhere {.volatile.}: ptr int = nil

proc spawnThen(path, ending: string): ReplayReport =
  ## A SUT that starts a grandchild, waits for it to beat, and then ends:
  ## `finish` returns, `quit` exits, `crash` faults.
  startSleeper(path)
  discard waitBeats(path, 10_000)
  case ending
  of "quit": quit(3)
  of "crash": nowhere[] = 1
  else: discard
  ReplayReport(reached: false, bound: true)

proc beatForever(path: string): ReplayReport =
  while true:
    try:
      let f = open(path, fmAppend)
      f.write('x')
      f.close()
    except CatchableError:
      discard
    sleep(50)

proc writeLimits(path: string): ReplayReport =
  let l = replayLimitsHeld()
  writeFile(path, $l.memory & " " & $l.cpuSeconds & " " & $l.fileSize & " " &
                  $l.processes)
  ReplayReport(bound: true)

proc runMode(mode: string): ReplayReport =
  ## What the SUT does, by name: `<kind>:<argument>`.
  let colon = mode.find(':')
  let kind = if colon < 0: mode else: mode[0 ..< colon]
  let arg = if colon < 0: "" else: mode[colon + 1 .. ^1]
  case kind
  of "spawn-finish": spawnThen(arg, "finish")
  of "spawn-quit": spawnThen(arg, "quit")
  of "spawn-crash": spawnThen(arg, "crash")
  of "beat": beatForever(arg)
  of "limits": writeLimits(arg)
  of "fd":
    # Whether descriptor `arg` is open in the child (a non-empty read of
    # its link, or a duplicate of it, says so).
    ReplayReport(reached: fdOpen(parseInt(arg)), bound: true)
  of "sig":
    raiseSignal(parseInt(arg))
    ReplayReport(bound: true)
  else: ReplayReport(bound: true)

# ---- the child's half (re-exec), and the host's ------------------------------

when replayReexecs:
  # RFC-0016 INT-29 (R2-22): a child whose report cannot be opened. Before the
  # site's entry, so it runs in the child before the entry opens the report:
  # the report becomes read-only (Windows) or a directory (POSIX, where root
  # writes a read-only file).
  if existsEnv("INT29_SPOIL_OUT"):
    let m = getEnv("NELLI_REPLAY_CHILD")
    let bar = m.find('|')
    if bar > 0:
      let outp = m[bar + 1 .. ^1] / "out"
      try: setFilePermissions(outp, {fpUserRead})
      except CatchableError: discard
      try:
        removeFile(outp)
        createDir(outp)
      except CatchableError: discard

  proc childRun(payload: string): ReplayReport {.nimcall.} =
    runMode(if payload.len > 8: payload[8 .. ^1] else: "")

  let registered {.used.} = replayChildEntry("int28-site", childRun)

proc payloadOf(mode: string): string =
  newString(8) & mode

template sut(e: untyped): untyped =
  proc (): ReplayReport {.closure, gcsafe.} =
    {.cast(gcsafe).}:
      result = (block:
        e)

proc runChild(mode: string; timeoutMs: int): ReplayChild =
  ## One replay of the SUT `mode`, forked or re-executed.
  when replayForks:
    let m = mode
    runReplayForked(sut(runMode(m)), timeoutMs)
  else:
    runReplayReexec("int28-site", payloadOf(mode), timeoutMs)

# A copy of this program whose own file is deleted before it replays (R1-32).
if existsEnv("INT28_DELETED_PROBE"):
  try: removeFile(getAppFilename())
  except CatchableError: discard
  let c = runChild("ok", 30_000)
  echo "PROBE ", c.ending, " why=", c.why
  quit(0)

# A host that replays a SUT beating without end, to be killed mid-replay.
if existsEnv("INT28_HOST"):
  discard runChild("beat:" & getEnv("INT28_HOST"), 120_000)
  quit(0)

suite "INT-28: the walker version":
  test "walker 404: a child that never ran, or a limit stopped, is no crash":
    check parseInt(symexWalkerVersion) >= 404

proc scratch(name: string): string =
  getTempDir() / ("int28-" & name & "-" & $getCurrentProcessId() & "-" &
                  $getMonoTime().ticks)

proc counted(n: int) {.thread.} =
  {.cast(gcsafe).}:
    for i in 0 ..< n:
      discard runChild("ok", 30_000)

suite "INT-28: what the SUT starts dies with the child":
  for ending in ["finish", "quit", "crash"]:
    test "a child that ends by itself (" & ending & ") takes its grandchild":
      let path = scratch("beat")
      defer: removeFile(path)
      let c = runChild("spawn-" & ending & ":" & path, 30_000)
      checkpoint describe(c)
      let ran = beats(path) > 0
      let dead = not stillBeating(path)
      check ran
      check dead
      pinNever(cellKey(axConstruct, "replay/child/lifecycle"), ran and dead,
        "the SUT's grandchild beat, and stopped beating once its child ended (" &
        ending & ")")

  test "a host that dies takes its replay's child with it":
    let path = scratch("host")
    defer: removeFile(path)
    let p = startProcess(getAppFilename(), env = envWith("INT28_HOST", path),
                         options = {poParentStreams})
    check waitBeats(path, 30_000)
    p.kill()
    discard p.waitForExit()
    p.close()
    check not stillBeating(path)

suite "INT-28: the child's limits":
  test "memory and processes are limited, and below the host's":
    let path = scratch("limits")
    defer: removeFile(path)
    let c = runChild("limits:" & path, 30_000)
    checkpoint describe(c)
    check c.ending == reFinished
    let f = readFile(path).splitWhitespace()
    check f.len == 4
    let host = replayLimitsHeld()
    let mem = parseBiggestInt(f[0])
    let procs = parseBiggestInt(f[3])
    checkpoint "child " & f.join(" ") & "; host " & $host
    check mem > 0
    check host.memory < 0 or mem < host.memory
    check procs > 0
    check host.processes < 0 or procs < host.processes
    pinNever(cellKey(axConstruct, "replay/child/limits"),
      mem > 0 and (host.memory < 0 or mem < host.memory) and procs > 0 and
        (host.processes < 0 or procs < host.processes),
      "the child's limits " & f.join(" ") & " sit below the host's " & $host)

  test "the replay count is exact when threads replay at once":
    let before = replayExecutions()
    var ts: array[4, Thread[int]]
    for t in ts.mitems: createThread(t, counted, 10)
    joinThreads(ts)
    check replayExecutions() - before == 40

when replayReexecs:
  suite "INT-28: the re-executed program's file":
    test "a program whose file was deleted still replays":
      let copy = scratch("copy") & ExeExt
      copyFileWithPermissions(getAppFilename(), copy)
      defer:
        try: removeFile(copy)
        except CatchableError: discard
      let p = startProcess(copy, env = envWith("INT28_DELETED_PROBE", "1"),
                           options = {poStdErrToStdOut})
      let output = p.outputStream.readAll()
      let code = p.waitForExit()
      p.close()
      checkpoint output
      check code == 0
      check "PROBE reFinished" in output

  suite "INT-29: a child that never took its witness":
    test "a report it cannot open is no run, not a crash":
      putEnv("INT29_SPOIL_OUT", "1")
      let c = runChild("ok", 30_000)
      delEnv("INT29_SPOIL_OUT")
      checkpoint describe(c)
      check c.ending == reRefused
      check c.runDependent
      check "witness" in c.why

  suite "INT-29: the private directory":
    test "it admits its owner alone":
      let d = replayPrivateDir()
      check d.len > 0
      defer: removeDir(d)
      let icacls = findExe("icacls")
      if icacls.len > 0:
        let (o, code) = execCmdEx(quoteShell(icacls) & " " & quoteShell(d))
        checkpoint o
        check code == 0
        check "(I)" notin o
        var aces = 0
        for line in o.splitLines:
          if ":(" in line: inc aces
        check aces == 1
        pinNever(cellKey(axConstruct, "replay/child/startup"),
          code == 0 and "(I)" notin o and aces == 1,
          "icacls: the private directory names one ACE and inherits none")
      else:
        let perms = getFilePermissions(d)
        check perms == {fpUserRead, fpUserWrite, fpUserExec}
        pinNever(cellKey(axConstruct, "replay/child/startup"),
          perms == {fpUserRead, fpUserWrite, fpUserExec},
          "the private directory's mode is 0700")

suite "INT-28: a run a limit stops is undecided":
  test "each limit's signal reads as stopped at that limit":
    # Every signal the platform's limits stop a child with; none on Windows.
    for (sig, limit) in replayLimitSignals():
      let c = runChild("sig:" & $sig, 30_000)
      checkpoint limit & ": " & describe(c)
      check c.ending == reTimedOut
      check limit in c.why

  test "CPU and file size are limited where a signal enforces them":
    let path = scratch("limits")
    defer: removeFile(path)
    let c = runChild("limits:" & path, 30_000)
    check c.ending == reFinished
    let f = readFile(path).splitWhitespace()
    var limits: seq[string]
    for (_, limit) in replayLimitSignals(): limits.add limit
    check (parseBiggestInt(f[1]) > 0) == ("CPU" in limits)
    check parseBiggestInt(f[2]) ==
      (if "file-size" in limits: replayFileSizeLimit else: -1'i64)

when posixChild:
  suite "INT-29: a host with fd 0-2 closed":
    test "its report still arrives":
      let saved = [dup(0), dup(1), dup(2)]
      for i in 0 .. 2: discard close(cint(i))
      let c = runChild("ok", 30_000)
      for i in 0 .. 2:
        discard dup2(saved[i], cint(i))
        discard close(saved[i])
      checkpoint describe(c)
      check c.ending == reFinished
      check c.bound
      pinNever(cellKey(axConstruct, "replay/child/startup"),
        c.ending == reFinished and c.bound,
        "a host with fd 0-2 closed read the child's report: " & describe(c))

  when replayExecs:
    suite "INT-29: the re-executed child's start":
      test "it inherits no descriptor the host left open":
        let null = posix.open("/dev/null", O_RDONLY)   # no O_CLOEXEC
        check null >= 0
        let hi = dup2(null, 200)
        discard close(null)
        defer: discard close(hi)
        let c = runChild("fd:200", 30_000)
        checkpoint describe(c)
        check c.ending == reFinished
        check not c.reached

      test "a failed execve is no run, not a crash":
        putEnv("INT29_BIG", repeat('x', 200_000))   # past MAX_ARG_STRLEN
        let c = runChild("ok", 30_000)
        delEnv("INT29_BIG")
        checkpoint describe(c)
        check c.ending == reRefused
        check c.runDependent
