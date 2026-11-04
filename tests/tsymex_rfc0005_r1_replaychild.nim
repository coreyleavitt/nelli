## RFC-0005 0.9.1 review, R1-18, R1-19, R1-20, R1-23 (marker), R1-30 -- the
## host's half of a replay child (`replayproc.nim`) holds against a child that
## misbehaves, and against the world around it.
##
## * R1-18: a child that hits its label millions of times, or writes into the
##   report pipe without end, neither takes the host past the replay's bound nor
##   grows its memory. Before: one `H` byte per hit, and the host decoded the
##   whole buffer again on every read (quadratic, and unbounded with no bound).
## * R1-19: a child whose exit status the host cannot get (the host ignores
##   `SIGCHLD`, so the kernel reaps it) is never reported as "exited with code
##   0", and the re-executing host does not spin to its bound and then signal a
##   pid that is no longer its child.
## * R1-20 (re-exec only): the files a re-executed child is handed live in a
##   private directory, created exclusively; a symlink planted at the old
##   predictable name is never followed.
## * R1-23 (re-exec only): a `NELLI_REPLAY_CHILD` the program inherited from its
##   environment, not one its host set for it, is ignored: the program neither
##   refuses every replay nor takes itself for a replay's child.
##
## * Review R2 (LV1, LV2): a child whose status was lost had started, so its
##   replay is not "declined" (that let its witness run in the host); and a
##   child stopped for flooding its report says so in its hint.
##
## `tsymex_rfc0005_r1_replaychild_reexec` runs this file under
## `-d:nelliReplayReexec`.
import std/[unittest, os, osproc, strutils, strtabs, monotimes, times, sequtils, streams]
import std/posix
import nelli/engine/markers
import nelli/smt/replayproc
import nelli/smt/replayresult
import nelli/smt/types

proc msSince(t: MonoTime): int64 = (getMonoTime() - t).inMilliseconds

proc hitLoop(n: int): ReplayReport =
  ## A SUT that reaches its label `n` times, as the replay body runs it.
  symexCaptureBegin()
  armReplayHit("t")
  for i in 0 ..< n:
    symexTarget("t")
  discard symexCaptureEnd()
  ReplayReport(reached: true, bound: true)

proc floodPipes() =
  ## A SUT that writes into every pipe it holds, without end.
  var junk = newString(65536)
  for i in 0 ..< junk.len: junk[i] = 'H'
  while true:
    for fd in 3.cint .. 255.cint:
      var st: Stat
      if fstat(fd, st) == 0 and S_ISFIFO(st.st_mode):
        discard write(fd, addr junk[0], junk.len)

proc killSelf() =
  discard kill(getpid(), SIGKILL)

proc hitThenKill(): ReplayReport =
  ## A SUT that reaches its label, then is killed before it returns.
  symexCaptureBegin()
  armReplayHit("t")
  symexTarget("t")
  killSelf()
  ReplayReport(reached: true, bound: true)

# ---- re-exec: the child's half, and a probe of this program as a host ---------

when replayReexecs:
  proc childRun(payload: string): ReplayReport {.nimcall.} =
    let mode = if payload.len > 8: payload[8 .. ^1] else: ""
    case mode
    of "ok": ReplayReport(reached: false, bound: true)
    of "hits": hitLoop(3_000_000)
    of "kill":
      killSelf()
      ReplayReport()
    of "hitkill": hitThenKill()
    else: ReplayReport()

  let registered {.used.} = replayChildEntry("r1-replaychild-site", childRun)

  proc payloadOf(mode: string): string =
    newString(8) & mode

  # A copy of this program started with a marker in its environment
  # (`staleMarker` below): it replays once and says how that went.
  if existsEnv("R1_STALE_PROBE"):
    let c = runReplayReexec("r1-replaychild-site", payloadOf("ok"), 20_000)
    echo "PROBE ", c.ending, " bound=", c.bound, " why=", c.why
    quit(0)

  proc staleMarker(marker: string): string =
    ## What a copy of this program started with `marker` reports.
    var env = newStringTable(modeCaseSensitive)
    for k, v in envPairs(): env[k] = v
    env["NELLI_REPLAY_CHILD"] = marker
    env["R1_STALE_PROBE"] = "1"
    let p = startProcess(getAppFilename(), env = env,
                         options = {poStdErrToStdOut})
    let output = p.outputStream.readAll()
    let code = p.waitForExit()
    p.close()
    checkpoint "marker " & marker & ": exit " & $code & ", output " & output
    if code != 0: return "exit " & $code
    for line in output.splitLines:
      if line.startsWith("PROBE "): return line
    "no probe line"

template sut(e: untyped): untyped =
  ## A replay body, as the entry macros emit one.
  proc (): ReplayReport {.closure, gcsafe.} =
    {.cast(gcsafe).}:
      result = (block:
        e)

proc runChild(body: proc (): ReplayReport {.closure, gcsafe.};
              mode: string; timeoutMs: int): ReplayChild =
  ## One replay of `body` (fork) or of the site's `mode` (re-exec).
  when replayForks:
    runReplayForked(body, timeoutMs)
  else:
    runReplayReexec("r1-replaychild-site", payloadOf(mode), timeoutMs)

suite "R1-18: a flood of hits":
  test "three million hits are reported once, inside the bound":
    let t0 = getMonoTime()
    let c = runChild(sut(hitLoop(3_000_000)), "hits", 30_000)
    let ms = msSince(t0)
    checkpoint "ending " & $c.ending & ", " & $ms & " ms, " & describe(c)
    check c.ending == reFinished
    check c.reached
    check c.bound
    check ms < 15_000

when replayForks:
  suite "R1-18: a child that floods its report pipe":
    test "with a bound: killed long before the bound, nothing reached":
      let t0 = getMonoTime()
      let c = runReplayForked(sut((floodPipes(); ReplayReport())), 20_000)
      let ms = msSince(t0)
      checkpoint "ending " & $c.ending & ", " & $ms & " ms, " & describe(c)
      check ms < 10_000
      check c.ending == reTimedOut
      check c.runDependent
      check not c.reached
      # Review R2 (LV2): the hint says why it was stopped, not that it ran
      # past replayTimeoutMs.
      let r = replayResultOf(c, lossy = false)
      check r.outcome == roTimedOut
      for h in candidateHint(r, sxSat, "", "") & winnerHint(r, "a claim", ""):
        checkpoint h.msg
        check "wrote past" in h.msg
        check "replayTimeoutMs" notin h.msg

    test "with no bound: the host still returns":
      let t0 = getMonoTime()
      let c = runReplayForked(sut((floodPipes(); ReplayReport())), 0)
      let ms = msSince(t0)
      checkpoint "ending " & $c.ending & ", " & $ms & " ms, " & describe(c)
      check ms < 10_000
      check c.ending == reTimedOut
      check not c.reached

suite "R1-19: the child's exit status":
  test "a child killed by a signal is reported as signalled":
    let c = runChild(sut((killSelf(); ReplayReport())), "kill", 20_000)
    checkpoint describe(c)
    check c.ending == reSignalled
    check c.code == int(SIGKILL)

  test "SIGCHLD ignored: a signalled child is never exit 0":
    discard signal(SIGCHLD, SIG_IGN)
    defer: discard signal(SIGCHLD, SIG_DFL)
    let t0 = getMonoTime()
    let c = runChild(sut((killSelf(); ReplayReport())), "kill", 5_000)
    let ms = msSince(t0)
    checkpoint "ending " & $c.ending & ", " & $ms & " ms, " & describe(c)
    check not (c.ending == reExited and c.code == 0)
    check c.ending == reLost
    check c.runDependent
    check "status" in c.why
    check ms < 4_000
    # Review R2 (LV1): a child that started is not one that did not run. It
    # ended its process before reaching the target, as far as anyone knows.
    let r = replayResultOf(c, lossy = false)
    check r.outcome == roCrashed
    check r.runDependence == {rdReplay}

  test "SIGCHLD ignored: a reach before the status was lost is confirmed":
    discard signal(SIGCHLD, SIG_IGN)
    defer: discard signal(SIGCHLD, SIG_DFL)
    let c = runChild(sut(hitThenKill()), "hitkill", 5_000)
    checkpoint "ending " & $c.ending & ", " & describe(c)
    check c.ending == reLost
    check c.reached
    let r = replayResultOf(c, lossy = true)
    check r.outcome == roConfirmed
    check r.replayStatus == rsConfirmed
    var unsafe = false
    let hints = confirmedEnding(r, sxSat, "", "", unsafe)
    check unsafe          # never run in the host
    check hints.len == 1

  test "SIGCHLD ignored: a child that finished is read as finished":
    discard signal(SIGCHLD, SIG_IGN)
    defer: discard signal(SIGCHLD, SIG_DFL)
    let t0 = getMonoTime()
    let c = runChild(sut(ReplayReport(reached: false, bound: true)), "ok",
                     5_000)
    let ms = msSince(t0)
    checkpoint "ending " & $c.ending & ", " & $ms & " ms, " & describe(c)
    check c.ending == reFinished
    check c.bound
    check ms < 4_000

when replayReexecs:
  suite "R1-20: the re-executed child's files":
    test "a symlink at the old predictable name is not followed":
      let tmp = getTempDir()
      let victim = tmp / ("r1-victim-" & $getCurrentProcessId())
      writeFile(victim, "precious")
      var planted: seq[string]
      for n in 1 .. 64:
        let base = tmp / ("nelli-replay-" & $getCurrentProcessId() & "-" & $n)
        for ext in [".in", ".out"]:
          let p = base & ext
          if symlink(victim.cstring, p.cstring) == 0: planted.add p
      defer:
        for p in planted: discard unlink(p.cstring)
        removeFile(victim)
      check planted.len > 0
      let c = runReplayReexec("r1-replaychild-site", payloadOf("ok"), 20_000)
      checkpoint describe(c)
      check readFile(victim) == "precious"
      check c.ending == reFinished
      check c.bound

    test "no replay file is left in the temporary directory":
      let before = toSeq(walkDir(getTempDir())).len
      let c = runReplayReexec("r1-replaychild-site", payloadOf("ok"), 20_000)
      check c.ending == reFinished
      check toSeq(walkDir(getTempDir())).len == before

  suite "R1-23: a marker the host did not set":
    test "a stale marker naming this site: the program runs as a host":
      check staleMarker("r1-replaychild-site|/nonexistent/in|/nonexistent/out") ==
        "PROBE reFinished bound=true why="

    test "a stale marker naming another site: replays are not refused":
      check staleMarker("elsewhere|/nonexistent/in|/nonexistent/out") ==
        "PROBE reFinished bound=true why="

    test "a stale marker of the current shape: ignored":
      check staleMarker("00112233445566778899aabbccddeeff|/nonexistent") ==
        "PROBE reFinished bound=true why="
