## RFC-0005 (soundness channels) slice S8ct -- no replay can end or corrupt the
## host process. A witness runs in a child (`replayproc.nim`): `fork` on POSIX, a
## re-execution of this binary on Windows (and on Linux under
## `-d:nelliReplayReexec`, `tsymex_rfc0005_s8ct_reexec`).
##
## RED before S8ct: this binary died at the first replay that reached `quit`, a
## nil dereference, unbounded recursion or a raw C `exit`, ending the whole run.
##
## Every row asserts three things: the host is still here (it reached the next
## line), the verdict is the one the row states, and a native run of the same SUT
## on the same kind of input agrees. A native run happens in a process of its own
## too (`nativeRun`): it really does die.
##
## "Declined" is `sxUnknown`. On a re-executing platform a SUT reaching what cannot
## be handed to a child does not run at all (`feReplayDeclined`), which the rows
## with a foreign routine or a proc value spell out.
import std/[unittest, strutils, os, osproc, streams, strtabs, exitprocs,
            typedthreads, monotimes, times, volatile]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/replayproc

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc msgOf(errs: seq[SymexErrorInfo]; k: SymexErrorKind): string =
  for e in errs:
    if e.kind == k: return e.msg
  ""

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

# ---- the SUTs ----------------------------------------------------------------
#
# `gG` is a module-level variable nothing writes: the walker's read of it is a
# fresh symbol (`feGlobalHavoc`, `dcFreshSymbol`), so a path past it is a replay
# candidate, on which the model may take `gG != 0`. It really holds 0.

var gG: int
var gN: ptr int
var gV: proc (k: int) {.nimcall.}

proc bye(c: int) = quit(c)

# B17: `quit`, directly and through a callee, before and after the label.
proc quitDirect(k: int) =
  if gG == 0:
    quit(7)
  symexTarget("t")

proc quitCallee(k: int) =
  if gG == 0:
    bye(7)
  symexTarget("t")

proc quitOnInput(k: int) =
  if gG == 0 and k == 3:
    quit(7)
  symexTarget("t")

proc labelThenQuit(k: int) =
  if k == 3:
    let a = gG
    symexTarget("t")
    quit(7 + a)

# S8cp item 3: `addExitProc`. Neither the SUT's nor the host's may run where they
# would do harm.
var hostPid = 0
var hostExitSentinel = ""
var sutExitSentinel = ""

proc sutExitProc() {.noconv.} =
  writeFile(sutExitSentinel, "the SUT's exit proc ran")

proc registerExitProc() {.symexOpaque.} =
  # Opaque because a walked `addExitProc` stops the compile: `classifyType`
  # recurses on `std/exitprocs`' state past the VM's call depth.
  addExitProc(sutExitProc)

proc quitWithExitProc(k: int) =
  if gG == 0:
    registerExitProc()
    quit(7)
  symexTarget("t")

# B18, B19.
proc nilDeref(k: int) =
  if gG == 0:
    gN[] = 1
  symexTarget("t")

proc recur(n: int): int =
  # The sort's probe holds `array[4096, int]`, whose access at `n and 7` now
  # declines (`arrayAccessTooWide`); `tsymex_rfc0005_s8ct_deepterm` pins that
  # SUT. This frame is modelled, so the row still decides.
  var pad: array[64, int]
  pad[n and 7] = n
  recur(n + 1) + pad[n and 7]

proc unboundedRecursion(k: int) =
  if gG == 0:
    discard recur(k)
  symexTarget("t")

# W1, W2: behind an opaque. Main gave a false sxSat for these.
proc cExit(c: cint) {.importc: "exit", header: "<stdlib.h>".}
proc cExitOpaque(k: int) {.symexOpaque.} = cExit(7)
proc rawExit(k: int) =
  symexAssume(k == 3)
  cExitOpaque(k)
  symexTarget("t")

proc quitLeaf(k: int) {.nimcall.} = quit(7)
proc procValueOpaque(k: int) {.symexOpaque.} = gV(k)
proc quitByProcValue(k: int) =
  symexAssume(k == 3)
  procValueOpaque(k)
  symexTarget("t")

# Anything else a real run can reach.
proc cAbort() {.importc: "abort", header: "<stdlib.h>".}
proc abortOpaque(k: int) {.symexOpaque.} = cAbort()
proc abortCall(k: int) =
  symexAssume(k == 3)
  abortOpaque(k)
  symexTarget("t")

proc raiseDefect(k: int) =
  if gG == 0:
    raise newException(IndexDefect, "s8ct")
  symexTarget("t")

proc writesWild(k: int) {.symexOpaque.} =
  cast[ptr int](0x10)[] = k

proc wildWrite(k: int) =
  if gG == 0:
    writesWild(k)
  symexTarget("t")

proc allocationLoop(k: int) =
  if gG == 0:
    var hold: seq[seq[byte]]
    while true:
      hold.add newSeq[byte](1 shl 24)
  symexTarget("t")

proc hugeAllocation(k: int) =
  if gG == 0:
    let s = newSeq[byte](1 shl 44)
    gG = s.len
  symexTarget("t")

proc doubleDealloc(k: int) =
  if gG == 0:
    let p = alloc(64)
    dealloc(p)
    dealloc(p)
  symexTarget("t")

proc spins(k: int) =
  if gG == 0:
    var n = k
    while true:
      n = (n xor 1) or 1
      if n == 0: break
  symexTarget("t")

# The host's state is out of reach, whatever the child does to its copy.
var gHostValue = 11
var gHostSeq = @[1, 2, 3]

proc overwritesHost(k: int) {.symexOpaque.} =
  gHostValue = 99
  gHostSeq.setLen(0)
  gHostSeq.add 7

proc writesThenLabel(k: int) =
  symexAssume(k == 3)
  overwritesHost(k)
  symexTarget("t")

# ... and the child sees the host's state as it is now, not as it started.
var gRuntimeSet = 0

proc readsRuntimeState(k: int) =
  let v = gRuntimeSet
  if k == 5 and v == 41:
    symexTarget("t")

# §2.3 rule 3 still holds: confirmed is `rsConfirmed`, refuted stays unknown.
proc confirmed(k: int) =
  if gG == 0 and k == 42:
    symexTarget("t")

proc refuted(k: int) =
  if gG != 0 and k == 42:
    symexTarget("t")

# State the re-executed child cannot be handed: a routine's `{.global.}`.
proc routineGlobal(k: int) =
  var calls {.global.} = 0
  if gG == 0 and calls == 0 and k == 3:
    symexTarget("t")

# Threads at the fork. Another thread would end the wait, and in the child that
# thread does not exist.
var gHeld: int

proc waitsForHeldLock(k: int) {.symexTransparent.} =
  while volatileLoad(addr gHeld) != 0:
    discard

proc locked(k: int) =
  if gG == 0:
    waitsForHeldLock(k)
  symexTarget("t")

# ---- native runs -------------------------------------------------------------

proc nativeSink(name: string; depth: int) {.nimcall, gcsafe.} =
  {.cast(gcsafe).}:
    stdout.writeLine "HIT|" & name
    stdout.flushFile()

proc nativeMain(row: string; k: int) =
  gV = quitLeaf
  symexCaptureBegin()
  symexHitSink = nativeSink
  try:
    case row
    of "quitDirect": quitDirect(k)
    of "quitCallee": quitCallee(k)
    of "quitOnInput": quitOnInput(k)
    of "labelThenQuit": labelThenQuit(k)
    of "quitWithExitProc": quitWithExitProc(k)
    of "nilDeref": nilDeref(k)
    of "unboundedRecursion": unboundedRecursion(k)
    of "rawExit": rawExit(k)
    of "quitByProcValue": quitByProcValue(k)
    of "abortCall": abortCall(k)
    of "raiseDefect": raiseDefect(k)
    of "wildWrite": wildWrite(k)
    of "doubleDealloc": doubleDealloc(k)
    of "writesThenLabel": writesThenLabel(k)
    of "confirmed": confirmed(k)
    of "refuted": refuted(k)
    of "routineGlobal": routineGlobal(k)
    else: quit(250)
  except Exception as e:
    stdout.writeLine "RAISED|" & $e.name
    stdout.flushFile()

if getEnv("S8CT_NATIVE").len > 0:
  sutExitSentinel = getEnv("S8CT_SUT_SENTINEL")
  nativeMain(getEnv("S8CT_NATIVE"), parseInt(getEnv("S8CT_INPUT")))
  quit(0)

type Native = object
  rc: int
  hit: bool
  raised: string

proc nativeRun(row: string; k: int): Native =
  ## `row` on `k` in a process of its own.
  var env = newStringTable(modeCaseSensitive)
  for name, value in envPairs(): env[name] = value
  env["S8CT_NATIVE"] = row
  env["S8CT_INPUT"] = $k
  env["S8CT_SUT_SENTINEL"] = sutExitSentinel & ".native"
  let p = startProcess(getAppFilename(), env = env,
                       options = {poStdErrToStdOut})
  var output = ""
  try:
    output = p.outputStream.readAll()
  except IOError:
    discard
  result.rc = p.waitForExit(30_000)
  p.close()
  for line in output.splitLines():
    if line == "HIT|t": result.hit = true
    if line.startsWith("RAISED|"): result.raised = line[7 .. ^1]

# ---- the rows ----------------------------------------------------------------

const noSat = {sxUnknown, sxRaised}

template declinedByCrash(r: untyped; label: string) =
  ## The real fn ended its child: `sxUnknown`, saying so, or on a re-executing
  ## platform a SUT that did not run.
  checkpoint(label & ": " & show(r.errors))
  check r.status == sxUnknown
  when replayForks:
    check hasKind(r.errors, feReplayCrashed)
  else:
    check hasKind(r.errors, feReplayCrashed) or
          hasKind(r.errors, feReplayDeclined)

suite "S8ct: a replay cannot end the host":
  hostPid = getCurrentProcessId()
  hostExitSentinel = getTempDir() / ("s8ct-host-exit-" & $hostPid)
  sutExitSentinel = getTempDir() / ("s8ct-sut-exit-" & $hostPid)
  gV = quitLeaf

  test "B17: quit directly":
    let r = symexFind(quitDirect, tLabel("t"))
    declinedByCrash(r, "quitDirect")
    when replayForks:
      check "code 7" in msgOf(r.errors, feReplayCrashed)
    let n = nativeRun("quitDirect", 0)
    check n.rc == 7
    check not n.hit

  test "B17: quit through a callee":
    let r = symexFind(quitCallee, tLabel("t"))
    declinedByCrash(r, "quitCallee")
    let n = nativeRun("quitCallee", 0)
    check n.rc == 7
    check not n.hit

  test "B17: quit on one input only: a confirmed witness or a crash, never unsat":
    let r = symexFind(quitOnInput, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status != sxUnsat
    if r.status == sxSat:
      check r.witness[0] != 3
      check r.soundness.replay == rsConfirmed
      check nativeRun("quitOnInput", r.witness[0]).hit
    else:
      check hasKind(r.errors, feReplayCrashed)
      check "code 7" in msgOf(r.errors, feReplayCrashed)
      check "3" in msgOf(r.errors, feReplayCrashed)   # the input
    check nativeRun("quitOnInput", 3).rc == 7
    check nativeRun("quitOnInput", 4).hit

  test "a label hit before the quit is reached: a confirmed sxSat":
    let r = symexFind(labelThenQuit, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    let n = nativeRun("labelThenQuit", 3)
    check n.hit
    check n.rc == 7

  test "S8cp 3: addExitProc then quit: no exit proc runs in the host or for it":
    # Registered in the host, to tell whether a child ran the host's exit procs.
    let sentinel = hostExitSentinel
    {.cast(gcsafe).}:
      addExitProc(proc () =
        if getCurrentProcessId() != hostPid:
          writeFile(sentinel, "the host's exit proc ran in a child"))
    let r = symexFind(quitWithExitProc, tLabel("t"))
    declinedByCrash(r, "quitWithExitProc")
    check not fileExists(hostExitSentinel)
    check not fileExists(sutExitSentinel)
    let n = nativeRun("quitWithExitProc", 0)
    check n.rc == 7
    check fileExists(sutExitSentinel & ".native")   # natively it does run
    removeFile(sutExitSentinel & ".native")

  test "B18: nil deref":
    let r = symexFind(nilDeref, tLabel("t"))
    declinedByCrash(r, "nilDeref")
    when replayForks:
      check "signal" in msgOf(r.errors, feReplayCrashed)
    let n = nativeRun("nilDeref", 0)
    check n.rc != 0
    check not n.hit

  test "B19: unbounded recursion":
    # With the sort's `array[4096, int]` this was not a replay's death: the
    # analysis ended the process, in S8by's `holds`. Here the replay of input 0
    # crashes, and input `high(int)` really does raise, at `n + 1`.
    let r = symexFind(unboundedRecursion, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status in noSat
    when replayForks:
      check hasKind(r.errors, feReplayCrashed)
    let n = nativeRun("unboundedRecursion", 0)
    check n.rc != 0
    check not n.hit
    if r.status == sxRaised:
      check r.raisedTypeId == "OverflowDefect"
      check nativeRun("unboundedRecursion", high(int)).raised == "OverflowDefect"

  test "W1: a raw C exit behind an opaque":
    let r = symexFind(rawExit, tLabel("t"))
    declinedByCrash(r, "rawExit")
    let n = nativeRun("rawExit", 3)
    check n.rc == 7
    check not n.hit

  test "W2: quit behind a proc value behind an opaque":
    let r = symexFind(quitByProcValue, tLabel("t"))
    declinedByCrash(r, "quitByProcValue")
    let n = nativeRun("quitByProcValue", 3)
    check n.rc == 7
    check not n.hit

  test "abort":
    let r = symexFind(abortCall, tLabel("t"))
    declinedByCrash(r, "abortCall")
    let n = nativeRun("abortCall", 3)
    check n.rc != 0
    check not n.hit

  test "a raised Defect is what it is, not a crash and not unsat":
    let r = symexFind(raiseDefect, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status in noSat
    check not hasKind(r.errors, feReplayCrashed)
    let n = nativeRun("raiseDefect", 0)
    check n.raised == "IndexDefect"
    check not n.hit
    if r.status == sxRaised:
      check r.raisedTypeId == "IndexDefect"

  test "a wild write":
    let r = symexFind(wildWrite, tLabel("t"))
    declinedByCrash(r, "wildWrite")
    let n = nativeRun("wildWrite", 0)
    check n.rc != 0
    check not n.hit

  test "an allocation loop fails in the child, which the host outlives":
    # Not run natively: it would take the machine's memory.
    let r = symexFind(allocationLoop, tLabel("t"))
    declinedByCrash(r, "allocationLoop")

  test "one allocation past the limit":
    let r = symexFind(hugeAllocation, tLabel("t"))
    declinedByCrash(r, "hugeAllocation")

  test "a double dealloc: whatever it does, it does to the child":
    let r = symexFind(doubleDealloc, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status != sxUnsat
    check nativeRun("doubleDealloc", 0).rc >= 0
    # The host's own heap still works.
    var s = newSeq[int](4096)
    s[4095] = 1
    check s[4095] == 1

  test "a replay that never ends is killed at its bound and leaves nothing behind":
    const lim = SymexSettings(replayTimeoutMs: 300)
    let t0 = getMonoTime()
    let r = symexFind(spins, tLabel("t"), lim)
    checkpoint(show(r.errors))
    check r.status == sxUnknown
    check hasKind(r.errors, feReplayTimedOut)
    check (getMonoTime() - t0).inSeconds < 50
    # No abandoned thread: the next replay of the same state is not disturbed.
    check symexFind(confirmed, tLabel("t")).status == sxSat

suite "S8ct: a replay cannot corrupt the host":
  test "the child's writes do not reach the host":
    gHostValue = 11
    gHostSeq = @[1, 2, 3]
    let r = symexFind(writesThenLabel, tLabel("t"))
    checkpoint(show(r.errors))
    when replayForks:
      check r.status == sxSat
    check gHostValue == 11
    check gHostSeq == @[1, 2, 3]

  test "the child runs on the host's state as it is at the replay":
    gRuntimeSet = 41
    let r = symexFind(readsRuntimeState, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed

  test "many replays: no descriptor or child is left behind":
    when defined(linux):
      proc openFds(): int =
        for _ in walkDir("/proc/self/fd"): inc result
      let before = openFds()
    let runs = replayExecutions()
    for i in 0 ..< 40:
      discard symexFind(confirmed, tLabel("t"))
    check replayExecutions() - runs >= 40
    when defined(linux):
      check openFds() == before

suite "S8ct: §2.3 rule 3 still holds":
  test "a confirmed witness is sxSat with rsConfirmed":
    let r = symexFind(confirmed, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status == sxSat
    check r.soundness.replay == rsConfirmed
    check r.witness[0] == 42
    check nativeRun("confirmed", 42).hit

  test "a refuted witness stays sxUnknown":
    let r = symexFind(refuted, tLabel("t"))
    checkpoint(show(r.errors))
    check r.status == sxUnknown
    check hasKind(r.errors, feReplayRefuted)
    check not nativeRun("refuted", 42).hit

  test "state the wire cannot carry: Linux decides, re-exec names why not":
    let r = symexFind(routineGlobal, tLabel("t"))
    checkpoint(show(r.errors))
    when replayReexecs:
      check r.status == sxUnknown
      check hasKind(r.errors, feReplayDeclined)
      check "replay not marshallable" in show(r.errors)
      check "a Linux or macOS run forks and replays it" in show(r.errors)
    else:
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed
    check nativeRun("routineGlobal", 3).hit

  test "the walker's version floor":
    check parseInt(symexWalkerVersion) >= 256

when replayForks:
  type Worker = object
    stop: bool

  var gWorker: Worker
  var gWorkerThread: Thread[void]

  proc busyWorker() {.thread.} =
    {.cast(gcsafe).}:
      volatileStore(addr gHeld, 1)
      while not volatileLoad(addr gWorker.stop):
        var s = newSeq[int](1024)
        s[0] = 1
      volatileStore(addr gHeld, 0)

  suite "S8ct: fork with other threads alive":
    test "a running thread does not exist in the child, and is unharmed":
      createThread(gWorkerThread, busyWorker)
      sleep(50)
      let r = symexFind(confirmed, tLabel("t"))
      check r.status == sxSat
      check r.soundness.replay == rsConfirmed

    test "what another thread would have ended stays waiting: the bound ends it":
      const lim = SymexSettings(replayTimeoutMs: 300)
      let r = symexFind(locked, tLabel("t"), lim)
      checkpoint(show(r.errors))
      check r.status == sxUnknown
      check hasKind(r.errors, feReplayTimedOut)
      volatileStore(addr gWorker.stop, true)
      joinThread(gWorkerThread)
