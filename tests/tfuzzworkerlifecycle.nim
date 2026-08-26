## RFC-fuzzer-nextgen E-cleanup (C2): workers die with the orchestrator
## (POSIX) — `PR_SET_PDEATHSIG`.
##
## The hazard: a persistent worker (E2a/E2b) can be deep inside dispatching
## an input (e.g. a hung target) when its orchestrator dies (OOM-killed,
## Ctrl-C'd). Such a worker never comes back around to notice anything about
## its parent — not even a closed input pipe, since it isn't calling `read`
## on it at that moment — so it would otherwise survive its dead
## orchestrator forever. `PR_SET_PDEATHSIG` is the kernel-enforced backstop:
## armed in the child BEFORE `execvpe` (the setting survives exec), the
## kernel delivers `SIGKILL` to the worker the instant its parent process
## dies, no matter what it's doing at that moment.
##
## Test structure (three process levels, all necessary, none racy): this
## test binary (marked `PR_SET_CHILD_SUBREAPER`) forks a stand-in
## "orchestrator" process, which spawns a REAL worker via the actual
## `spawnWorkerProcess` (fork+exec of this SAME binary in
## `--nelli-worker=` mode) and dispatches it an input that hangs FOREVER on
## the worker's OWN self-referential pipe — deliberately decoupled from any
## fd the orchestrator itself holds, so nothing about the orchestrator's fd
## lifetime could incidentally unblock it. The test then SIGKILLs the
## surrogate orchestrator (unblockable/uncatchable — faithfully modeling an
## OOM kill) and asserts the worker does not survive it. Marking the test
## process a child-subreaper makes the worker reparent to IT (not init) once
## the orchestrator dies, so the final `waitpid` is a genuine BLOCKING,
## non-polling wait — deterministic, not a sleep-loop race.

import std/[unittest, options, strutils]
import nelli
import nelli/[datasource, rng, serialize]

# Same reason as `tfuzzworkerprocess.nim`: a re-exec'd worker child is
# launched with `--nelli-worker=<id>` on argv, which `std/unittest` would
# otherwise treat as a test-name glob filter.
disableParamFiltering()

when defined(posix):
  import std/posix

  proc drawChoicesFor(lo, hi: int; seedBase: uint64; pred: proc(n: int): bool): ChoiceSeq =
    ## Draws a real, strategy-valid `ChoiceSeq` for `integers(lo, hi)` whose
    ## generated value matches `pred` — never hand-built, so replay stays
    ## strategy-valid (same discipline as `tfuzzworkerprocess.nim`'s own
    ## `drawUntil`).
    for attempt in 0'u64 ..< 10_000'u64:
      var ds = newDataSource(initSplitMix64(seedBase + attempt))
      let v = integers(lo, hi).generate(ds)
      if pred(v): return ds.recorded
    doAssert false, "could not draw a value matching the predicate"

  proc hangingProp(n: int) {.cover.} =
    ## Hangs FOREVER for `n == 42`, but ONLY inside a genuine re-exec'd
    ## worker (`nelliWorkerModeId.len > 0`) — the front-door registration
    ## call below runs this in-process once too, and must never hang
    ## regardless of what value its own (unrelated) draw happens to produce.
    if n == 42 and nelliWorkerModeId.len > 0:
      var p: array[2, cint]
      discard posix.pipe(p)
      var buf: array[1, byte]
      discard posix.read(p[0], addr buf[0], 1)   # blocks forever: p[1] is never written

  proc readPidFrom(fd: cint): Pid =
    var buf: array[32, byte]
    let n = posix.read(fd, addr buf[0], buf.len)
    doAssert n > 0, "expected the surrogate orchestrator to report the worker pid"
    var s = newString(n)
    copyMem(addr s[0], addr buf[0], n)
    Pid(parseInt(s.strip))

  suite "fuzz: workers die with the orchestrator (RFC-fuzzer-nextgen E-cleanup C2)":
    test "a worker hung inside dispatch does not outlive a SIGKILL'd orchestrator":
      setChildSubreaper()

      discard fuzz(integers(0, 100), hangingProp, FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0
      let hangChoices = drawChoicesFor(0, 100, 1'u64, proc(n: int): bool = n == 42)

      var qPipe: array[2, cint]
      discard posix.pipe(qPipe)

      let orchPid = fork()
      doAssert orchPid >= 0, "fork (surrogate orchestrator) failed"
      if orchPid == 0:
        # --- surrogate "orchestrator" process ---
        discard close(qPipe[0])
        let (workerPid, inFd, outFd) = spawnWorkerProcess(id, "")
        writeFrame(inFd, toBytes(hangChoices))   # dispatches the worker into the hang; never returns
        discard outFd
        let pidMsg = $int(workerPid) & "\n"
        discard posix.write(qPipe[1], unsafeAddr pidMsg[0], pidMsg.len)
        discard close(qPipe[1])
        # Deliberately keep `inFd` open — a real orchestrator mid-campaign
        # would too, expecting to send more input later. Proves the
        # worker's death below is NOT just ordinary pipe-EOF.
        while true: discard pause()

      # --- test process ---
      discard close(qPipe[1])
      let workerPid = readPidFrom(qPipe[0])
      discard close(qPipe[0])

      discard kill(orchPid, SIGKILL)
      var orchStatus: cint = 0
      discard waitpid(orchPid, orchStatus, 0)
      check WIFSIGNALED(orchStatus)
      check WTERMSIG(orchStatus) == SIGKILL

      # A genuine BLOCKING wait: once the orchestrator dies, the worker
      # reparents to this (subreaper) process, and PR_SET_PDEATHSIG delivers
      # SIGKILL to it — this returns as soon as that happens, no polling.
      var workerStatus: cint = 0
      let reaped = waitpid(workerPid, workerStatus, 0)
      check reaped == workerPid
      check WIFSIGNALED(workerStatus)          # PDEATHSIG's kill, not a graceful exit
      check WTERMSIG(workerStatus) == SIGKILL

  # --- E-cleanup C3: process-group kill on orchestrator shutdown -------------
  #
  # The orchestrator-INITIATED counterpart to C2's kernel-enforced
  # PR_SET_PDEATHSIG: `isolateOwnProcessGroup`/`killWorkerGroup` let a
  # CLEAN-shutdown path (e.g. a caught SIGINT) tear down a worker's entire
  # process subtree — the worker itself plus any descendant IT forked (an
  # externally-fuzzed target process, say) — in one call, without needing
  # every descendant to have armed its own PDEATHSIG.

  proc blockForeverOnOwnPipe() =
    var p: array[2, cint]
    discard posix.pipe(p)
    var buf: array[1, byte]
    discard posix.read(p[0], addr buf[0], 1)   # blocks forever: p[1] is never written

  suite "fuzz: process-group kill on orchestrator shutdown (RFC-fuzzer-nextgen E-cleanup C3)":
    test "killWorkerGroup kills a plain worker, and the caller survives to see it":
      let workerPid = fork()
      doAssert workerPid >= 0, "fork (worker) failed"
      if workerPid == 0:
        blockForeverOnOwnPipe()
        quit(0)

      isolateOwnProcessGroup(workerPid)
      killWorkerGroup(workerPid)

      var status: cint = 0
      check waitpid(workerPid, status, 0) == workerPid
      check WIFSIGNALED(status)
      check WTERMSIG(status) == SIGKILL
      # Reaching this line at all proves the CALLER (this test process)
      # was not itself caught in the group's blast radius.

    test "killWorkerGroup also reaches a descendant the worker forked (group inheritance)":
      setChildSubreaper()   # the descendant reparents here once the worker dies

      var goPipe: array[2, cint]     # test -> worker: "your pgid is set now, go ahead and fork"
      discard posix.pipe(goPipe)
      var qPipe: array[2, cint]      # worker -> test: hands back its descendant's pid
      discard posix.pipe(qPipe)

      let workerPid = fork()
      doAssert workerPid >= 0, "fork (worker) failed"
      if workerPid == 0:
        discard close(goPipe[1])
        discard close(qPipe[0])
        var gobuf: array[1, byte]
        discard posix.read(goPipe[0], addr gobuf[0], 1)   # wait until OUR pgid is already isolated
        let descendantPid = fork()
        if descendantPid == 0:
          blockForeverOnOwnPipe()
          quit(0)
        let msg = $int(descendantPid) & "\n"
        discard posix.write(qPipe[1], unsafeAddr msg[0], msg.len)
        discard close(qPipe[1])
        blockForeverOnOwnPipe()
        quit(0)

      discard close(goPipe[0])
      discard close(qPipe[1])
      # Isolate the worker's group BEFORE it forks its own descendant — the
      # "go" handshake below avoids the classic setpgid/fork ordering race
      # (a descendant forked before its parent's pgid changed would inherit
      # the OLD pgid instead).
      isolateOwnProcessGroup(workerPid)
      let goByte = "x"
      discard posix.write(goPipe[1], unsafeAddr goByte[0], 1)
      discard close(goPipe[1])
      let descendantPid = readPidFrom(qPipe[0])
      discard close(qPipe[0])

      killWorkerGroup(workerPid)

      var workerStatus, descendantStatus: cint = 0
      check waitpid(workerPid, workerStatus, 0) == workerPid
      check WIFSIGNALED(workerStatus)
      check WTERMSIG(workerStatus) == SIGKILL
      check waitpid(descendantPid, descendantStatus, 0) == descendantPid
      check WIFSIGNALED(descendantStatus)   # killed directly by the group signal, not PDEATHSIG
      check WTERMSIG(descendantStatus) == SIGKILL
