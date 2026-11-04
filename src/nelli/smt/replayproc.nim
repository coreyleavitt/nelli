## RFC-0005 S8ct. A witness replay runs the real SUT on solver-chosen inputs, on
## a path the model may have got wrong, so it may reach anything: `quit`, a raw C
## `exit`, `abort`, a nil dereference, unbounded recursion, heap exhaustion, wild
## writes. None of those can be contained in the process they happen in. So no
## replay runs in the host process: this module runs each one in a child, and
## what the child does ends with the child.
##
## Two ways to get a child:
##
## * `fork` (POSIX). The child is a copy of the calling thread and of the whole
##   address space, so the SUT sees exactly the state the host has, on a stack of
##   the same size, and needs nothing marshalled. The other threads of the host
##   do not exist in it: anything it waits on from one of them runs into the
##   bound, and a lock one of them held stays held, which also runs into the
##   bound. Neither reaches the host.
## * Re-executing the program (Windows, which has no `fork`). The child starts
##   the same binary and runs its module initialisers in the normal order. A
##   `{.global.}` initialiser the entry macro emits at each call site runs in the
##   module holding the call, before that module's first statement
##   (`replayChildEntry`): none of the program's own top-level code runs in the
##   child. The witness and the variables the SUT reaches are marshalled to it
##   (`replaywire.nim`). State that cannot be marshalled declines the replay.
##   `-d:nelliReplayReexec` selects this path on Linux, so it can be run there.
##
## A platform with neither runs no replay at all.

import std/strutils
when defined(windows) or defined(nelliReplayReexec):
  import std/os
import ../engine/markers

const
  replayForks* = defined(posix) and not defined(nelliReplayReexec)
  replayReexecs* = defined(windows) or
                   (defined(posix) and defined(nelliReplayReexec))
  replayMemoryLimit* = 2 shl 30
    ## What a replay may allocate past the address space it starts with. An
    ## allocation loop then fails in the child ("out of memory", a real exit)
    ## instead of taking the machine's memory from the host.

type
  ReplayEnding* = enum
    ## How one child ended.
    reFinished    ## the SUT returned, or raised into the replay's frame
    reExited      ## the process exited before that (`quit`, C `exit`, ...)
    reSignalled   ## a signal or an unhandled system exception ended it
    reTimedOut    ## it ran past the bound and was killed
    reRefused     ## no child ran: it could not be started, or the state the
                  ## SUT reaches could not be handed to it

  ReplayReport* = object
    ## What the SUT's run established, from inside the child.
    reached*: bool   ## the target was reached (`replayReached`)
    bound*: bool     ## the arguments were bound: `fn` itself was called

  ReplayChild* = object
    ## What the host learned.
    ending*: ReplayEnding
    reached*: bool   ## the target was reached, whatever happened afterwards
    bound*: bool
    code*: int       ## `reExited`: the exit code. `reSignalled`: the signal,
                     ## or the system's exception code
    why*: string     ## `reRefused`: the reason
    outOfMemory*: bool
      ## RFC-0005 0.9.1 (WA-7). The child ended because an allocation failed
      ## at the replay's memory limit (`replayMemoryLimit`), which on a fork
      ## is relative to what the host had mapped.
    runDependent*: bool
      ## RFC-0005 0.9.1 (WA-7). How the child ended depends on this run, not
      ## only on the program and the witness: it ran past its bound, hit the
      ## memory limit, or could not be started or handed its state for a
      ## reason of the moment (a failed `fork`, pipe or job object, a runtime
      ## hook the host had set). Another run may decide it, so a verdict
      ## it leaves undecided is not cached (`rdReplay`, carried on the
      ## result's `Soundness.runDependence`).

var replayExecCount = 0
  ## How many children the host has started: symex never runs `fn` itself, so
  ## this counts real executions. What a SUT does to the host's variables can no
  ## longer count them.

proc replayExecutions*(): int =
  ## RFC-0005 S8ct. How many replays this process has run.
  {.cast(gcsafe).}:
    replayExecCount

func describe*(c: ReplayChild): string =
  ## How the child ended, in words, for a `feReplay*` hint (`replayresult.nim`).
  ##
  ## Known limitation (RFC-0005 0.9.1, WA-13): on a forked child where libc
  ## has no `on_exit` (macOS, musl: `hasOnExit` is false), the exit hook is
  ## `atexit`, which is not told the status. The child reports an exit with
  ## no code, so `code` is 0 and the hint reads "exited the process with code
  ## 0" for ANY `quit(n)` or C `exit(n)`, whatever `n` was. The ending
  ## (`reExited`) and every verdict are right; only the code in the message
  ## is not. Linux with glibc, and the re-executed child (which reads the
  ## real status from `waitpid` or the process exit code), report the code.
  case c.ending
  of reFinished: "it ran to its end"
  of reExited:
    if c.outOfMemory:
      "it ran out of the replay's memory limit (an allocation failed; exit " &
        "code " & $c.code & ")"
    else: "it exited the process with code " & $c.code
  of reSignalled:
    when defined(windows):
      "it was ended by the system exception 0x" & toHex(c.code, 8)
    else:
      "it was ended by signal " & $c.code
  of reTimedOut: "it ran past its bound and was killed"
  of reRefused: c.why

func settled(c: ReplayChild): ReplayChild =
  ## The child as the host reports it: a run past the bound or into the memory
  ## limit is the run's, not only the program's.
  result = c
  if c.ending == reTimedOut or c.outOfMemory: result.runDependent = true

proc refused(why: string; runDependent = true): ReplayChild =
  ## No child ran. `runDependent`: for a reason of the moment (the default:
  ## a failed `fork`, pipe, job object or temporary file); `false` for one
  ## that holds on every run (`refusedStatically`, `refusedNotMarshallable`).
  settled(ReplayChild(ending: reRefused, why: why, runDependent: runDependent))

proc refusedStatically*(why: string): ReplayChild =
  ## RFC-0005 S8ct. No child: the entry macro proved at compile time that this
  ## SUT's state cannot be handed to one.
  refused(why, runDependent = false)

proc refusedNotMarshallable*(why: string): ReplayChild =
  ## RFC-0005 S8ct. A re-executed child (Windows) must be handed what the SUT
  ## reaches, and `why` names what cannot be. A forked child copies everything,
  ## so a Linux or macOS run replays the same SUT; the message says so.
  refused("replay not marshallable: " & why & " (on this platform replay " &
          "runs in a re-executed child, which must be handed what the SUT " &
          "reaches; a Linux or macOS run forks and replays it)",
          runDependent = false)

proc refusedHostHook*(why: string): ReplayChild =
  ## RFC-0005 0.9.1 (WA-7). As `refusedNotMarshallable`, for a runtime hook the
  ## host had set at the time (`hostRuntimeHook`): a run without it replays,
  ## so the decline depends on the run.
  refused("replay not marshallable: " & why & " (on this platform replay " &
          "runs in a re-executed child, which must be handed what the SUT " &
          "reaches; a Linux or macOS run forks and replays it)",
          runDependent = true)

proc hostRuntimeHook*(): string =
  ## RFC-0005 batch 11. A runtime hook of the stdlib's that the program set,
  ## named for a decline, or "". The hook is a proc value the host installed at
  ## run time, and it changes what the SUT does (a `raise` runs it, an
  ## allocation failure, an exception nothing catches). A re-executed child runs
  ## none of the host's top-level code, so it starts without it, and no wire can
  ## hand a proc value over: a replay there would run a different program.
  template check(h: untyped) =
    when declared(h):
      if h != nil: return "`" & astToStr(h) & "`, a runtime hook the host set"
  check globalRaiseHook
  check localRaiseHook
  check outOfMemHook
  check unhandledExceptionHook
  check onUnhandledException
  check errorMessageWriter
  ""

var hitLabel: string
var hitDepth: int
var hitOut: proc (b: char) {.nimcall, gcsafe.}

proc hitSink(name: string; depth: int) {.nimcall, gcsafe.} =
  {.cast(gcsafe).}:
    if depth == hitDepth and name == hitLabel and hitOut != nil:
      hitOut('H')

proc armReplayHit*(label: string) =
  ## RFC-0005 S8ct. Called by the replay body, inside the child, just after it
  ## opens its capture frame. A label is reported as it is hit, so a process
  ## that dies afterwards has still reached it. `label` empty: not a label
  ## target, and the report at the end says.
  if label.len > 0 and hitOut != nil:
    hitLabel = label
    hitDepth = symexCapture.enclosing.len
    symexHitSink = hitSink

proc flagsChar(r: ReplayReport): char =
  char(ord('0') + ord(r.reached) + 2 * ord(r.bound))

proc readFlags(c: char; into: var ReplayChild) =
  let f = ord(c) - ord('0')
  into.reached = into.reached or (f and 1) != 0
  into.bound = (f and 2) != 0

# ---- fork ---------------------------------------------------------------------

when replayForks:
  import std/posix

  proc c_fflush(f: pointer): cint {.importc: "fflush", header: "<stdio.h>".}
  proc c_signal(sig: cint; handler: pointer): pointer
    {.importc: "signal", header: "<signal.h>".}
  proc c_atexit(f: proc () {.noconv.}): cint
    {.importc: "atexit", header: "<stdlib.h>".}

  var rlimitCore {.importc: "RLIMIT_CORE", header: "<sys/resource.h>".}: cint
  var rlimitAs {.importc: "RLIMIT_AS", header: "<sys/resource.h>".}: cint

  const hasOnExit = defined(linux) and not defined(musl)
  when hasOnExit:
    proc c_on_exit(f: proc (status: cint; arg: pointer) {.noconv.};
                   arg: pointer): cint
      {.importc: "on_exit", header: "<stdlib.h>".}
  when defined(linux):
    proc c_prctl(option: cint; arg: culong): cint
      {.importc: "prctl", header: "<sys/prctl.h>".}
    const prSetPdeathsig = cint(1)

  var childFd = cint(-1)

  proc childWrite(bytes: openArray[char]) {.gcsafe.} =
    {.cast(gcsafe).}:
      var i = 0
      while i < bytes.len:
        let n = write(childFd, unsafeAddr bytes[i], bytes.len - i)
        if n <= 0:
          if n < 0 and errno == EINTR: continue
          return
        i += n

  proc childOut(b: char) {.nimcall, gcsafe.} =
    childWrite([b])

  var hostOomHook: proc () {.nimcall, tags: [], gcsafe, raises: [].}

  proc childOom() {.nimcall, tags: [], gcsafe, raises: [].} =
    ## RFC-0005 0.9.1 (WA-7): an allocation failed. Written before Nim's own
    ## `out of memory` exit, so the host can tell the limit from a `quit(1)`.
    {.cast(gcsafe).}:
      {.cast(tags: []).}:
        childWrite(['M'])
        if hostOomHook != nil: hostOomHook()

  when hasOnExit:
    proc childOnExit(status: cint; arg: pointer) {.noconv.} =
      # Registered last, so runs first: what the host registered to run at its
      # own exit (a temporary directory's removal, a report) must not run here.
      let s = $status
      childWrite(['X'])
      childWrite(s)
      childWrite(['\n'])
      exitnow(status)
  else:
    proc childAtExit() {.noconv.} =
      # `atexit` is not handed the status, so the report carries no code and
      # the host reads 0 (see `describe`'s known limitation). The child's own
      # status is then 120, not the SUT's.
      childWrite(['X'])
      childWrite(['\n'])
      exitnow(120)

  proc enterChild() =
    ## Everything that keeps the child's ending from touching the host's world.
    when defined(linux):
      # Dies with the host, and starts its own group so that a kill at the
      # bound reaches what the SUT started.
      discard c_prctl(prSetPdeathsig, culong(SIGKILL))
      discard setpgid(0, 0)
    var noCore = RLimit(rlim_cur: 0, rlim_max: 0)
    discard setrlimit(rlimitCore, noCore)
    when defined(linux):
      # The host's own mappings count against the limit, so it is relative.
      var pages = 0
      try:
        pages = parseInt(readFile("/proc/self/statm").splitWhitespace()[0])
      except CatchableError:
        pages = 0
      if pages > 0:
        let total = pages * int(sysconf(SC_PAGESIZE)) + replayMemoryLimit
        var r: RLimit
        if getrlimit(rlimitAs, r) == 0:
          r.rlim_cur = total
          discard setrlimit(rlimitAs, r)
    # Nim's handlers turn a fault into `exit(1)` after a trace; the report must
    # say what happened. A SUT's own handler installed later still wins.
    for s in [SIGSEGV, SIGBUS, SIGILL, SIGFPE, SIGABRT]:
      discard c_signal(s, nil)
    let null = open("/dev/null", O_RDWR)
    if null >= 0:
      discard dup2(null, 0)
      discard dup2(null, 1)
      discard dup2(null, 2)
      if null > 2: discard close(null)
    when hasOnExit:
      discard c_on_exit(childOnExit, nil)
    else:
      discard c_atexit(childAtExit)
    hostOomHook = outOfMemHook   # the SUT runs under the host's, after ours
    outOfMemHook = childOom

  proc runChildBody(body: proc (): ReplayReport {.closure, gcsafe.}) =
    enterChild()
    hitOut = childOut
    var rep: ReplayReport
    try:
      {.cast(gcsafe).}:
        rep = body()
    except Exception:
      exitnow(121)
    childWrite(['E', flagsChar(rep)])
    exitnow(0)

  proc decodeChild(buf: string; c: var ReplayChild): bool =
    ## The stream a child has written so far. True when it says the child is
    ## finished.
    var i = 0
    while i < buf.len:
      case buf[i]
      of 'H':
        c.reached = true
      of 'M':
        c.outOfMemory = true
      of 'E':
        if i + 1 < buf.len:
          readFlags(buf[i + 1], c)
          c.ending = reFinished
          return true
      of 'X':
        let e = buf.find('\n', i)
        if e > 0:
          c.ending = reExited
          c.code = (if e > i + 1: parseInt(buf[i + 1 .. e - 1]) else: 0)
          return true
      else:
        discard
      inc i
    false

  proc nowMs(): int64 =
    var t: Timespec
    discard clock_gettime(CLOCK_MONOTONIC, t)
    int64(t.tv_sec) * 1000 + int64(t.tv_nsec) div 1_000_000

  proc killChild(pid: Pid) =
    when defined(linux):
      discard kill(-pid, SIGKILL)   # its group: what the SUT started with it
    discard kill(pid, SIGKILL)

  proc runReplayForked*(body: proc (): ReplayReport {.closure, gcsafe.};
                        timeoutMs: int): ReplayChild =
    ## RFC-0005 S8ct. `body` in a forked child, killed at `timeoutMs` (`<= 0`: no
    ## bound).
    var fds: array[2, cint]
    if pipe(fds) != 0:
      return refused("a pipe could not be created for the replay's child")
    discard fcntl(fds[0], F_SETFD, FD_CLOEXEC)
    discard fcntl(fds[1], F_SETFD, FD_CLOEXEC)
    # Whatever the host has buffered must not be written twice.
    discard c_fflush(nil)
    let pid = fork()
    if pid < 0:
      discard close(fds[0])
      discard close(fds[1])
      return refused("fork failed (errno " & $errno & ")")
    if pid == 0:
      childFd = fds[1]
      discard close(fds[0])
      runChildBody(body)
      exitnow(122)   # not reached
    {.cast(gcsafe).}:
      inc replayExecCount
    discard close(fds[1])
    when defined(linux):
      discard setpgid(pid, pid)   # either side may run first
    let deadline = if timeoutMs > 0: nowMs() + timeoutMs else: 0'i64
    var buf = ""
    var eof = false
    var reaped = false
    var status: cint = 0
    var c = ReplayChild(ending: reSignalled)
    var finished = false
    var killed = false
    while not (finished or reaped):
      var wait = cint(50)
      if deadline != 0:
        let left = deadline - nowMs()
        if left <= 0:
          killed = true
          break
        wait = cint(min(left, 50))
      if not eof:
        var p = TPollfd(fd: fds[0], events: POLLIN)
        if poll(addr p, Tnfds(1), wait) > 0:
          var chunk: array[256, char]
          let n = read(fds[0], addr chunk[0], chunk.len)
          if n > 0:
            for i in 0 ..< n: buf.add chunk[i]
            finished = decodeChild(buf, c)
          elif n == 0:
            eof = true
          elif errno != EINTR:
            eof = true
      else:
        discard usleep(cuint(wait) * 1000)
      if not finished and not reaped:
        # A child's own children may hold the pipe open past its end, and the
        # pipe may be closed while it still runs.
        let w = waitpid(pid, status, WNOHANG)
        if w == pid: reaped = true
        elif w < 0 and errno != EINTR:
          reaped = true   # SIGCHLD ignored: no status is coming
          status = 0
          eof = true
    if killed or finished:
      # A finished child calls `_exit` straight after its report; one that
      # raced past the bound has done nothing the verdict reads.
      killChild(pid)
    if not reaped:
      while waitpid(pid, status, 0) < 0 and errno == EINTR:
        discard
    # What a child wrote before it ended.
    while not finished:
      var chunk: array[256, char]
      var p = TPollfd(fd: fds[0], events: POLLIN)
      if poll(addr p, Tnfds(1), 0) <= 0: break
      let n = read(fds[0], addr chunk[0], chunk.len)
      if n <= 0: break
      for i in 0 ..< n: buf.add chunk[i]
      finished = decodeChild(buf, c)
    discard close(fds[0])
    if not finished:
      discard decodeChild(buf, c)
    if finished:
      discard
    elif killed:
      c.ending = reTimedOut
    elif WIFSIGNALED(status):
      c.ending = reSignalled
      c.code = int(WTERMSIG(status))
    else:
      c.ending = reExited
      c.code = int(WEXITSTATUS(status))
    settled(c)

# ---- re-execution -------------------------------------------------------------

const replayChildEnv = "NELLI_REPLAY_CHILD"

type ChildSpec = object
  site, input, output: string

when replayReexecs:
  proc parseSpec(s: string): ChildSpec =
    let parts = s.split('|')
    if parts.len == 3:
      result = ChildSpec(site: parts[0], input: parts[1], output: parts[2])

  let childSpec = parseSpec(getEnv(replayChildEnv))
    ## Non-empty in a child, from its first module initialiser on.

  var tempCounter = 0

  when defined(windows):
    import std/winlean
    import std/widestrs

    type
      JobBasicLimits {.pure.} = object
        perProcessUserTime, perJobUserTime: int64
        limitFlags: uint32
        minWs, maxWs: uint
        activeProcessLimit: uint32
        affinity: uint
        priorityClass, schedulingClass: uint32
      IoCounters {.pure.} = object
        a, b, c, d, e, f: uint64
      JobExtendedLimits {.pure.} = object
        basic: JobBasicLimits
        io: IoCounters
        processMemoryLimit, jobMemoryLimit: uint
        peakProcess, peakJob: uint

    const
      jobObjectExtendedLimitInformation = 9'i32
      jobObjectLimitProcessMemory = 0x100'u32
      jobObjectLimitKillOnJobClose = 0x2000'u32
      jobObjectLimitDieOnUnhandledException = 0x400'u32
      createSuspendedFlag = 0x4'i32
      createNoWindowFlag = 0x08000000'i32
      createUnicodeEnvironmentFlag = 0x00000400'i32
      startfUseStdHandlesFlag = 0x100'i32
      semFailCriticalErrors = 0x1'u32
      semNoGpFaultErrorBox = 0x2'u32
      semNoOpenFileErrorBox = 0x8000'u32
      waitObject0 = 0'i32
      waitTimeoutResult = 258'i32
      genericReadWrite = 0xC0000000'u32
      fileShareRW = 3'u32
      openExistingFlag = 3'u32
      handleFlagInherit = 1'u32

    proc createJobObjectW(attrs: pointer; name: pointer): Handle
      {.importc: "CreateJobObjectW", stdcall, dynlib: "kernel32".}
    proc setInformationJobObject(job: Handle; cls: int32; info: pointer;
                                 size: uint32): int32
      {.importc: "SetInformationJobObject", stdcall, dynlib: "kernel32".}
    proc assignProcessToJobObject(job, process: Handle): int32
      {.importc: "AssignProcessToJobObject", stdcall, dynlib: "kernel32".}
    proc terminateJobObject(job: Handle; code: uint32): int32
      {.importc: "TerminateJobObject", stdcall, dynlib: "kernel32".}
    proc setErrorModeR(mode: uint32): uint32
      {.importc: "SetErrorMode", stdcall, dynlib: "kernel32".}
    proc createFileWR(name: WideCString; access, share: uint32; attrs: pointer;
                      disposition, flags: uint32; tmpl: Handle): Handle
      {.importc: "CreateFileW", stdcall, dynlib: "kernel32".}
    proc setHandleInformationR(h: Handle; mask, flags: uint32): int32
      {.importc: "SetHandleInformation", stdcall, dynlib: "kernel32".}
    proc getEnvironmentStringsWR(): pointer
      {.importc: "GetEnvironmentStringsW", stdcall, dynlib: "kernel32".}
    proc freeEnvironmentStringsWR(p: pointer): int32
      {.importc: "FreeEnvironmentStringsW", stdcall, dynlib: "kernel32".}
    proc getCurrentThreadStackLimits(lo, hi: ptr uint)
      {.importc: "GetCurrentThreadStackLimits", stdcall, dynlib: "kernel32".}
    proc convertThreadToFiberR(param: pointer): pointer
      {.importc: "ConvertThreadToFiber", stdcall, dynlib: "kernel32".}
    proc convertFiberToThreadR(): int32
      {.importc: "ConvertFiberToThread", stdcall, dynlib: "kernel32".}
    proc createFiberExR(stackCommit, stackReserve: csize_t, flags: uint32,
                        startAddr, param: pointer): pointer
      {.importc: "CreateFiberEx", stdcall, dynlib: "kernel32".}
    proc deleteFiberR(f: pointer)
      {.importc: "DeleteFiber", stdcall, dynlib: "kernel32".}
    proc switchToFiberR(f: pointer)
      {.importc: "SwitchToFiber", stdcall, dynlib: "kernel32".}
    proc exitProcessR(code: uint32) {.noreturn, importc: "ExitProcess", stdcall,
                                      dynlib: "kernel32".}
    proc terminateProcessSelf(code: uint32) =
      exitProcessR(code)

    proc environmentWith(name, value: string): seq[uint16] =
      ## The block `CreateProcessW` takes: the current environment and one more
      ## variable. An exact block rather than `SetEnvironmentVariable`, which
      ## another thread starting a process could inherit.
      let base = getEnvironmentStringsWR()
      if base != nil:
        var p = cast[ptr UncheckedArray[uint16]](base)
        var i = 0
        while not (p[i] == 0 and p[i + 1] == 0):
          result.add p[i]
          inc i
        # The last variable's terminator. A second one would end the block here,
        # and the child would not see the variable added below.
        if i > 0: result.add 0'u16
        discard freeEnvironmentStringsWR(base)
      let added = newWideCString(name & "=" & value)
      var j = 0
      while added[j].uint16 != 0:
        result.add added[j].uint16
        inc j
      result.add 0'u16
      result.add 0'u16

    proc spawnAndWait(spec: string; timeoutMs: int; c: var ReplayChild): bool =
      ## False: no child ran (`c.why`).
      let job = createJobObjectW(nil, nil)
      if job == Handle(0):
        c.why = "a job object could not be created for the replay's child"
        return false
      var lim: JobExtendedLimits
      lim.basic.limitFlags = jobObjectLimitProcessMemory or
                             jobObjectLimitKillOnJobClose or
                             jobObjectLimitDieOnUnhandledException
      lim.processMemoryLimit = uint(replayMemoryLimit)
      if setInformationJobObject(job, jobObjectExtendedLimitInformation,
                                 addr lim, uint32(sizeof(lim))) == 0:
        discard closeHandle(job)
        c.why = "the replay's job object could not be limited"
        return false
      let null = createFileWR(newWideCString("NUL"), genericReadWrite,
                              fileShareRW, nil, openExistingFlag, 0, Handle(0))
      if null == Handle(-1):
        discard closeHandle(job)
        c.why = "NUL could not be opened for the replay's child"
        return false
      discard setHandleInformationR(null, handleFlagInherit, handleFlagInherit)
      var si: STARTUPINFO
      si.cb = int32(sizeof(si))
      si.dwFlags = startfUseStdHandlesFlag
      si.hStdInput = null
      si.hStdOutput = null
      si.hStdError = null
      var pi: PROCESS_INFORMATION
      var env = environmentWith(replayChildEnv, spec)
      let exe = newWideCString(getAppFilename())
      let ok = createProcessW(exe, nil, nil, nil, 1,
                              createSuspendedFlag or createNoWindowFlag or
                                createUnicodeEnvironmentFlag,
                              cast[WideCString](addr env[0]), nil, si, pi)
      discard closeHandle(null)
      if ok == 0:
        discard closeHandle(job)
        c.why = "the program could not be re-executed (error " &
                $getLastError() & ")"
        return false
      if assignProcessToJobObject(job, pi.hProcess) == 0:
        discard terminateProcess(pi.hProcess, 1)
        discard closeHandle(pi.hThread)
        discard closeHandle(pi.hProcess)
        discard closeHandle(job)
        c.why = "the replay's child could not join its job object"
        return false
      discard resumeThread(pi.hThread)
      discard closeHandle(pi.hThread)
      {.cast(gcsafe).}:
        inc replayExecCount
      let wait = if timeoutMs > 0: int32(timeoutMs) else: -1'i32
      let w = waitForSingleObject(pi.hProcess, wait)
      if w == waitObject0:
        var code: int32
        discard getExitCodeProcess(pi.hProcess, code)
        let ucode = cast[uint32](code)
        if ucode >= 0xC0000000'u32:
          c.ending = reSignalled
          c.code = int(ucode)
        else:
          c.ending = reExited
          c.code = int(ucode)
      else:
        c.ending = reTimedOut
      discard terminateJobObject(job, 1)
      discard closeHandle(pi.hProcess)
      discard closeHandle(job)   # kills whatever the SUT started
      true

    proc callerStackSize*(): int =
      var lo, hi: uint
      getCurrentThreadStackLimits(addr lo, addr hi)
      int(hi - lo)

    type FiberRun = object
      body: proc () {.closure.}
      mainFiber: pointer

    proc fiberMain(param: pointer) {.stdcall, stackTrace: off, lineTrace: off.} =
      # Never returns: it switches away, and its stack is then freed. With a stack
      # trace frame of its own, Nim's frame chain would be left pointing into
      # that freed stack, and the next call read it (0xC0000005 on Windows).
      let f = cast[ptr FiberRun](param)
      f.body()
      switchToFiberR(f.mainFiber)

    proc runOnStack(stack: int; body: proc () {.closure.}) =
      ## `body` on a fiber whose stack reserve is the calling thread's size in
      ## the host. `body` catches what it raises.
      if stack <= 0:
        body()
        return
      let mainFiber = convertThreadToFiberR(nil)
      if mainFiber == nil:
        body()
        return
      var f = FiberRun(body: body, mainFiber: mainFiber)
      let fib = createFiberExR(csize_t(64 * 1024), csize_t(stack), 1,
                               cast[pointer](fiberMain), addr f)
      if fib == nil:
        discard convertFiberToThreadR()
        body()
        return
      switchToFiberR(fib)
      deleteFiberR(fib)
      discard convertFiberToThreadR()

    proc quietChild() =
      discard setErrorModeR(semFailCriticalErrors or semNoGpFaultErrorBox or
                            semNoOpenFileErrorBox)

    proc endChild(code: int) =
      terminateProcessSelf(uint32(code))

  else:
    # -d:nelliReplayReexec on POSIX: the same protocol with the same files, to
    # run this path where it can be debugged.
    import std/posix

    proc c_exit_now(code: cint) {.importc: "_exit", header: "<unistd.h>".}
    # At module scope: an `importc` var declared in a proc is emitted as a C
    # local of that name, which shadows the enum constant with an
    # uninitialised one, and `setrlimit` then fails without a word.
    var rlimitAsReexec {.importc: "RLIMIT_AS", header: "<sys/resource.h>".}: cint

    proc spawnAndWait(spec: string; timeoutMs: int; c: var ReplayChild): bool =
      let exe = getAppFilename()
      let pid = fork()
      if pid < 0:
        c.why = "fork failed"
        return false
      if pid == 0:
        putEnv(replayChildEnv, spec)
        let null = open("/dev/null", O_RDWR)
        if null >= 0:
          discard dup2(null, 0)
          discard dup2(null, 1)
          discard dup2(null, 2)
        var args = allocCStringArray([exe])
        discard execv(exe.cstring, args)
        c_exit_now(127)
      {.cast(gcsafe).}:
        inc replayExecCount
      var status: cint
      var waited = 0
      var done = false
      while true:
        let w = waitpid(pid, status, WNOHANG)
        if w == pid:
          done = true
          break
        if timeoutMs > 0 and waited >= timeoutMs: break
        sleep(2)
        waited += 2
      if not done:
        discard kill(pid, SIGKILL)
        discard waitpid(pid, status, 0)
        c.ending = reTimedOut
      elif WIFSIGNALED(status):
        c.ending = reSignalled
        c.code = int(WTERMSIG(status))
      else:
        c.ending = reExited
        c.code = int(WEXITSTATUS(status))
      true

    proc callerStackSize*(): int = 0

    proc runOnStack(stack: int; body: proc () {.closure.}) = body()

    proc quietChild() =
      # As the fork path: the verdict reads the signal, not Nim's trace.
      for s in [SIGSEGV, SIGBUS, SIGILL, SIGFPE, SIGABRT]:
        var sa: Sigaction
        sa.sa_handler = SIG_DFL
        discard sigaction(s, sa, nil)
      var r: RLimit
      if getrlimit(rlimitAsReexec, r) == 0:
        r.rlim_cur = replayMemoryLimit
        discard setrlimit(rlimitAsReexec, r)

    proc endChild(code: int) =
      c_exit_now(cint(code))

  var childOutput: File
  var hostOomHookR: proc () {.nimcall, tags: [], gcsafe, raises: [].}

  proc childOomR() {.nimcall, tags: [], gcsafe, raises: [].} =
    ## RFC-0005 0.9.1 (WA-7): as the fork path's `childOom`.
    {.cast(gcsafe).}:
      {.cast(tags: []).}:
        try:
          childOutput.write('M')
          childOutput.flushFile()
        except Exception:
          discard
        if hostOomHookR != nil: hostOomHookR()

  proc childOut(b: char) {.nimcall, gcsafe.} =
    {.cast(gcsafe).}:
      childOutput.write(b)
      childOutput.flushFile()

  proc inReplayChild*(): bool =
    ## RFC-0005 S8ct. This process is a replay's child. It starts no child of
    ## its own: should the call site not be found on the way in (a library
    ## loaded by another program), it must not go on re-executing.
    childSpec.site.len > 0

  proc runReplayReexec*(site, payload: string; timeoutMs: int): ReplayChild =
    ## RFC-0005 S8ct. The host's half: `payload` to a re-executed copy of this
    ## program, which the initialiser at call site `site` picks up
    ## (`replayChildEntry`), and what it reported.
    if inReplayChild():
      return refused("a replay's child does not start another")
    {.cast(gcsafe).}:
      inc tempCounter
      let tag = $getCurrentProcessId() & "-" & $tempCounter
    let base = getTempDir() / ("nelli-replay-" & tag)
    let input = base & ".in"
    let output = base & ".out"
    defer:
      try: removeFile(input)
      except CatchableError: discard
      try: removeFile(output)
      except CatchableError: discard
    try:
      writeFile(input, payload)
      writeFile(output, "")
    except CatchableError as e:
      return refused("the replay's witness could not be written: " & e.msg)
    var c = ReplayChild(ending: reSignalled)
    flushFile(stdout)
    flushFile(stderr)
    if not spawnAndWait(site & "|" & input & "|" & output, timeoutMs, c):
      return refused(c.why)
    var seen = ""
    try:
      seen = readFile(output)
    except CatchableError:
      seen = ""
    var i = 0
    while i < seen.len:
      case seen[i]
      of 'H':
        c.reached = true
      of 'M':
        c.outOfMemory = c.ending != reTimedOut
      of 'E':
        if i + 1 < seen.len and c.ending != reTimedOut:
          readFlags(seen[i + 1], c)
          c.ending = reFinished
        inc i
      of 'W':
        c.ending = reRefused
        c.why = "the child could not read the witness"
        c.runDependent = true
      else:
        discard
      inc i
    settled(c)

  proc replayChildEntry*(site: string;
                         run: proc (payload: string): ReplayReport {.nimcall.}):
                           bool =
    ## RFC-0005 S8ct. The child's half, from a `{.global.}` initialiser at each
    ## call site: returns at once except in the child of this very site, which
    ## runs the SUT and ends.
    if childSpec.site != site: return false
    quietChild()
    hostOomHookR = outOfMemHook
    outOfMemHook = childOomR
    var rep: ReplayReport
    var failed = false
    try:
      childOutput = open(childSpec.output, fmWrite)
      hitOut = childOut
      let payload = readFile(childSpec.input)
      let stack = (if payload.len >= 8: cast[ptr int64](unsafeAddr payload[0])[]
                   else: 0'i64)
      runOnStack(int(stack), proc () {.closure.} =
        try:
          rep = run(payload)
        except Exception:
          failed = true)
    except Exception:
      failed = true
    try:
      if failed: childOut('W')
      else:
        childOutput.write('E')
        childOut(flagsChar(rep))
      childOutput.close()
    except Exception:
      endChild(123)
    endChild(0)
    true
