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

import std/[strutils, monotimes, times]
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
    ## How one child ended. Review R3 (E1): the zero value is `reRefused`, a
    ## child that did not run, so a `ReplayChild` nothing filled in reports
    ## no run, never one that finished.
    reRefused     ## no child ran: it could not be started, or the state the
                  ## SUT reaches could not be handed to it
    reFinished    ## the SUT returned, or raised into the replay's frame
    reExited      ## the process exited before that (`quit`, C `exit`, ...)
    reSignalled   ## a signal or an unhandled system exception ended it
    reTimedOut    ## it ran past the bound and was killed
    reLost        ## review R2 (LV1). A child ran and ended without a report
                  ## of its end, and its exit status was gone before the host
                  ## could read it (`statusLost`). It did not finish, as far
                  ## as anyone knows, so it counts as having ended its
                  ## process: never as "did not run"

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
    why*: string     ## `reRefused`, `reLost`: the reason. `reTimedOut`: why
                     ## it was stopped, when that was not the bound
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
  of reTimedOut:
    if c.why.len > 0: c.why else: "it ran past its bound and was killed"
  of reRefused, reLost: c.why

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
var hitSent = false
  ## RFC-0005 0.9.1 (review R1-18). The child has reported its hit. A label is
  ## reported once: a SUT that reaches it a million times must not write a
  ## million bytes for the host to read.

proc hitSink(name: string; depth: int) {.nimcall, gcsafe.} =
  {.cast(gcsafe).}:
    if not hitSent and depth == hitDepth and name == hitLabel and
       hitOut != nil:
      hitSent = true
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

# ---- the child's report -------------------------------------------------------
#
# RFC-0005 0.9.1 (review R1-18, R1-30). What a child writes, the host decodes as
# it arrives, a byte at a time: no byte is read twice, none is kept, and nothing
# in it can raise. A report is a handful of bytes, each written once:
#
#   H        the target label was hit (`hitSink`)
#   M        an allocation failed at the memory limit (`childOom`)
#   E<f>     the SUT ran to its end; `f` is '0'..'3' (`flagsChar`)
#   X<n>\n   the process exited with status `n` (fork, `childOnExit`)
#   W        the witness could not be read (re-exec)
#
# A child that writes more than `replayReportCap` bytes, or a byte the report
# does not have, is not writing a report: what it wrote is not trusted, and it
# is stopped.

const replayReportCap* = 4096
  ## The most a child's report may take before the host stops the child.

type
  ReportState = enum
    rsNext, rsFlags, rsCode, rsDone
  ReportReader = object
    state: ReportState
    total: int
    reached, outOfMemory: bool
    finished: bool       ## E<f>
    flags: char
    exited: bool         ## X<n>\n
    code, digits: int
    negative: bool
    unreadable: bool     ## W
    corrupt: bool        ## past the cap, or not a report

proc done(r: ReportReader): bool = r.state == rsDone

proc feed(r: var ReportReader; bytes: openArray[char]) =
  for ch in bytes:
    if r.corrupt: return
    inc r.total
    if r.total > replayReportCap:
      r.corrupt = true
      return
    case r.state
    of rsNext:
      case ch
      of 'H': r.reached = true
      of 'M': r.outOfMemory = true
      of 'E': r.state = rsFlags
      of 'X': r.state = rsCode
      of 'W':
        r.unreadable = true
        r.state = rsDone
      else: r.corrupt = true
    of rsFlags:
      if ch in {'0' .. '3'}:
        r.flags = ch
        r.finished = true
        r.state = rsDone
      else:
        r.corrupt = true
    of rsCode:
      if ch == '\n':
        if r.negative and r.digits == 0: r.corrupt = true
        else:
          if r.negative: r.code = -r.code
          r.exited = true
          r.state = rsDone
      elif ch == '-' and r.digits == 0 and not r.negative:
        r.negative = true
      elif ch in {'0' .. '9'} and r.digits < 10:
        r.code = r.code * 10 + (ord(ch) - ord('0'))
        inc r.digits
      else:
        r.corrupt = true
    of rsDone:
      # What follows an ending is not read: a copy of the child the SUT forked
      # may finish too.
      discard

proc stopped(why: string): ReplayChild =
  ## A child whose report was not a report (`ReportReader.corrupt`): killed,
  ## and nothing it wrote is read. Undecided, and not cached.
  settled(ReplayChild(ending: reTimedOut,
    why: "it wrote past what a replay's report holds (" &
         $replayReportCap & " bytes) or what one says, and was killed" &
         (if why.len > 0: " (" & why & ")" else: "")))

proc statusLost(c: ReplayChild): ReplayChild =
  ## RFC-0005 0.9.1 (review R1-19). The child ended without a report, and its
  ## exit status was gone before the host could read it: the host ignores
  ## `SIGCHLD`, so the system reaped it, or another thread's `wait` did. How
  ## it ended is not known, so it is not reported as anything it may not
  ## have been. Review R2 (LV1): it is `reLost`, not `reRefused`. It ran, so
  ## a hit it reported stands (`reached` is kept), and it did not finish, so
  ## its witness is never run in the host.
  result = c
  result.ending = reLost
  result.why = "the replay's child ended, but its exit status was lost " &
    "before the host could read it (SIGCHLD is ignored, or another wait " &
    "reaped it), so how it ended is not known"
  result.runDependent = true

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

  var oomSent = false

  proc childOom() {.nimcall, tags: [], gcsafe, raises: [].} =
    ## RFC-0005 0.9.1 (WA-7): an allocation failed. Written before Nim's own
    ## `out of memory` exit, so the host can tell the limit from a `quit(1)`.
    ## Once (R1-18).
    {.cast(gcsafe).}:
      {.cast(tags: []).}:
        if not oomSent:
          oomSent = true
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

  proc killChild(pid: Pid) =
    ## Only for a child not yet waited for: until then its pid, and the group
    ## it leads, are still this process's and cannot name another.
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
      let err = errno
      discard close(fds[0])
      discard close(fds[1])
      return refused("fork failed (errno " & $err & ")")
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
    let start = getMonoTime()
    var rd: ReportReader
    var eof = false
    var reaped = false       # waited for: its pid is no longer the host's
    var haveStatus = false   # and `status` is what it ended with
    var status: cint = 0
    var killed = false
    template reap(flags: cint) =
      let w = waitpid(pid, status, flags)
      if w == pid:
        reaped = true
        haveStatus = true
      elif w < 0 and errno != EINTR:
        # ECHILD: the host ignores SIGCHLD, or another wait took it. Gone,
        # and its status with it; its pid may already name another process.
        reaped = true
    template readSome(wait: cint): bool =
      ## Reads what is there within `wait` ms; false when nothing was.
      var got = false
      var p = TPollfd(fd: fds[0], events: POLLIN)
      if poll(addr p, Tnfds(1), wait) > 0:
        var chunk: array[512, char]
        let n = read(fds[0], addr chunk[0], chunk.len)
        if n > 0:
          rd.feed(chunk.toOpenArray(0, n - 1))
          got = true
        elif n == 0 or errno != EINTR:
          eof = true
      got
    while not (rd.done or rd.corrupt or reaped):
      var wait = cint(50)
      if timeoutMs > 0:
        let left = timeoutMs - (getMonoTime() - start).inMilliseconds
        if left <= 0:
          killed = true
          break
        wait = cint(min(left, 50))
      if not eof:
        discard readSome(wait)
      else:
        discard usleep(cuint(wait) * 1000)
      if not (rd.done or rd.corrupt):
        # A child's own children may hold the pipe open past its end, and the
        # pipe may be closed while it still runs.
        reap(WNOHANG)
    if not reaped:
      # Timed out, flooding, or finished and about to `_exit`: either way
      # nothing more is read from it. Not yet waited for, so its pid is ours.
      killChild(pid)
      while not reaped: reap(0)
    # What a child wrote before it ended, up to the cap: a SUT's children
    # outside its group may still be writing.
    while not (rd.done or rd.corrupt or eof):
      if not readSome(0): break
    discard close(fds[0])
    if rd.corrupt:
      return stopped("")
    var c = ReplayChild(reached: rd.reached, outOfMemory: rd.outOfMemory)
    if rd.finished:
      readFlags(rd.flags, c)
      c.ending = reFinished
    elif rd.exited:
      c.ending = reExited
      c.code = rd.code
    elif killed:
      c.ending = reTimedOut
    elif haveStatus and WIFSIGNALED(status):
      c.ending = reSignalled
      c.code = int(WTERMSIG(status))
    elif haveStatus and WIFEXITED(status):
      c.ending = reExited
      c.code = int(WEXITSTATUS(status))
    else:
      c = statusLost(c)
    settled(c)

# ---- re-execution -------------------------------------------------------------
#
# RFC-0005 0.9.1 (review R1-20, R1-23). The host hands a re-executed child two
# files in a directory of its own, created for this one child and readable by
# no other user (`mkdtemp`, or a random name `CreateDirectoryW` would refuse to
# reuse), each created exclusively: `in` (the witness) and `out` (the report).
# The child is told where by `NELLI_REPLAY_CHILD`, which also carries a nonce
# drawn for this spawn. `in` starts with the same nonce, so a marker the program
# merely inherited (one its host never set for it, or one left from a replay
# long gone) names no file that matches it, and is ignored. The host reads
# `out` through the handle it created it with, never by its name again.

const replayChildEnv = "NELLI_REPLAY_CHILD"

when replayReexecs:
  import std/sysrand

  const
    replayMagic = "NELLIRP1"
    nonceLen = 32           # hex digits
    replayStackCap = 1 shl 32
      ## The most stack a child's fiber is given: what a host thread may
      ## have, and no more, whatever the witness file says.

  type ChildRole = object
    site, payload, output: string

  var childRoleRead = false
  var childRoleVal: ChildRole

  proc toHexString(b: openArray[byte]): string =
    const digits = "0123456789abcdef"
    for x in b:
      result.add digits[int(x shr 4)]
      result.add digits[int(x and 15)]

  proc putInt64(s: var string; v: int64) =
    var x = v
    let at = s.len
    s.setLen(at + 8)
    copyMem(addr s[at], addr x, 8)

  proc getInt64(s: string; at: int): int64 =
    copyMem(addr result, unsafeAddr s[at], 8)

  proc witnessFile(nonce, site, payload: string): string =
    result = replayMagic & nonce
    result.putInt64(int64(site.len))
    result.add site
    result.add payload

  proc readChildRole(): ChildRole =
    ## This process's part as a replay's child: none, unless its host set the
    ## marker for it, which `in` proves.
    let marker = getEnv(replayChildEnv)
    if marker.len < nonceLen + 2 or marker[nonceLen] != '|': return
    let nonce = marker[0 ..< nonceLen]
    for ch in nonce:
      if ch notin {'0' .. '9', 'a' .. 'f'}: return
    let dir = marker[nonceLen + 1 .. ^1]
    var data: string
    try:
      data = readFile(dir / "in")
    except CatchableError:
      return
    let head = replayMagic.len + nonceLen + 8
    if data.len < head or data[0 ..< replayMagic.len] != replayMagic or
       data[replayMagic.len ..< replayMagic.len + nonceLen] != nonce:
      return
    let siteLen = getInt64(data, head - 8)
    if siteLen <= 0 or siteLen > int64(data.len - head): return
    result = ChildRole(site: data[head ..< head + int(siteLen)],
                       payload: data[head + int(siteLen) .. ^1],
                       output: dir / "out")
    # One child: a process the SUT starts must not take itself for it.
    delEnv(replayChildEnv)
    try: removeFile(dir / "in")
    except CatchableError: discard

  proc childRole(): ChildRole =
    {.cast(gcsafe).}:
      if not childRoleRead:
        childRoleRead = true
        childRoleVal = readChildRole()
      childRoleVal

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
      StartupInfoEx {.pure.} = object
        ## `STARTUPINFOEXW`.
        startupInfo: STARTUPINFO
        attributeList: pointer

    const
      jobObjectExtendedLimitInformation = 9'i32
      jobObjectLimitProcessMemory = 0x100'u32
      jobObjectLimitKillOnJobClose = 0x2000'u32
      jobObjectLimitDieOnUnhandledException = 0x400'u32
      createSuspendedFlag = 0x4'i32
      createNoWindowFlag = 0x08000000'i32
      createUnicodeEnvironmentFlag = 0x00000400'i32
      extendedStartupInfoPresent = 0x00080000'i32
      procThreadAttributeHandleList = 0x00020002'u
      startfUseStdHandlesFlag = 0x100'i32
      semFailCriticalErrors = 0x1'u32
      semNoGpFaultErrorBox = 0x2'u32
      semNoOpenFileErrorBox = 0x8000'u32
      waitObject0 = 0'i32
      waitTimeoutResult = 258'i32
      genericRead = 0x80000000'u32
      genericWrite = 0x40000000'u32
      genericReadWrite = 0xC0000000'u32
      fileShareRW = 3'u32
      fileShareAll = 7'u32
      createNewFlag = 1'u32
      openExistingFlag = 3'u32
      fileAttributeTemporary = 0x100'u32

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
    proc createDirectoryWR(name: WideCString; attrs: pointer): int32
      {.importc: "CreateDirectoryW", stdcall, dynlib: "kernel32".}
    proc writeFileR(h: Handle; buf: pointer; n: uint32; written: ptr uint32;
                    overlapped: pointer): int32
      {.importc: "WriteFile", stdcall, dynlib: "kernel32".}
    proc readFileR(h: Handle; buf: pointer; n: uint32; got: ptr uint32;
                   overlapped: pointer): int32
      {.importc: "ReadFile", stdcall, dynlib: "kernel32".}
    proc getFileSizeExR(h: Handle; size: ptr int64): int32
      {.importc: "GetFileSizeEx", stdcall, dynlib: "kernel32".}
    proc initializeProcThreadAttributeListR(list: pointer; count: uint32;
                                            flags: uint32;
                                            size: ptr csize_t): int32
      {.importc: "InitializeProcThreadAttributeList", stdcall,
        dynlib: "kernel32".}
    proc updateProcThreadAttributeR(list: pointer; flags: uint32;
                                    attribute: uint; value: pointer;
                                    size: csize_t; previous: pointer;
                                    returnSize: ptr csize_t): int32
      {.importc: "UpdateProcThreadAttribute", stdcall, dynlib: "kernel32".}
    proc deleteProcThreadAttributeListR(list: pointer)
      {.importc: "DeleteProcThreadAttributeList", stdcall, dynlib: "kernel32".}
    proc createProcessExR(app, cmdLine: WideCString;
                          processAttrs, threadAttrs: pointer;
                          inheritHandles: int32; flags: int32;
                          env: pointer; dir: WideCString;
                          startup: ptr StartupInfoEx;
                          info: ptr PROCESS_INFORMATION): int32
      {.importc: "CreateProcessW", stdcall, dynlib: "kernel32".}
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

    type OutHandle = Handle
    const noOut = Handle(-1)

    proc makePrivateDir(): string =
      ## A directory of this host's own, by a name no one can guess, which
      ## `CreateDirectoryW` refuses to reuse. "" when none could be made.
      var r: array[16, byte]
      if not urandom(r): return ""
      let dir = getTempDir() / ("nelli-replay-" & toHexString(r))
      if createDirectoryWR(newWideCString(dir), nil) == 0: return ""
      dir

    proc writeNew(path, data: string): bool =
      ## `data` to `path`, which must not exist yet (`CREATE_NEW`).
      let h = createFileWR(newWideCString(path), genericWrite, 0, nil,
                           createNewFlag, fileAttributeTemporary, Handle(0))
      if h == Handle(-1): return false
      result = true
      var at = 0
      while at < data.len:
        var n: uint32
        let want = uint32(min(data.len - at, 1 shl 20))
        if writeFileR(h, unsafeAddr data[at], want, addr n, nil) == 0 or
           n == 0:
          result = false
          break
        at += int(n)
      discard closeHandle(h)

    proc openNewOutput(path: string): OutHandle =
      ## The report's file, created here (`CREATE_NEW`) and read through this
      ## handle; the child opens it by name to write.
      createFileWR(newWideCString(path), genericRead, fileShareAll, nil,
                   createNewFlag, fileAttributeTemporary, Handle(0))

    proc outputSize(h: OutHandle): int64 =
      if getFileSizeExR(h, addr result) == 0: result = 0

    proc readOutput(h: OutHandle; most: int): string =
      result = newString(most)
      var at = 0
      while at < most:
        var n: uint32
        if readFileR(h, addr result[at], uint32(most - at), addr n, nil) == 0 or
           n == 0:
          break
        at += int(n)
      result.setLen(at)

    proc closeOutput(h: OutHandle) =
      discard closeHandle(h)

    proc environmentWith(name, value: string): seq[uint16] =
      ## The block `CreateProcessW` takes: the current environment with `name`
      ## set to `value`. An exact block rather than `SetEnvironmentVariable`,
      ## which another thread starting a process could inherit. A `name` the
      ## environment already has (one this program inherited) is left out, so
      ## the child sees one, ours.
      let prefix = newWideCString(name & "=")
      var plen = 0
      while prefix[plen].uint16 != 0: inc plen
      proc upper(c: uint16): uint16 =
        if c >= uint16('a') and c <= uint16('z'): c - 32 else: c
      let base = getEnvironmentStringsWR()
      if base != nil:
        let p = cast[ptr UncheckedArray[uint16]](base)
        var i = 0
        while p[i] != 0:
          # One variable, from `i` to its terminator.
          var e = i
          while p[e] != 0: inc e
          var same = e - i >= plen
          if same:
            for k in 0 ..< plen:
              if upper(p[i + k]) != upper(prefix[k].uint16):
                same = false
                break
          if not same:
            for k in i .. e: result.add p[k]   # with its terminator
          i = e + 1
        discard freeEnvironmentStringsWR(base)
      let added = newWideCString(name & "=" & value)
      var j = 0
      while added[j].uint16 != 0:
        result.add added[j].uint16
        inc j
      result.add 0'u16
      result.add 0'u16

    proc spawnAndWait(spec: string; timeoutMs: int; output: OutHandle;
                      c: var ReplayChild; lost, flooded: var bool): bool =
      ## False: no child ran (`c.why`). `lost`: it ended, and how is not
      ## known. `flooded`: its report grew past `replayReportCap`, and it was
      ## killed.
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
      # Inheritable from birth, and the only handle the child inherits: the
      # attribute list below names it alone (R1-21).
      var sa = SECURITY_ATTRIBUTES(nLength: int32(sizeof(SECURITY_ATTRIBUTES)),
                                   lpSecurityDescriptor: nil,
                                   bInheritHandle: 1)
      let null = createFileWR(newWideCString("NUL"), genericReadWrite,
                              fileShareRW, addr sa, openExistingFlag, 0,
                              Handle(0))
      if null == Handle(-1):
        discard closeHandle(job)
        c.why = "NUL could not be opened for the replay's child"
        return false
      var attrSize: csize_t = 0
      discard initializeProcThreadAttributeListR(nil, 1, 0, addr attrSize)
      var attrs = newSeq[byte](max(int(attrSize), 1))
      if initializeProcThreadAttributeListR(addr attrs[0], 1, 0,
                                            addr attrSize) == 0:
        discard closeHandle(null)
        discard closeHandle(job)
        c.why = "the replay's child could not be limited to the handles " &
                "it needs (error " & $getLastError() & ")"
        return false
      var inherit = [null]
      if updateProcThreadAttributeR(addr attrs[0], 0,
                                    procThreadAttributeHandleList,
                                    addr inherit[0],
                                    csize_t(sizeof(Handle)), nil, nil) == 0:
        deleteProcThreadAttributeListR(addr attrs[0])
        discard closeHandle(null)
        discard closeHandle(job)
        c.why = "the replay's child could not be limited to the handles " &
                "it needs (error " & $getLastError() & ")"
        return false
      var si: StartupInfoEx
      si.startupInfo.cb = int32(sizeof(StartupInfoEx))
      si.startupInfo.dwFlags = startfUseStdHandlesFlag
      si.startupInfo.hStdInput = null
      si.startupInfo.hStdOutput = null
      si.startupInfo.hStdError = null
      si.attributeList = addr attrs[0]
      var pi: PROCESS_INFORMATION
      var env = environmentWith(replayChildEnv, spec)
      let exe = newWideCString(getAppFilename())
      let ok = createProcessExR(exe, nil, nil, nil, 1,
                                createSuspendedFlag or createNoWindowFlag or
                                  createUnicodeEnvironmentFlag or
                                  extendedStartupInfoPresent,
                                addr env[0], nil, addr si, addr pi)
      let err = getLastError()
      deleteProcThreadAttributeListR(addr attrs[0])
      discard closeHandle(null)
      if ok == 0:
        discard closeHandle(job)
        c.why = "the program could not be re-executed (error " & $err & ")"
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
      # In slices, so the report's size is watched and no bound wraps an
      # `int32`.
      let start = getMonoTime()
      var ended = false
      var killed = false
      while true:
        var slice = 50'i32
        if timeoutMs > 0:
          let left = timeoutMs - (getMonoTime() - start).inMilliseconds
          if left <= 0:
            killed = true
            break
          slice = int32(min(left, 50))
        let w = waitForSingleObject(pi.hProcess, slice)
        if w == waitObject0:
          ended = true
          break
        if w != waitTimeoutResult:
          lost = true   # WAIT_FAILED: what it does is not known
          break
        if outputSize(output) > replayReportCap:
          flooded = true
          break
      if ended:
        var code: int32
        if getExitCodeProcess(pi.hProcess, code) == 0:
          lost = true
        else:
          let ucode = cast[uint32](code)
          if ucode >= 0xC0000000'u32:
            c.ending = reSignalled
            c.code = int(ucode)
          else:
            c.ending = reExited
            c.code = int(ucode)
      elif killed:
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
    var oNoFollow {.importc: "O_NOFOLLOW", header: "<fcntl.h>".}: cint

    type OutHandle = cint
    const noOut = cint(-1)

    proc makePrivateDir(): string =
      ## A directory only this user can enter, by a name `mkdtemp` chose and
      ## created. "" when none could be made.
      var tmpl = getTempDir() / "nelli-replay-XXXXXX"
      if mkdtemp(tmpl.cstring) == nil: return ""
      tmpl

    proc writeNew(path, data: string): bool =
      ## `data` to `path`, which must not exist yet (`O_EXCL`), as a file only
      ## this user can read.
      let fd = open(path.cstring,
                    O_WRONLY or O_CREAT or O_EXCL or oNoFollow or O_CLOEXEC,
                    Mode(0o600))
      if fd < 0: return false
      result = true
      var at = 0
      while at < data.len:
        let n = write(fd, unsafeAddr data[at], data.len - at)
        if n < 0 and errno == EINTR: continue
        if n <= 0:
          result = false
          break
        at += n
      discard close(fd)

    proc openNewOutput(path: string): OutHandle =
      ## The report's file, created here (`O_EXCL`) and read through this
      ## descriptor; the child opens it by name to write.
      open(path.cstring, O_RDONLY or O_CREAT or O_EXCL or oNoFollow or
           O_CLOEXEC, Mode(0o600))

    proc outputSize(h: OutHandle): int64 =
      var st: Stat
      if fstat(h, st) == 0: int64(st.st_size) else: 0

    proc readOutput(h: OutHandle; most: int): string =
      result = newString(most)
      var at = 0
      while at < most:
        let n = pread(h, addr result[at], most - at, Off(at))
        if n < 0 and errno == EINTR: continue
        if n <= 0: break
        at += n
      result.setLen(at)

    proc closeOutput(h: OutHandle) =
      discard close(h)

    proc childEnvironment(spec: string): seq[string] =
      ## This process's environment with the marker set to `spec`: built
      ## before the `fork`, so the child allocates nothing before `execve`.
      for k, v in envPairs():
        if k != replayChildEnv: result.add k & "=" & v
      result.add replayChildEnv & "=" & spec

    proc spawnAndWait(spec: string; timeoutMs: int; output: OutHandle;
                      c: var ReplayChild; lost, flooded: var bool): bool =
      ## As the Windows one. The child leads a process group of its own, and
      ## is signalled, it and its group, only while it is not yet waited for:
      ## until then its pid cannot name another process (R1-19).
      let exe = getAppFilename()
      let args = allocCStringArray([exe])
      let envp = allocCStringArray(childEnvironment(spec))
      let pid = fork()
      if pid < 0:
        let err = errno
        deallocCStringArray(args)
        deallocCStringArray(envp)
        c.why = "fork failed (errno " & $err & ")"
        return false
      if pid == 0:
        discard setpgid(0, 0)
        let null = open("/dev/null", O_RDWR)
        if null >= 0:
          discard dup2(null, 0)
          discard dup2(null, 1)
          discard dup2(null, 2)
        discard execve(exe.cstring, args, envp)
        c_exit_now(127)
      deallocCStringArray(args)
      deallocCStringArray(envp)
      discard setpgid(pid, pid)   # either side may run first
      {.cast(gcsafe).}:
        inc replayExecCount
      let start = getMonoTime()
      var status: cint
      var reaped = false       # waited for: its pid is no longer the host's
      var haveStatus = false
      var killed = false
      var nap = 1
      while true:
        let w = waitpid(pid, status, WNOHANG)
        if w == pid:
          reaped = true
          haveStatus = true
          break
        if w < 0:
          if errno == EINTR: continue
          # ECHILD: the host ignores SIGCHLD, or another wait took it.
          reaped = true
          break
        if outputSize(output) > replayReportCap:
          flooded = true
          break
        var left = 20'i64
        if timeoutMs > 0:
          left = timeoutMs - (getMonoTime() - start).inMilliseconds
          if left <= 0:
            killed = true
            break
        discard usleep(cuint(min(int64(nap), left)) * 1000)
        nap = min(nap * 2, 20)
      if not reaped:
        discard kill(-pid, SIGKILL)   # its group: what the SUT started with it
        discard kill(pid, SIGKILL)
        while true:
          let w = waitpid(pid, status, 0)
          if w == pid:
            haveStatus = true
            break
          if w < 0 and errno == EINTR: continue
          break
      if flooded:
        discard
      elif killed:
        c.ending = reTimedOut
      elif haveStatus and WIFSIGNALED(status):
        c.ending = reSignalled
        c.code = int(WTERMSIG(status))
      elif haveStatus and WIFEXITED(status):
        c.ending = reExited
        c.code = int(WEXITSTATUS(status))
      else:
        lost = true
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
  var oomSentR = false

  proc childOomR() {.nimcall, tags: [], gcsafe, raises: [].} =
    ## RFC-0005 0.9.1 (WA-7): as the fork path's `childOom`.
    {.cast(gcsafe).}:
      {.cast(tags: []).}:
        if not oomSentR:
          oomSentR = true
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
    ## loaded by another program), it must not go on re-executing. Only a
    ## marker its host set for it counts (`readChildRole`).
    childRole().site.len > 0

  proc removeQuietly(path: string) =
    try: removeFile(path)
    except CatchableError: discard

  proc runReplayReexec*(site, payload: string; timeoutMs: int): ReplayChild =
    ## RFC-0005 S8ct. The host's half: `payload` to a re-executed copy of this
    ## program, which the initialiser at call site `site` picks up
    ## (`replayChildEntry`), and what it reported.
    if inReplayChild():
      return refused("a replay's child does not start another")
    var r: array[16, byte]
    if not urandom(r):
      return refused("no random bytes for the replay's private directory")
    let nonce = toHexString(r)
    let dir = makePrivateDir()
    if dir.len == 0:
      return refused("a private directory could not be created for the " &
                     "replay's child")
    let input = dir / "in"
    let outName = dir / "out"
    var output = noOut
    defer:
      if output != noOut: closeOutput(output)
      removeQuietly(input)
      removeQuietly(outName)
      try: removeDir(dir)
      except CatchableError: discard
    if not writeNew(input, witnessFile(nonce, site, payload)):
      return refused("the replay's witness could not be written")
    output = openNewOutput(outName)
    if output == noOut:
      return refused("the replay's report file could not be created")
    var c = ReplayChild(ending: reSignalled)
    var lost, flooded = false
    flushFile(stdout)
    flushFile(stderr)
    if not spawnAndWait(nonce & "|" & dir, timeoutMs, output, c, lost,
                        flooded):
      return refused(c.why)
    var rd: ReportReader
    rd.feed(readOutput(output, replayReportCap + 1))
    if flooded or rd.corrupt:
      return stopped("")
    c.reached = rd.reached
    c.outOfMemory = rd.outOfMemory and c.ending != reTimedOut
    if rd.finished and c.ending != reTimedOut:
      readFlags(rd.flags, c)
      c.ending = reFinished
    elif rd.unreadable:
      c.ending = reRefused
      c.why = "the child could not read the witness"
      c.runDependent = true
    elif lost:
      c = statusLost(c)
    settled(c)

  proc replayChildEntry*(site: string;
                         run: proc (payload: string): ReplayReport {.nimcall.}):
                           bool =
    ## RFC-0005 S8ct. The child's half, from a `{.global.}` initialiser at each
    ## call site: returns at once except in the child of this very site, which
    ## runs the SUT and ends.
    let role = childRole()
    if role.site.len == 0 or role.site != site: return false
    quietChild()
    hostOomHookR = outOfMemHook
    outOfMemHook = childOomR
    var rep: ReplayReport
    var failed = false
    try:
      childOutput = open(role.output, fmWrite)
      hitOut = childOut
      let payload = role.payload
      var stack = (if payload.len >= 8: getInt64(payload, 0) else: 0'i64)
      if stack < 0 or stack > replayStackCap: stack = 0
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
