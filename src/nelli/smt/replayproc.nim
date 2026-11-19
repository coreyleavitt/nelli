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

import std/[strutils, monotimes, times, macros, atomics, cpuinfo]
when defined(windows) or defined(nelliReplayReexec):
  import std/os
import ../engine/markers
import ./replaywire   ## RFC-0016 INT-13
from ./buildprofile import buildIsExecutable

const
  replayForks* = defined(posix) and not defined(nelliReplayReexec)
  replayReexecs* = defined(windows) or
                   (defined(posix) and defined(nelliReplayReexec))
  replayExecs* = replayReexecs and defined(posix)
    ## RFC-0016 INT-29. The re-executed child is started by `fork` and
    ## `execve`, so it can fail to start after the fork (`execve` refused) and
    ## inherits the host's descriptors unless it closes them.
  hasMethodTable* = defined(nimHasMethodDispatchTable) and
                    buildIsExecutable
    ## RFC-0016 PRC-02b. The toolchain's method dispatch table exists, and this
    ## build can import it: the patched compiler writes the accessor for
    ## executables only (a library build would export a symbol every other Nim
    ## binary linking it also defines), so a library build keeps the stock
    ## decline.
  hasSubtypeTable* = defined(nimHasSubtypeHookTable) and
                     buildIsExecutable
    ## RFC-0016 PRC-02m. The toolchain's subtype-hook table exists, and this
    ## build can import it (executables only, as `hasMethodTable`).
  replayMemoryLimit* = 2 shl 30
    ## What a replay may allocate past the address space it starts with. An
    ## allocation loop then fails in the child ("out of memory", a real exit)
    ## instead of taking the machine's memory from the host.
  replayProcessLimit* = 64
    ## RFC-0016 INT-28. How many processes a replay's SUT may start beside the
    ## child. Windows: the job's `ActiveProcessLimit`, counting the child.
    ## Linux: `RLIMIT_NPROC`, which counts every thread of the user, so the
    ## child's is the threads the system ran as it started plus this many.
  replayFileSizeLimit* = 1'i64 shl 32
    ## RFC-0016 INT-28. The largest file a replay may write (POSIX
    ## `RLIMIT_FSIZE`). Past it the child is killed by `SIGXFSZ`, which the
    ## host reads as a run stopped at a bound (`reTimedOut`), never a crash.

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
      ## RFC-0005 0.9.1 (WA-7), review R5 (D4b). The run-dependence the ending
      ## cannot express. This flag and `ending` are the two sources of a
      ## replay's `rdReplay`, and `ReplayResult.runDependence` (`replayresult.nim`)
      ## joins them: a `reLost` ending, a `reTimedOut` one stopped for a reason
      ## other than the bound (a limit, a flood: `why`), and a `reSignalled`
      ## one ended from outside the SUT (`signalledFromOutside`) are
      ## run-dependent BY CONSTRUCTION, whatever this flag says. RFC-0016
      ## INT-32: a child killed at the bound (`killedAtBound`) is not: the
      ## bound is keyed. This flag carries the rest: an allocation that failed at
      ## the memory limit (`outOfMemory`), a child that could not be started or
      ## handed its state for a reason of the moment (a failed `fork`, pipe or
      ## job object, a runtime hook the host had set), and a report the host
      ## could not read. Another run may decide these, so a verdict they leave
      ## undecided is not cached.

var replayExecCount: Atomic[int]
  ## How many children the host has started: symex never runs `fn` itself, so
  ## this counts real executions. What a SUT does to the host's variables can no
  ## longer count them. RFC-0016 INT-28: atomic, as replays may run on several
  ## threads at once.

proc replayExecutions*(): int =
  ## RFC-0005 S8ct. How many replays this process has run.
  {.cast(gcsafe).}:
    replayExecCount.load()

proc countExecution() =
  {.cast(gcsafe).}:
    replayExecCount.atomicInc()

type
  ReplayLimits* = object
    ## RFC-0016 INT-28. The limits the current process runs under, as
    ## `replayLimitsHeld` reads them; -1 for none. A replay's child holds the
    ## ones its platform applies: POSIX all four (`processes` on Linux only;
    ## `memory` where the system enforces an address-space limit, so not on
    ## macOS); Windows `memory` and `processes`, from its job object.
    memory*: int64       ## bytes of address space (Windows: committed memory)
    cpuSeconds*: int64   ## seconds of CPU time
    fileSize*: int64     ## bytes of one file
    processes*: int64    ## processes (POSIX: of the user, threads included)

proc cpuBound(timeoutMs: int): int =
  ## RFC-0016 INT-28. The CPU seconds a replay bounded at `timeoutMs` may use:
  ## every processor busy for the whole bound, and a second more. Not stricter
  ## than the bound itself on any SUT; it stops a child the host no longer
  ## watches (the host gone where no death signal reaches the child). 0: none.
  if timeoutMs <= 0: 0
  else: ((timeoutMs + 999) div 1000) * max(1, countProcessors()) + 1

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
  ## The child as the host reports it. What makes it run-dependent is
  ## stated once, at `ReplayChild.runDependent`.
  result = c
  if c.outOfMemory: result.runDependent = true

proc refused(why: string; runDependent = true): ReplayChild =
  ## No child ran. `runDependent` defaults to true; see
  ## `ReplayChild.runDependent` for what it means (`refusedStatically` and
  ## `refusedNotMarshallable` pass false).
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

when hasMethodTable:
  type MethodRow = object
    bucket, fn: pointer
    recv: cstring

  proc nimMethodDispatchTable(count: ptr int): pointer
    {.importc: "nimMethodDispatchTable", cdecl.}
    ## RFC-0016 PRC-02b. The patched toolchain's per-binary table: one row per
    ## branch of every method dispatcher, in the dispatcher's if-chain order.

  proc methodDispatchRefusal*(names: openArray[string];
                              called, scanned: openArray[pointer]): string =
    ## RFC-0016 PRC-02b. Empty when every body a dispatcher of the methods
    ## `called` (the bodies at those addresses, named `names`) can run is one of
    ## `scanned`, the bodies of the methods the scan read; else the decline. The
    ## child is this
    ## binary, so the table the host reads is the child's. It lists what the
    ## dispatcher chooses from, an override in a module the entry cannot see
    ## included, and the one of two same-signature overrides the compiler kept.
    ## A dispatcher's whole bucket is checked, not only the receivers the replay
    ## can build: an unread override of an unrelated subtype declines too.
    var n = 0
    let rows = cast[ptr UncheckedArray[MethodRow]](nimMethodDispatchTable(addr n))
    if n < 0:
      return "dispatch of a method here is not an if-chain (vtables), so its " &
             "overrides cannot be listed"
    var buckets: seq[pointer]
    var bucketName: seq[string]    # a scanned method that names each bucket
    for i, m in called:
      var found = false
      for r in 0 ..< n:
        if rows[r].fn == m:
          found = true
          if rows[r].bucket notin buckets:
            buckets.add rows[r].bucket
            bucketName.add names[i]
      if not found:
        return "`" & names[i] & "`, a method the toolchain's dispatch table " &
               "does not list"
    for r in 0 ..< n:
      let b = buckets.find(rows[r].bucket)
      if b >= 0 and rows[r].fn notin scanned:
        var recv = $rows[r].recv
        let colon = recv.find(':')
        if colon >= 0: recv.setLen colon
        return "an override of `" & bucketName[b] & "` for `" & recv &
               "` the entry could not see"

when hasMethodTable:
  proc methodRouteGuard*(routes: seq[string]; names: openArray[string];
                         called, scanned: openArray[pointer]): seq[string] =
    ## RFC-0016 PRC-02m. The route scan of a SUT that dispatches a method read
    ## the methods registered at the entry as the override set, a hypothesis.
    ## This run's table confirms it (`methodDispatchRefusal`): confirmed, the
    ## routes stand; refused, every read of a variable declines, as the walk's
    ## dispatch over the overrides the entry saw cannot stand for the body the
    ## binary runs (`!` is `routeOpenValue`; this module cannot import it).
    result = @routes
    let why = methodDispatchRefusal(names, called, scanned)
    if why.len > 0:
      result.add "!|" & why & " (the dispatch table and the scan disagree)"

when hasSubtypeTable:
  type SubtypeHookRow = object
    base, sub: cstring
    hook: pointer
    open: int

  proc nimSubtypeHookTable(count: ptr int): pointer
    {.importc: "nimSubtypeHookTable", cdecl.}
    ## RFC-0016 PRC-02m. The patched toolchain's per-binary table: per proper
    ## ancestor of every inheriting object type the binary writes a header for,
    ## each user lifetime hook a value of the subtype may run.

  proc subtypeHookRefusal*(bases: openArray[string];
                           scanned: openArray[pointer]): string =
    ## RFC-0016 PRC-02m. Empty when every user lifetime hook a subtype of one of
    ## `bases` (`module.Type`) may run in this binary is one of `scanned`, the
    ## hooks the route scan read; else the decline. The table lists every
    ## subtype the binary can construct, one declared in a module the entry
    ## cannot see included, so a subtype whose hooks the scan never read is
    ## named here.
    var n = 0
    let rows = cast[ptr UncheckedArray[SubtypeHookRow]](nimSubtypeHookTable(addr n))
    if n < 0:
      return "lifetime hooks do not run on this memory manager's path, so the " &
             "toolchain's subtype table lists none"
    for r in 0 ..< n:
      if $rows[r].base notin bases: continue
      if rows[r].open != 0:
        return "the subtype `" & $rows[r].sub & "` of `" & $rows[r].base &
               "` holds a closure, whose environment's hooks cannot be listed"
      if rows[r].hook != nil and rows[r].hook notin scanned:
        return "the subtype `" & $rows[r].sub & "` of `" & $rows[r].base &
               "` has a lifetime hook the entry could not see"

  proc subtypeRouteGuard*(routes: seq[string]; bases: openArray[string];
                          scanned: openArray[pointer]): seq[string] =
    ## RFC-0016 PRC-02m. The route scan of a SUT that holds a `ref` of an
    ## object hierarchy read the hooks of the subtypes it could see, a
    ## hypothesis: no other subtype runs a hook. This run's table confirms it
    ## (`subtypeHookRefusal`); refused, every read of a variable declines
    ## (`!`, as `methodRouteGuard`).
    result = @routes
    let why = subtypeHookRefusal(bases, scanned)
    if why.len > 0:
      result.add "!|" & why & " (the subtype table and the scan disagree)"

proc closureEnvRefusal*[T: proc](name: string; x: T;
                                 benign: openArray[pointer] = []): string =
  ## RFC-0016 W3-z R8. Empty when the closure the module-level variable `name`
  ## holds as the run starts runs no lifetime hook when it is dropped: it is
  ## nil, it has no environment, or its environment's type has no destructor
  ## (every captured value is plain bits). Otherwise the decline, naming the
  ## variable: the scan never read the code that built the environment, so
  ## the hooks dropping it runs cannot be listed. Read under ARC/ORC, where
  ## an environment is an object whose first field is its type's
  ## `TNimTypeV2`, whose first field is the destructor; any other memory
  ## manager declines. RFC-0016 W3-z R11: an environment with a destructor
  ## is no hook the scan misses when the closure's routine is in `benign`,
  ## the code addresses of the nested routines whose environment holds only
  ## values whose drop runs the compiler's hooks (`dsl_parser.envBenignExpr`,
  ## `benignEnvCodes`): a routine's code names its environment's type.
  when sizeof(T) <= sizeof(pointer):
    ""
  else:
    if x.isNil or rawEnv(x).isNil: return ""
    let why = "the closure `" & name & "` holds when the run starts has a " &
              "captured environment"
    when defined(gcArc) or defined(gcOrc) or defined(gcAtomicArc):
      let rti = cast[ptr pointer](rawEnv(x))[]
      if rti != nil and cast[ptr pointer](rti)[] == nil: return ""
      # RFC-0016 W3-z R11: or its routine is one whose environment's
      # destructor is the compiler's and runs no user code (`benign`).
      if rti != nil and rawProc(x) in benign: return ""
      why & " whose lifetime hooks the scan cannot list (dropping it runs them)"
    else:
      why & ", whose type this memory manager does not describe"

macro nestedRoutineAddrs*(probe: typed; rs: varargs[typed]): untyped =
  ## RFC-0016 W3-z R10. The code addresses of the nested routines `rs`, in
  ## order. A nested routine that captures is a closure: code that names it
  ## builds one with its enclosing routine's environment, which only that
  ## routine and module-level code (where it has none) can do. So the
  ## addresses are taken only where `probe` (a variable declared beside this
  ## call) is module-level; inside a routine every slot a capturing routine
  ## holds is nil, which no value matches (the settle and the wire then name
  ## nothing for it).
  ## RFC-0016 W3-z R11: the enclosing routine's address is taken first. The
  ## code generator lifts a nested routine's captures when it generates the
  ## routine enclosing it; naming the nested one first, from module-level
  ## code of the same module, generates it unlifted (an internal compiler
  ## error: its captured local "not init").
  ## RFC-0016 W3-z R12: every routine enclosing it is, outermost first. A
  ## routine nested in a nested one is lifted when the outermost is
  ## generated; naming only the routine enclosing it is the same failure.
  ## A capturing enclosing routine is named through `rawProc`, as `rs` are.
  let top = owner(probe).kind == nnkSym and symKind(owner(probe)) == nskModule
  var items = nnkBracket.newTree()
  for r in rs:
    if top:
      var chain: seq[NimNode]
      var o = owner(r)
      while o.kind == nnkSym and symKind(o) in {nskProc, nskFunc, nskMethod,
                                                nskConverter} and chain.len < 64:
        chain.insert(o, 0)
        o = owner(o)
      var first = newStmtList()
      for e in chain:
        let held = genSym(nskLet, "enclosingFirst")
        first.add quote do:
          let `held` {.used.} =
            (when compiles(cast[pointer](`e`)): cast[pointer](`e`)
             else: rawProc(`e`))
      items.add quote do:
        (when compiles(cast[pointer](`r`)): cast[pointer](`r`)
         else: (block:
           `first`
           rawProc(`r`)))
    else:
      items.add quote do:
        (when compiles(cast[pointer](`r`)): cast[pointer](`r`)
         else: pointer(nil))
  if items.len == 0:
    result = quote do: newSeq[pointer]()
  else:
    result = quote do: @`items`

proc benignEnvCodes*(codes: seq[pointer]; ok: openArray[bool]): seq[pointer] =
  ## RFC-0016 W3-z R11. The code addresses of `codes` (`nestedRoutineAddrs`)
  ## whose slot of `ok` holds: the routines whose environment runs no user
  ## hook when dropped. A nil address (one not taken) names nothing.
  for i, c in codes:
    if c != nil and i < ok.len and ok[i]: result.add c

proc closureRouteGuard*(routes: seq[string]; refusals: openArray[string]):
    seq[string] =
  ## RFC-0016 W3-z R8. The route scan of a SUT that names a module-level
  ## closure variable left its type closed, a hypothesis: what each holds when
  ## the run starts runs no hook when dropped (`closureEnvRefusal`). Refused,
  ## every writable global is open (`*`, the scan's own answer for a closure
  ## it cannot read), with the variable named.
  result = @routes
  for why in refusals:
    if why.len > 0:
      result.add "*|" & why
      return

proc refusedHostHook*(why: string): ReplayChild =
  ## RFC-0005 0.9.1 (WA-7). As `refusedNotMarshallable`, for a runtime hook the
  ## host had set at the time (`hostRuntimeHook`): a run without it replays,
  ## so the decline depends on the run.
  refused("replay not marshallable: " & why & " (on this platform replay " &
          "runs in a re-executed child, which must be handed what the SUT " &
          "reaches; a Linux or macOS run forks and replays it)",
          runDependent = true)

proc putHostHooks*(w: var WireWriter): string =
  ## RFC-0005 batch 11, RFC-0016 INT-13. The runtime hooks of the stdlib's that
  ## the program set, handed to a re-executed child, which starts without
  ## them: a hook is a proc value the host installed at run time, and it
  ## changes what the SUT does (a `raise` runs it, an allocation failure, an
  ## exception nothing catches). Each is written as a proc value
  ## (`replaywire.nim`), so one naming a routine the replayed code names (whose
  ## state the child is then handed) is installed in the child, and any other
  ## declines. Returns "", or the hook that declines, named.
  ## `setControlCHook` is not among them (INT-15).
  template put(h: untyped) =
    when declared(h):
      try:
        w.wirePut(h)
      except WireError as e:
        return "`" & astToStr(h) & "`, a runtime hook the host set, holding " &
               e.msg
  put globalRaiseHook
  put localRaiseHook
  put outOfMemHook
  put unhandledExceptionHook
  put onUnhandledException
  put errorMessageWriter
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

# ---- a child the host has started and not yet finished with -------------------
#
# RFC-0016 INT-32 (item 8). Starting a child and waiting for it are two steps,
# so the host can watch several at once (`replayInOrder`, `replayresult.nim`):
# `stepChild` waits on one for at most a slice, `stopChild` kills one whose
# ending nobody will read, `awaitChild` waits it out. A child that was never
# started (refused) is `readyChild`, done from the start.

type
  PendingChild* = ref object of RootObj
    done: bool
    res: ReplayChild

proc readyChild*(c: ReplayChild): PendingChild =
  ## A child decided without a run (a refusal), or one already waited out.
  PendingChild(done: true, res: c)

proc childDone*(p: PendingChild): bool =
  ## Its ending is known (`childEnding`), or it was stopped.
  p.done

proc childEnding*(p: PendingChild): ReplayChild =
  ## How it ended. Only once `childDone`.
  doAssert p.done, "childEnding of a child still running"
  p.res

# ---- POSIX: what both ways of starting a child share ---------------------------

when defined(posix):
  import std/posix

  # At module scope: an `importc` var declared in a proc is emitted as a C
  # local of that name, which shadows the constant with an uninitialised one.
  var rlimitCore {.importc: "RLIMIT_CORE", header: "<sys/resource.h>".}: cint
  var rlimitCpu {.importc: "RLIMIT_CPU", header: "<sys/resource.h>".}: cint
  var rlimitFsize {.importc: "RLIMIT_FSIZE", header: "<sys/resource.h>".}: cint
  var rlimitNproc {.importc: "RLIMIT_NPROC", header: "<sys/resource.h>".}: cint
  var rlimInfinity {.importc: "RLIM_INFINITY", header: "<sys/resource.h>".}: int
  when defined(openbsd):
    # OpenBSD has no RLIMIT_AS; its data limit counts anonymous mappings.
    var rlimitMem {.importc: "RLIMIT_DATA", header: "<sys/resource.h>".}: cint
  else:
    var rlimitMem {.importc: "RLIMIT_AS", header: "<sys/resource.h>".}: cint
  var mapAnon {.importc: "MAP_ANON", header: "<sys/mman.h>".}: cint
  var pPid {.importc: "P_PID", header: "<sys/wait.h>".}: cint
  var wExited {.importc: "WEXITED", header: "<sys/wait.h>".}: cint
  var wNoWait {.importc: "WNOWAIT", header: "<sys/wait.h>".}: cint

  when defined(linux):
    proc c_prctl(option: cint; arg: culong): cint
      {.importc: "prctl", header: "<sys/prctl.h>".}
    const prSetPdeathsig = cint(1)
    proc c_syscall(n: clong): clong
      {.importc: "syscall", header: "<unistd.h>", varargs.}
  when defined(linux) or defined(freebsd) or defined(netbsd) or
       defined(openbsd) or defined(dragonfly):
    proc c_pipe2(fds: var array[2, cint]; flags: cint): cint
      {.importc: "pipe2", header: "<unistd.h>".}

  proc finite(v: int): bool = v != rlimInfinity and v >= 0

  proc lowerSoft(res: cint; v: int) =
    ## RFC-0016 INT-28. The soft limit `res` to `v`, unless it is already
    ## lower, and never past the hard one.
    var r: RLimit
    if getrlimit(res, r) != 0: return
    var x = v
    if finite(r.rlim_max) and x > r.rlim_max: x = r.rlim_max
    if finite(r.rlim_cur) and r.rlim_cur <= x: return
    r.rlim_cur = x
    discard setrlimit(res, r)

  proc mapsUnder(limit: int; saved: RLimit; page: int): int =
    ## 1: one more page maps under an address-space limit of `limit`; 0: it
    ## does not; -1: the limit could not be set.
    var r = saved
    r.rlim_cur = limit
    if setrlimit(rlimitMem, r) != 0: return -1
    let p = mmap(nil, page, PROT_READ or PROT_WRITE, MAP_PRIVATE or mapAnon,
                 -1, 0)
    if p == MAP_FAILED: return 0
    discard munmap(p, page)
    1

  proc memoryInUse(): int =
    ## RFC-0016 INT-28 (R1-31). The address space this process maps, to a
    ## page, found by halving the least limit under which one more page maps:
    ## the same on every POSIX system that enforces the limit, where Linux's
    ## `/proc/self/statm` was read before and the others had no cap at all.
    ## 0 where the system does not enforce it (a page maps under a limit of
    ## one page: macOS) or a limit cannot be set. It allocates nothing, so it
    ## may run between `fork` and the SUT.
    var saved: RLimit
    if getrlimit(rlimitMem, saved) != 0: return 0
    let page = int(sysconf(SC_PAGESIZE))
    var lo = page
    var hi =
      if finite(saved.rlim_max): saved.rlim_max
      else: (when sizeof(int) >= 8: 1 shl 47 else: high(int) div 2)
    result = 0
    if mapsUnder(lo, saved, page) == 0 and mapsUnder(hi, saved, page) == 1:
      result = -1
      while hi - lo > page:
        let mid = lo + (hi - lo) div 2
        case mapsUnder(mid, saved, page)
        of 1: hi = mid
        of 0: lo = mid
        else:
          result = 0
          break
      if result != 0: result = hi - page
    discard setrlimit(rlimitMem, saved)

  proc limitMemory() =
    ## The replay's memory limit, relative to what this process maps now.
    let used = memoryInUse()
    if used > 0: lowerSoft(rlimitMem, used + replayMemoryLimit)

  proc limitChild(cpuSeconds, processes: int) =
    ## RFC-0016 INT-28 (R1-31). No core file, and the CPU, file-size and
    ## process limits (`cpuBound`, `replayFileSizeLimit`, `processBound`).
    ## Inherited across `exec`.
    var noCore = RLimit(rlim_cur: 0, rlim_max: 0)
    discard setrlimit(rlimitCore, noCore)
    if cpuSeconds > 0: lowerSoft(rlimitCpu, cpuSeconds)
    lowerSoft(rlimitFsize, int(replayFileSizeLimit))
    if processes > 0: lowerSoft(rlimitNproc, processes)

  proc replayLimitsHeld*(): ReplayLimits =
    ## RFC-0016 INT-28. The soft limits this process runs under.
    proc soft(res: cint): int64 =
      var r: RLimit
      if getrlimit(res, r) == 0 and finite(r.rlim_cur): int64(r.rlim_cur)
      else: -1
    ReplayLimits(memory: soft(rlimitMem), cpuSeconds: soft(rlimitCpu),
                 fileSize: soft(rlimitFsize), processes: soft(rlimitNproc))

  proc processBound(): int =
    ## RFC-0016 INT-28. The child's `RLIMIT_NPROC`: the threads the system
    ## runs now (`/proc/loadavg`, at least the user's, which the limit
    ## counts) and `replayProcessLimit` more. 0, none, off Linux: no other
    ## system reads the count without a privileged interface.
    when defined(linux):
      try:
        let f = readFile("/proc/loadavg")
        let slash = f.find('/')
        if slash < 0: return 0
        var n = 0
        var i = slash + 1
        while i < f.len and f[i] in {'0' .. '9'}:
          n = n * 10 + (ord(f[i]) - ord('0'))
          inc i
        if n > 0: n + replayProcessLimit else: 0
      except CatchableError:
        0
    else:
      0

  proc limitEnding(status: cint; cpuSeconds: int): string =
    ## RFC-0016 INT-28. Why a child a resource limit stopped was stopped, or
    ## "": `SIGXCPU` past the CPU limit, `SIGXFSZ` past the file-size limit.
    ## Such a run is undecided (`reTimedOut`), not a crash of the SUT.
    if not WIFSIGNALED(status): return ""
    let sig = WTERMSIG(status)
    if sig == SIGXCPU and cpuSeconds > 0:
      "it used the replay's CPU-time limit (" & $cpuSeconds &
        " s) and was stopped"
    elif sig == SIGXFSZ:
      "it wrote a file past the replay's file-size limit (" &
        $replayFileSizeLimit & " bytes) and was stopped"
    else: ""

  proc hasEnded(pid: Pid): int =
    ## RFC-0016 INT-28 (R1-24). 1: the child has ended and is not yet
    ## waited for, so its pid and the group it leads are still the host's,
    ## and the group can still be killed. 0: it runs. -1: it is no longer
    ## the host's child (`SIGCHLD` ignored, or another wait took it).
    var info: SigInfo
    while true:
      zeroMem(addr info, sizeof(info))
      if waitid(pPid, Id(pid), info, wExited or WNOHANG or wNoWait) == 0:
        return (if info.si_pid == pid: 1 else: 0)
      if errno != EINTR: return -1

  proc killGroup(pid: Pid) =
    ## The child and its group: what the SUT started. Only for a child not
    ## yet waited for (`hasEnded`): until then its pid, and the group it
    ## leads, are this process's and cannot name another.
    discard kill(-pid, SIGKILL)
    discard kill(pid, SIGKILL)

  proc enterGroup(hostPid: Pid) =
    ## In a child, before anything else: it leads a group of its own, so
    ## that what the SUT starts is killed with it (every POSIX system, not
    ## Linux alone: R2-25), and on Linux it dies with the host. The host may
    ## have died between the `fork` and the `prctl`, when no signal comes, so
    ## the parent is checked after (R1-32).
    discard setpgid(0, 0)
    when defined(linux):
      discard c_prctl(prSetPdeathsig, culong(SIGKILL))
      if getppid() != hostPid: exitnow(125)

  proc closeFrom(low: cint) =
    ## RFC-0016 INT-29 (R2-24). Every descriptor from `low` up, in a child
    ## about to `exec`: what the host opened without `O_CLOEXEC` is not the
    ## program's to inherit.
    when defined(linux):
      if c_syscall(clong(436), cuint(low), high(cuint), cuint(0)) == 0:
        return   # close_range(2)
    var r: RLimit
    var top = 65536
    if getrlimit(RLIMIT_NOFILE, r) == 0 and finite(r.rlim_max) and
       r.rlim_max < top:
      top = r.rlim_max
    for fd in low ..< cint(top): discard close(fd)

proc replayLimitSignals*(): seq[tuple[signal: int, limit: string]] =
  ## RFC-0016 INT-28. The signals a replay child's resource limits stop it
  ## with, and the word for the limit each names in `ReplayChild.why`: a run
  ## one stops is undecided (`reTimedOut`). None on Windows, where the job's
  ## limits end the process and the replay's deadline bounds its time.
  when defined(posix):
    @[(int(SIGXCPU), "CPU"), (int(SIGXFSZ), "file-size")]
  else:
    @[]

func signalledFromOutside*(c: ReplayChild): bool =
  ## RFC-0016 INT-32 (R1-33). The child was ended by a signal the SUT's own
  ## run does not raise: one sent from outside it (`SIGKILL` from the OOM
  ## killer or an operator, `SIGTERM`, `SIGINT`, `SIGHUP`, ...). Another run
  ## may not be, so the replay is run-dependent (`ReplayResult.runDependence`).
  ## A synchronous fault (`SIGSEGV`, `SIGBUS`, `SIGFPE`, `SIGILL`, `SIGTRAP`,
  ## `SIGSYS`) or an abort (`SIGABRT`: `abort`, a failed C assertion) is the
  ## program's, and the same on every run. A signal the SUT sends itself
  ## with `kill` cannot be told from one sent from outside, so it is
  ## run-dependent too: conservative, a verdict not stored is only re-derived.
  ## Windows reports a system exception code, always the program's.
  when defined(posix):
    c.ending == reSignalled and
      c.code notin [int(SIGSEGV), int(SIGBUS), int(SIGFPE), int(SIGILL),
                    int(SIGABRT), int(SIGTRAP), int(SIGSYS)]
  else:
    false

func killedAtBound*(c: ReplayChild): bool =
  ## RFC-0016 INT-32 (R4-07). The child ran past `replayTimeoutMs` and was
  ## killed for it, and for nothing else (no `why`: not a resource limit, not
  ## a report flood). The bound and the host are in the cache key, so this is
  ## the key's fact, and the verdict it leaves is stored.
  c.ending == reTimedOut and c.why.len == 0

# ---- fork ---------------------------------------------------------------------

when replayForks:
  proc c_fflush(f: pointer): cint {.importc: "fflush", header: "<stdio.h>".}
  proc c_signal(sig: cint; handler: pointer): pointer
    {.importc: "signal", header: "<signal.h>".}
  proc c_atexit(f: proc () {.noconv.}): cint
    {.importc: "atexit", header: "<stdlib.h>".}

  const hasOnExit = defined(linux) and not defined(musl)
  when hasOnExit:
    proc c_on_exit(f: proc (status: cint; arg: pointer) {.noconv.};
                   arg: pointer): cint
      {.importc: "on_exit", header: "<stdlib.h>".}

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

  proc enterChild(hostPid: Pid; cpuSeconds, processes: int) =
    ## Everything that keeps the child's ending from touching the host's world.
    enterGroup(hostPid)
    limitChild(cpuSeconds, processes)
    # The host's own mappings count against the limit, so it is relative.
    limitMemory()
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

  proc runChildBody(body: proc (): ReplayReport {.closure, gcsafe.};
                    hostPid: Pid; cpuSeconds, processes: int) =
    enterChild(hostPid, cpuSeconds, processes)
    hitOut = childOut
    var rep: ReplayReport
    try:
      {.cast(gcsafe).}:
        rep = body()
    except Exception:
      exitnow(121)
    childWrite(['E', flagsChar(rep)])
    exitnow(0)

  proc reportPipe(fds: var array[2, cint]): bool =
    ## The report's pipe, close-on-exec from birth where the system can
    ## (`pipe2`, R1-32: another thread's `fork` and `exec` between `pipe` and
    ## `fcntl` would hand its program both ends; macOS has no `pipe2`).
    ## RFC-0016 INT-29 (R2-26): neither end is one of fd 0-2, which a host
    ## that closed them is handed here, and over which the child puts
    ## `/dev/null`, closing its end of the report.
    when declared(c_pipe2):
      if c_pipe2(fds, O_CLOEXEC) != 0: return false
    else:
      if pipe(fds) != 0: return false
      discard fcntl(fds[0], F_SETFD, FD_CLOEXEC)
      discard fcntl(fds[1], F_SETFD, FD_CLOEXEC)
    for i in 0 .. 1:
      if fds[i] < 3:
        let d = fcntl(fds[i], F_DUPFD_CLOEXEC, cint(3))
        if d < 0:
          discard close(fds[0])
          discard close(fds[1])
          return false
        discard close(fds[i])
        fds[i] = d
    true

  type ForkRun = ref object of PendingChild
    ## RFC-0016 INT-32 (item 8). A forked child being watched.
    pid: Pid
    fd: cint                 # the report's read end
    timeoutMs, cpuSeconds: int
    start: MonoTime
    rd: ReportReader
    eof: bool
    reaped: bool             # waited for: its pid is no longer the host's
    ended: bool              # ended, and not yet waited for
    haveStatus: bool         # and `status` is what it ended with
    status: cint
    killed: bool

  proc reap(p: ForkRun; flags: cint) =
    let w = waitpid(p.pid, p.status, flags)
    if w == p.pid:
      p.reaped = true
      p.haveStatus = true
    elif w < 0 and errno != EINTR:
      # ECHILD: the host ignores SIGCHLD, or another wait took it. Gone,
      # and its status with it; its pid may already name another process.
      p.reaped = true

  proc readSome(p: ForkRun; wait: cint): bool =
    ## Reads what is there within `wait` ms; false when nothing was.
    var pf = TPollfd(fd: p.fd, events: POLLIN)
    if poll(addr pf, Tnfds(1), wait) > 0:
      var chunk: array[512, char]
      let n = read(p.fd, addr chunk[0], chunk.len)
      if n > 0:
        p.rd.feed(chunk.toOpenArray(0, n - 1))
        result = true
      elif n == 0 or errno != EINTR:
        p.eof = true

  proc watching(p: ForkRun): bool =
    not (p.rd.done or p.rd.corrupt or p.reaped or p.ended or p.killed)

  proc forkFinish(p: ForkRun) =
    if not p.reaped:
      # Timed out, flooding, finished, or ended by itself: either way nothing
      # more is read from it, and what the SUT started dies with it. Not yet
      # waited for, so its pid and its group are ours.
      killGroup(p.pid)
      while not p.reaped: p.reap(0)
    # What a child wrote before it ended, up to the cap: a SUT's children
    # outside its group may still be writing.
    while not (p.rd.done or p.rd.corrupt or p.eof):
      if not p.readSome(0): break
    discard close(p.fd)
    p.done = true
    if p.rd.corrupt:
      p.res = stopped("")
      return
    var c = ReplayChild(reached: p.rd.reached, outOfMemory: p.rd.outOfMemory)
    let limit = if p.haveStatus: limitEnding(p.status, p.cpuSeconds) else: ""
    if p.rd.finished:
      readFlags(p.rd.flags, c)
      c.ending = reFinished
    elif p.rd.exited:
      c.ending = reExited
      c.code = p.rd.code
    elif p.killed:
      c.ending = reTimedOut
    elif limit.len > 0:
      c.ending = reTimedOut
      c.why = limit
    elif p.haveStatus and WIFSIGNALED(p.status):
      c.ending = reSignalled
      c.code = int(WTERMSIG(p.status))
    elif p.haveStatus and WIFEXITED(p.status):
      c.ending = reExited
      c.code = int(WEXITSTATUS(p.status))
    else:
      c = statusLost(c)
    p.res = settled(c)

  proc forkStep(p: ForkRun; slice: int) =
    ## One wait of at most `slice` ms on the child; finished with it once it
    ## has reported, ended or run past its bound.
    if p.watching:
      var wait = cint(max(slice, 0))
      if p.timeoutMs > 0:
        let left = p.timeoutMs - (getMonoTime() - p.start).inMilliseconds
        if left <= 0:
          p.killed = true
        else:
          wait = cint(min(left, int64(wait)))
      if not p.killed:
        if not p.eof:
          discard p.readSome(wait)
        else:
          discard usleep(cuint(wait) * 1000)
        if not (p.rd.done or p.rd.corrupt):
          # A child's own children may hold the pipe open past its end, and
          # the pipe may be closed while it still runs. RFC-0016 INT-28
          # (R1-24): an ended child is left unwaited for, so its group is
          # still the host's to kill below.
          case hasEnded(p.pid)
          of 1: p.ended = true
          of -1: p.reaped = true
          else: discard
    if not p.watching: p.forkFinish()

  proc forkStop(p: ForkRun) =
    ## Killed, its group with it, and nothing it wrote read.
    if not p.reaped:
      killGroup(p.pid)
      while not p.reaped: p.reap(0)
    discard close(p.fd)
    p.done = true

  proc startReplayForked*(body: proc (): ReplayReport {.closure, gcsafe.};
                          timeoutMs: int): PendingChild =
    ## RFC-0005 S8ct. `body` in a forked child, killed at `timeoutMs` (`<= 0`: no
    ## bound). RFC-0016 INT-32 (item 8): started, not waited for
    ## (`stepChild`, `awaitChild`).
    var fds: array[2, cint]
    if not reportPipe(fds):
      return readyChild(
        refused("a pipe could not be created for the replay's child"))
    let cpuSeconds = cpuBound(timeoutMs)
    let processes = processBound()
    let hostPid = getpid()
    # Whatever the host has buffered must not be written twice.
    discard c_fflush(nil)
    let pid = fork()
    if pid < 0:
      let err = errno
      discard close(fds[0])
      discard close(fds[1])
      return readyChild(refused("fork failed (errno " & $err & ")"))
    if pid == 0:
      childFd = fds[1]
      discard close(fds[0])
      runChildBody(body, hostPid, cpuSeconds, processes)
      exitnow(122)   # not reached
    countExecution()
    discard close(fds[1])
    discard setpgid(pid, pid)   # either side may run first
    ForkRun(pid: pid, fd: fds[0], timeoutMs: timeoutMs,
            cpuSeconds: cpuSeconds, start: getMonoTime())


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
    site, payload, output, input: string

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
                       output: dir / "out", input: dir / "in")
    # One child: a process the SUT starts must not take itself for it.
    # RFC-0016 INT-29: `in` is removed when the child takes the witness
    # (`replayChildEntry`), not here.
    delEnv(replayChildEnv)

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
      jobObjectLimitActiveProcess = 0x8'u32
      jobObjectLimitProcessTime = 0x2'u32
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
    proc queryInformationJobObjectR(job: Handle; cls: int32; info: pointer;
                                    size: uint32; got: ptr uint32): int32
      {.importc: "QueryInformationJobObject", stdcall, dynlib: "kernel32".}
    proc resumeThreadR(thread: Handle): uint32
      {.importc: "ResumeThread", stdcall, dynlib: "kernel32".}
    proc getCurrentProcessR(): Handle
      {.importc: "GetCurrentProcess", stdcall, dynlib: "kernel32".}
    proc localFreeR(p: pointer): pointer
      {.importc: "LocalFree", stdcall, dynlib: "kernel32".}
    proc openProcessTokenR(process: Handle; access: uint32; token: ptr Handle):
        int32 {.importc: "OpenProcessToken", stdcall, dynlib: "advapi32".}
    proc getTokenInformationR(token: Handle; cls: int32; info: pointer;
                              size: uint32; got: ptr uint32): int32
      {.importc: "GetTokenInformation", stdcall, dynlib: "advapi32".}
    proc convertSidToStringSidW(sid: pointer; str: ptr WideCString): int32
      {.importc: "ConvertSidToStringSidW", stdcall, dynlib: "advapi32".}
    proc convertStringSdToSdW(sddl: WideCString; revision: uint32;
                              sd: ptr pointer; size: ptr uint32): int32
      {.importc: "ConvertStringSecurityDescriptorToSecurityDescriptorW",
        stdcall, dynlib: "advapi32".}
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

    proc ownerOnlySddl(): string =
      ## RFC-0016 INT-29 (R2-23). A protected DACL granting this process's
      ## user, and no one else, full access, inherited by what is created in
      ## the directory: "" when the user cannot be read.
      const tokenQuery = 0x8'u32
      const tokenUserClass = 1'i32
      var token: Handle
      if openProcessTokenR(getCurrentProcessR(), tokenQuery, addr token) == 0:
        return ""
      var buf: array[256, byte]
      var got: uint32
      let ok = getTokenInformationR(token, tokenUserClass, addr buf[0],
                                    uint32(buf.len), addr got)
      discard closeHandle(token)
      if ok == 0: return ""
      # TOKEN_USER: its first field is the user's SID.
      let sid = cast[ptr pointer](addr buf[0])[]
      var str: WideCString
      if convertSidToStringSidW(sid, addr str) == 0: return ""
      let sidText = $str
      discard localFreeR(cast[pointer](str))
      "D:P(A;OICI;FA;;;" & sidText & ")"

    proc replayPrivateDir*(): string =
      ## A directory of this host's own, by a name no one can guess, which
      ## `CreateDirectoryW` refuses to reuse. "" when none could be made.
      ## RFC-0016 INT-29 (R2-23): its DACL is this user's alone and protected,
      ## so it does not inherit what the temporary directory grants others;
      ## the files the host creates in it inherit it.
      var r: array[16, byte]
      if not urandom(r): return ""
      let sddl = ownerOnlySddl()
      if sddl.len == 0: return ""
      var sd: pointer
      if convertStringSdToSdW(newWideCString(sddl), 1, addr sd, nil) == 0:
        return ""
      var sa = SECURITY_ATTRIBUTES(nLength: int32(sizeof(SECURITY_ATTRIBUTES)),
                                   lpSecurityDescriptor: sd,
                                   bInheritHandle: 0)
      let dir = getTempDir() / ("nelli-replay-" & toHexString(r))
      let made = createDirectoryWR(newWideCString(dir), addr sa)
      discard localFreeR(sd)
      if made == 0: return ""
      dir

    proc replayLimitsHeld*(): ReplayLimits =
      ## RFC-0016 INT-28. The limits of the job this process runs in.
      result = ReplayLimits(memory: -1, cpuSeconds: -1, fileSize: -1,
                            processes: -1)
      var lim: JobExtendedLimits
      if queryInformationJobObjectR(Handle(0),
                                    jobObjectExtendedLimitInformation,
                                    addr lim, uint32(sizeof(lim)), nil) == 0:
        return
      let f = lim.basic.limitFlags
      if (f and jobObjectLimitProcessMemory) != 0:
        result.memory = int64(lim.processMemoryLimit)
      if (f and jobObjectLimitActiveProcess) != 0:
        result.processes = int64(lim.basic.activeProcessLimit)
      if (f and jobObjectLimitProcessTime) != 0:
        result.cpuSeconds = lim.basic.perProcessUserTime div 10_000_000

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

    type ReexecRun = ref object of PendingChild
      ## RFC-0016 INT-32 (item 8). A re-executed child being watched.
      timeoutMs: int
      start: MonoTime
      dir, input, outName: string
      output: OutHandle
      c: ReplayChild
      lost: bool      # it ended, and how is not known
      flooded: bool   # its report grew past `replayReportCap`; killed
      killed: bool    # it ran past `timeoutMs`; killed
      ended: bool
      process, job: Handle

    proc spawnChild(p: ReexecRun; spec: string): bool =
      ## False: no child ran (`p.c.why`).
      template c: untyped = p.c
      let job = createJobObjectW(nil, nil)
      if job == Handle(0):
        c.why = "a job object could not be created for the replay's child"
        return false
      var lim: JobExtendedLimits
      lim.basic.limitFlags = jobObjectLimitProcessMemory or
                             jobObjectLimitKillOnJobClose or
                             jobObjectLimitDieOnUnhandledException or
                             jobObjectLimitActiveProcess
      lim.processMemoryLimit = uint(replayMemoryLimit)
      # RFC-0016 INT-28 (R1-31): the child and what the SUT starts, which
      # the job holds (no breakaway) and kills when it is closed.
      lim.basic.activeProcessLimit = uint32(replayProcessLimit + 1)
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
      # RFC-0016 INT-28 (R1-32): a child left suspended would run into the
      # bound, or, with none, hold the host forever.
      if resumeThreadR(pi.hThread) == high(uint32):
        let rerr = getLastError()
        discard terminateJobObject(job, 1)
        discard closeHandle(pi.hThread)
        discard closeHandle(pi.hProcess)
        discard closeHandle(job)
        c.why = "the replay's child could not be resumed (error " & $rerr & ")"
        return false
      discard closeHandle(pi.hThread)
      countExecution()
      p.process = pi.hProcess
      p.job = job
      p.start = getMonoTime()
      true

    proc watching(p: ReexecRun): bool =
      not (p.ended or p.killed or p.lost or p.flooded)

    proc childStep(p: ReexecRun; slice: int) =
      ## One wait of at most `slice` ms, so the report's size is watched and
      ## no bound wraps an `int32`.
      var wait = int32(clamp(slice, 0, 50))
      if p.timeoutMs > 0:
        let left = p.timeoutMs - (getMonoTime() - p.start).inMilliseconds
        if left <= 0:
          p.killed = true
          return
        wait = int32(min(left, int64(wait)))
      let w = waitForSingleObject(p.process, wait)
      if w == waitObject0:
        p.ended = true
      elif w != waitTimeoutResult:
        p.lost = true   # WAIT_FAILED: what it does is not known
      elif outputSize(p.output) > replayReportCap:
        p.flooded = true

    proc childKill(p: ReexecRun) =
      discard terminateJobObject(p.job, 1)
      discard closeHandle(p.process)
      discard closeHandle(p.job)   # kills whatever the SUT started

    proc childEnd(p: ReexecRun) =
      if p.ended:
        var code: int32
        if getExitCodeProcess(p.process, code) == 0:
          p.lost = true
        else:
          let ucode = cast[uint32](code)
          if ucode >= 0xC0000000'u32:
            p.c.ending = reSignalled
            p.c.code = int(ucode)
          else:
            p.c.ending = reExited
            p.c.code = int(ucode)
      elif p.killed:
        p.c.ending = reTimedOut
      p.childKill()


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

    const fiberSafe = defined(gcArc) or defined(gcOrc) or defined(gcAtomicArc)
      ## RFC-0016 INT-30 (R2-28). A tracing collector (refc, mark-and-sweep,
      ## Boehm) scans the thread's stack from where it runs to the bottom it
      ## recorded at the thread's start: run on a fiber's stack, elsewhere in
      ## memory, that scan spans whatever lies between the two, and misses
      ## the references on the fiber's own. ARC and ORC scan no stack. So
      ## only they run the SUT on a fiber; the others run it on the thread.

    proc runOnStack(stack: int; body: proc () {.closure.}) =
      ## `body` on a fiber whose stack reserve is the calling thread's size in
      ## the host. `body` catches what it raises.
      if stack <= 0 or not fiberSafe:
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
    proc c_exit_now(code: cint) {.importc: "_exit", header: "<unistd.h>".}
    var oNoFollow {.importc: "O_NOFOLLOW", header: "<fcntl.h>".}: cint

    type OutHandle = cint
    const noOut = cint(-1)

    proc replayPrivateDir*(): string =
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

    type ReexecRun = ref object of PendingChild
      ## RFC-0016 INT-32 (item 8). A re-executed child being watched.
      timeoutMs: int
      start: MonoTime
      dir, input, outName: string
      output: OutHandle
      c: ReplayChild
      lost: bool      # it ended, and how is not known
      flooded: bool   # its report grew past `replayReportCap`; killed
      killed: bool    # it ran past `timeoutMs`; killed
      ended: bool     # ended, not yet waited for: its group is ours
      gone: bool      # no longer the host's child: its status is lost
      pid: Pid
      cpuSeconds: int
      nap: int

    proc spawnChild(p: ReexecRun; spec: string): bool =
      ## As the Windows one. The child leads a process group of its own, and
      ## is signalled, it and its group, only while it is not yet waited for:
      ## until then its pid cannot name another process (R1-19). RFC-0016
      ## INT-28 (R1-24): that holds when it ended by itself too, so what the
      ## SUT started is killed then as well.
      # RFC-0016 INT-28 (R1-32): on Linux the running image itself, which
      # `exec` reaches when its file was deleted or replaced since it started
      # (`getAppFilename` then names " (deleted)", or another program).
      let exe = when defined(linux): "/proc/self/exe" else: getAppFilename()
      let args = allocCStringArray([getAppFilename()])
      let envp = allocCStringArray(childEnvironment(spec))
      let cpuSeconds = cpuBound(p.timeoutMs)
      let processes = processBound()
      let hostPid = getpid()
      let pid = fork()
      if pid < 0:
        let err = errno
        deallocCStringArray(args)
        deallocCStringArray(envp)
        p.c.why = "fork failed (errno " & $err & ")"
        return false
      if pid == 0:
        enterGroup(hostPid)
        limitChild(cpuSeconds, processes)
        let null = open("/dev/null", O_RDWR)
        if null >= 0:
          discard dup2(null, 0)
          discard dup2(null, 1)
          discard dup2(null, 2)
        closeFrom(3)
        discard execve(exe.cstring, args, envp)
        # The witness is not taken: the host reads that as no run
        # (`runReplayReexec`), whatever this status says.
        c_exit_now(127)
      deallocCStringArray(args)
      deallocCStringArray(envp)
      discard setpgid(pid, pid)   # either side may run first
      countExecution()
      p.pid = pid
      p.cpuSeconds = cpuSeconds
      p.nap = 1
      p.start = getMonoTime()
      true

    proc watching(p: ReexecRun): bool =
      not (p.ended or p.gone or p.killed or p.flooded)

    proc probe(p: ReexecRun) =
      let e = hasEnded(p.pid)
      if e == 1: p.ended = true
      elif e < 0: p.gone = true
      elif outputSize(p.output) > replayReportCap: p.flooded = true
      elif p.timeoutMs > 0 and
           (getMonoTime() - p.start).inMilliseconds >= p.timeoutMs:
        p.killed = true

    proc childStep(p: ReexecRun; slice: int) =
      ## One wait of at most `slice` ms (and of at most the next nap: the
      ## naps grow from 1 ms to 20 ms, so a short run is seen soon).
      p.probe()
      if not p.watching: return
      var wait = int64(min(p.nap, max(slice, 0)))
      if p.timeoutMs > 0:
        wait = min(wait, p.timeoutMs - (getMonoTime() - p.start).inMilliseconds)
      if wait > 0: discard usleep(cuint(wait) * 1000)
      p.nap = min(p.nap * 2, 20)
      p.probe()

    proc childKill(p: ReexecRun) =
      ## Its group killed and the child waited for, unless it is no longer
      ## the host's.
      var status: cint
      if not p.gone:
        killGroup(p.pid)
        while true:
          let w = waitpid(p.pid, status, 0)
          if w == p.pid: break
          if w < 0 and errno == EINTR: continue
          break

    proc childEnd(p: ReexecRun) =
      var status: cint
      var haveStatus = false
      if not p.gone:
        killGroup(p.pid)
        while true:
          let w = waitpid(p.pid, status, 0)
          if w == p.pid:
            haveStatus = true
            break
          if w < 0 and errno == EINTR: continue
          break
      let limit = if haveStatus: limitEnding(status, p.cpuSeconds) else: ""
      if p.flooded:
        discard
      elif p.killed:
        p.c.ending = reTimedOut
      elif limit.len > 0:
        p.c.ending = reTimedOut
        p.c.why = limit
      elif haveStatus and WIFSIGNALED(status):
        p.c.ending = reSignalled
        p.c.code = int(WTERMSIG(status))
      elif haveStatus and WIFEXITED(status):
        p.c.ending = reExited
        p.c.code = int(WEXITSTATUS(status))
      else:
        p.lost = true


    proc callerStackSize*(): int = 0

    proc runOnStack(stack: int; body: proc () {.closure.}) = body()

    proc quietChild() =
      # As the fork path: the verdict reads the signal, not Nim's trace.
      for s in [SIGSEGV, SIGBUS, SIGILL, SIGFPE, SIGABRT]:
        var sa: Sigaction
        sa.sa_handler = SIG_DFL
        discard sigaction(s, sa, nil)
      # Relative to this image, as the fork path's (RFC-0016 INT-28); the
      # other limits were set before the `exec`.
      limitMemory()

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

  proc readHostHooks*(r: var WireReader) =
    ## RFC-0016 INT-13. The child's half of `putHostHooks`, in its order. The
    ## child's own `outOfMemHook` stays installed and the host's runs after it
    ## (`hostOomHookR`).
    template get(h: untyped) =
      when declared(h):
        r.wireGet(h)
    get globalRaiseHook
    get localRaiseHook
    r.wireGet(hostOomHookR)
    get unhandledExceptionHook
    get onUnhandledException
    get errorMessageWriter

  proc childOut(b: char) {.nimcall, gcsafe.} =
    {.cast(gcsafe).}:
      if childOutput != nil:
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

  proc cleanUp(p: ReexecRun) =
    if p.output != noOut:
      closeOutput(p.output)
      p.output = noOut
    removeQuietly(p.input)
    removeQuietly(p.outName)
    try: removeDir(p.dir)
    except CatchableError: discard

  proc reexecFinish(p: ReexecRun) =
    ## What the child reported, once it is no longer watched.
    p.childEnd()
    p.done = true
    var rd: ReportReader
    rd.feed(readOutput(p.output, replayReportCap + 1))
    var c = p.c
    if p.flooded or rd.corrupt:
      p.res = stopped("")
    elif rd.total == 0 and c.ending != reTimedOut and fileExists(p.input):
      # RFC-0016 INT-29 (R2-21, R2-22). The child ended without taking its
      # witness: the program could not be started (a failed `execve` ends
      # its fork with 127), or it could not open its report, or no site of
      # it took the marker. The SUT did not run, so this is no crash of it.
      p.res = refused("the re-executed child ended before it took its " &
                      "witness (" & describe(c) & "), so the SUT did not run")
    else:
      c.reached = rd.reached
      c.outOfMemory = rd.outOfMemory and c.ending != reTimedOut
      if rd.finished and c.ending != reTimedOut:
        readFlags(rd.flags, c)
        c.ending = reFinished
      elif rd.unreadable:
        c.ending = reRefused
        c.why = "the child could not read the witness"
        c.runDependent = true
      elif p.lost:
        c = statusLost(c)
      p.res = settled(c)
    p.cleanUp()

  proc reexecStep(p: ReexecRun; slice: int) =
    if p.watching: p.childStep(slice)
    if not p.watching: p.reexecFinish()

  proc reexecStop(p: ReexecRun) =
    p.childKill()
    p.cleanUp()
    p.done = true

  proc startReplayReexec*(site, payload: string; timeoutMs: int): PendingChild =
    ## RFC-0005 S8ct. The host's half: `payload` to a re-executed copy of this
    ## program, which the initialiser at call site `site` picks up
    ## (`replayChildEntry`), and what it reported. RFC-0016 INT-32 (item 8):
    ## started, not waited for (`stepChild`, `awaitChild`).
    if inReplayChild():
      return readyChild(refused("a replay's child does not start another"))
    var r: array[16, byte]
    if not urandom(r):
      return readyChild(
        refused("no random bytes for the replay's private directory"))
    let nonce = toHexString(r)
    let dir = replayPrivateDir()
    if dir.len == 0:
      return readyChild(refused("a private directory could not be created " &
                                "for the replay's child"))
    let p = ReexecRun(timeoutMs: timeoutMs, dir: dir, input: dir / "in",
                      outName: dir / "out", output: noOut,
                      c: ReplayChild(ending: reSignalled))
    if not writeNew(p.input, witnessFile(nonce, site, payload)):
      p.cleanUp()
      return readyChild(refused("the replay's witness could not be written"))
    p.output = openNewOutput(p.outName)
    if p.output == noOut:
      p.cleanUp()
      return readyChild(
        refused("the replay's report file could not be created"))
    flushFile(stdout)
    flushFile(stderr)
    if not p.spawnChild(nonce & "|" & dir):
      p.cleanUp()
      return readyChild(refused(p.c.why))
    p


  proc replayChildEntry*(site: string;
                         run: proc (payload: string): ReplayReport {.nimcall.}):
                           bool =
    ## RFC-0005 S8ct. The child's half, from a `{.global.}` initialiser at each
    ## call site: returns at once except in the child of this very site, which
    ## runs the SUT and ends.
    let role = childRole()
    if role.site.len == 0 or role.site != site: return false
    quietChild()
    # RFC-0016 INT-29 (R2-22). The report first: a child that cannot write
    # one ends here, its witness not taken (`in` left), which the host reads
    # as no run. Before, the SUT ran and its ending was written to nil.
    try:
      childOutput = open(role.output, fmWrite)
    except CatchableError:
      endChild(124)
    try: removeFile(role.input)
    except CatchableError: discard
    hostOomHookR = outOfMemHook
    outOfMemHook = childOomR
    var rep: ReplayReport
    var failed = false
    try:
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

# ---- watching a started child ---------------------------------------------------

proc stepChild*(p: PendingChild; slice: int) =
  ## RFC-0016 INT-32 (item 8). Waits on `p` for at most `slice` ms; once its
  ## ending is known (it reported, ended, or ran past its bound and was
  ## killed), `childDone`.
  if p.done: return
  when replayForks:
    forkStep(ForkRun(p), slice)
  elif replayReexecs:
    reexecStep(ReexecRun(p), slice)

proc stopChild*(p: PendingChild) =
  ## RFC-0016 INT-32 (item 8). Kills `p`, and what its SUT started, when its
  ## ending will not be read; it is then `childDone` with no ending.
  if p.done: return
  when replayForks:
    forkStop(ForkRun(p))
  elif replayReexecs:
    reexecStop(ReexecRun(p))
  p.res = refused("stopped by the host: its ending is not read")

proc awaitChild*(p: PendingChild): ReplayChild =
  ## RFC-0016 INT-32 (item 8). `p` waited out.
  while not p.done: stepChild(p, 50)
  p.res

when replayForks:
  proc runReplayForked*(body: proc (): ReplayReport {.closure, gcsafe.};
                        timeoutMs: int): ReplayChild =
    ## RFC-0005 S8ct. `startReplayForked`, waited out.
    awaitChild(startReplayForked(body, timeoutMs))

when replayReexecs:
  proc runReplayReexec*(site, payload: string; timeoutMs: int): ReplayChild =
    ## RFC-0005 S8ct. `startReplayReexec`, waited out.
    awaitChild(startReplayReexec(site, payload, timeoutMs))
