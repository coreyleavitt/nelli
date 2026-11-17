## RFC-0016 S8ck-r (INF-04): the per-thread state release registry.
##
## nelli keeps its walker, lowering, cache and engine state in
## `{.threadvar.}`s. Nim never destroys a threadvar when its thread exits
## (stock and patched Nim 2.2.10, a `createThread` thread and a foreign
## thread alike; tests/asan/nim_threadvar_exit_leak.nim), so whatever that
## state holds when a thread ends is leaked: a `symexFind` on a raw pthread
## left about 100 KB behind under LeakSanitizer
## (tsymex_rfc0005_s8cb_replay).
##
## The fix is a release, not a suppression. Every module that declares a
## threadvar registers, at module init, one proc that sets each of its
## threadvars back to `default` (`releaseToDefault`). `releaseSymexThreadState`
## runs every registered proc and then a cycle collection, which also frees
## the ORC root buffer of the calling thread. The default IS the state a
## fresh thread starts in (a threadvar cannot have an initializer), so every
## lazily built cache is rebuilt on the next use and a later run on the same
## thread behaves exactly as on a new thread.
##
## Who calls it:
##   * a thread Nim created (`createThread`): nobody. The first symex run on a
##     thread arms `onThreadDestruction` (`armThreadStateRelease`), and the
##     release runs when the thread proc returns.
##   * a foreign thread (one Nim did not create: a raw pthread, a thread of a
##     host program calling into a Nim library): its owner MUST call
##     `releaseSymexThreadState()` before the thread exits. Nim runs no
##     destruction handler on a thread it did not create.
##   * any thread that is done with nelli and keeps running may call it to
##     give the memory back. Never call it while a run is in progress on the
##     calling thread (from inside a property or a symex target).
##
## A threadvar that must survive a release (it records something the release
## does not undo) carries the reviewed marker
## `[thread-state: kept -- <reason>]` on its declaration line instead.
## tsymex_0016_s8ckr_threadstate_audit checks that every threadvar under
## src/nelli is named by a `releaseToDefault` in its own module, or carries
## that marker, and that every module with a `releaseToDefault` registers it.
##
## Z3-free and a leaf: `import nelli` and the engine use it as well.

import std/macros

type ThreadStateRelease* = proc () {.nimcall, gcsafe, raises: [].}
  ## One module's release: sets each of its threadvars to `default`.

const maxThreadStateReleases = 64

var
  threadStateReleases: array[maxThreadStateReleases, ThreadStateRelease]
    ## Plain globals, not threadvars: written only by module init (on the
    ## main thread, before any other thread can run nelli code), read by
    ## every thread's release.
  threadStateReleaseCount: int

proc registerThreadStateRelease*(p: ThreadStateRelease) =
  ## Adds `p` to the procs `releaseSymexThreadState` runs. Call it at module
  ## top level, after the module's last threadvar declaration and its
  ## release proc, so it runs once, at module init.
  doAssert threadStateReleaseCount < maxThreadStateReleases,
    "thread_state: more than " & $maxThreadStateReleases & " release procs"
  threadStateReleases[threadStateReleaseCount] = p
  inc threadStateReleaseCount

macro releaseToDefault*(vars: varargs[untyped]): untyped =
  ## `v = default(typeof(v))` for each named threadvar. The audit reads the
  ## names given here, so list them by plain name.
  result = newStmtList()
  for v in vars:
    result.add quote do:
      `v` = default(typeof(`v`))

proc releaseSymexThreadState*() {.gcsafe, raises: [].} =
  ## Gives back every piece of nelli's per-thread state on the calling
  ## thread: each registered module release, then a cycle collection (the
  ## released IR and walker graphs are cyclic, and the collection also frees
  ## this thread's ORC root buffer once it is empty). Safe to call any number
  ## of times; a later run on the same thread rebuilds what it needs. A
  ## foreign thread must call it before it exits (see the module doc).
  {.cast(gcsafe).}:
    for i in 0 ..< threadStateReleaseCount:
      threadStateReleases[i]()
  when defined(gcOrc):
    GC_runOrc()

var threadStateArmed {.threadvar.}: bool  # [thread-state: kept -- records that this thread's onThreadDestruction hook is registered; the hook outlives a release, so clearing the flag would register it twice]

proc releaseAtThreadExit() {.gcsafe, raises: [].} =
  releaseSymexThreadState()
  when declared(nimThreadDestructionHandlers):
    # Nim's own handler list is a threadvar too, and is never freed. When
    # this hook is its first entry it is the last one `afterThreadRuns`
    # calls (it iterates down to index 0), so the list can be dropped here.
    if nimThreadDestructionHandlers.len > 0 and
       rawProc(nimThreadDestructionHandlers[0]) ==
         cast[pointer](releaseAtThreadExit):
      nimThreadDestructionHandlers = @[]

proc armThreadStateRelease*() =
  ## Registers `releaseSymexThreadState` to run when the calling thread exits,
  ## once per thread. Has an effect only on a thread Nim created; on the main
  ## thread and a foreign thread no handler ever runs (the main thread's
  ## state is reachable until exit; a foreign thread's owner releases it).
  when compileOption("threads"):
    if not threadStateArmed:
      threadStateArmed = true
      onThreadDestruction(releaseAtThreadExit)
