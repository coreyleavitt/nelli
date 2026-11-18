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
##
## It reads no build option (RFC-0016 K5a: those reads live in
## `buildprofile.nim` only), and it cannot import `buildprofile`: that module
## imports `pcre_engine`, which imports this one, so the import would be a
## cycle. It needs none: whether the build has threads is whether system.nim
## declares the thread-exit API (`onThreadDestruction`,
## `nimThreadDestructionHandlers`; system includes `threadimpl` only when
## `hasThreadSupport`), and that symbol is what the code below calls. A
## `when declared(...)` on it is the exact compile guard the call needs.

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

var threadStateArmed {.threadvar.}: bool  # [thread-state: kept -- records whether this thread's onThreadDestruction hook is registered; only disarmThreadStateRelease, which removes the hook, clears it]

proc releaseSymexThreadState*() {.gcsafe, raises: [].}

proc releaseAtThreadExit() {.gcsafe, raises: [].} =
  releaseSymexThreadState()

proc disarmThreadStateRelease() {.gcsafe, raises: [].} =
  ## Takes this thread's exit hook back out of Nim's handler list. Nim's list
  ## is a threadvar too and is never freed, and on a foreign thread no
  ## handler in it ever runs: a run there armed the hook and so allocated
  ## the list (24 bytes, tsymex_rfc0005_s8cb_replay under LeakSanitizer).
  ## The release this precedes leaves the thread in its fresh state, so it
  ## needs no hook until a later run arms it again. Called from the hook
  ## itself, the removal is safe: `afterThreadRuns` walks the list down to
  ## index 0, and deleting entry `i` moves only entries it has already run.
  when declared(nimThreadDestructionHandlers):
    if threadStateArmed:
      threadStateArmed = false
      {.cast(gcsafe).}:
        for i in countdown(nimThreadDestructionHandlers.len - 1, 0):
          if rawProc(nimThreadDestructionHandlers[i]) ==
             cast[pointer](releaseAtThreadExit):
            nimThreadDestructionHandlers.delete(i)
            break
        if nimThreadDestructionHandlers.len == 0:
          nimThreadDestructionHandlers = @[]  # frees the payload

proc releaseSymexThreadState*() {.gcsafe, raises: [].} =
  ## Gives back every piece of nelli's per-thread state on the calling
  ## thread: this thread's exit hook, each registered module release, then a
  ## cycle collection (the released IR and walker graphs are cyclic, and the
  ## collection also frees this thread's ORC root buffer once it is empty).
  ## Safe to call any number of times; a later run on the same thread
  ## rebuilds what it needs and re-arms the hook. A foreign thread must call
  ## it before it exits (see the module doc).
  disarmThreadStateRelease()
  {.cast(gcsafe).}:
    for i in 0 ..< threadStateReleaseCount:
      threadStateReleases[i]()
  when defined(gcOrc):
    GC_runOrc()

proc armThreadStateRelease*() =
  ## Registers `releaseSymexThreadState` to run when the calling thread exits,
  ## once per arming (a release disarms). Runs only on a thread Nim created;
  ## on the main thread and a foreign thread no handler ever runs (the main
  ## thread's state is reachable until exit; a foreign thread's owner
  ## releases it, which also takes the hook back out).
  when declared(onThreadDestruction):
    if not threadStateArmed:
      threadStateArmed = true
      onThreadDestruction(releaseAtThreadExit)
