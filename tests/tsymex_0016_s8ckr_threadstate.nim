## RFC-0016 S8ck-r (INF-04). nelli's per-thread state can be released.
##
## Nim never destroys a threadvar when its thread exits
## (tests/asan/nim_threadvar_exit_leak.nim), so before S8ck-r everything
## nelli's walker kept in threadvars leaked with each thread that ran it.
## `releaseSymexThreadState` (src/nelli/thread_state.nim) runs every module's
## registered release; a symex run arms it for the exit of a thread Nim
## created; a foreign thread calls it itself
## (tsymex_rfc0005_s8cb_replay's raw pthread). Under LeakSanitizer
## (scripts/asan-slice.sh) this file and s8cb_replay are leak-clean.
##
## Pinned:
##   * the registry runs a registered release on `releaseSymexThreadState`;
##   * a symex run on a `createThread` thread arms the release for that
##     thread's exit, and it runs exactly once there;
##   * a release does not break a later run on the same thread, the main
##     thread or a Nim thread: the second run finds the same witness.
import std/[unittest, atomics]
import nelli/symex
import nelli/thread_state

proc sut(x, y: int) =
  if x > 1 and y > 1 and x < 2000 and y < 2000 and x * y == 1022117:
    symexTarget("s8ckr_ts")

var releases: Atomic[int]

proc countRelease() {.nimcall, gcsafe, raises: [].} =
  releases.atomicInc

registerThreadStateRelease(countRelease)

type Probe = tuple[first, second: SymexStatusKind, armedRuns: int]
var probe: Probe

proc runTwiceOnThread() {.thread.} =
  {.cast(gcsafe).}:
    probe.first = symexFind(sut, tLabel("s8ckr_ts")).status
    let before = releases.load
    releaseSymexThreadState()
    probe.armedRuns = releases.load - before
    probe.second = symexFind(sut, tLabel("s8ckr_ts")).status

proc runOnceOnThread() {.thread.} =
  {.cast(gcsafe).}:
    probe.first = symexFind(sut, tLabel("s8ckr_ts")).status

suite "S8ck-r: per-thread state release":

  test "releaseSymexThreadState runs every registered release":
    let before = releases.load
    releaseSymexThreadState()
    check releases.load == before + 1

  test "a release does not break a later run on the main thread":
    check symexFind(sut, tLabel("s8ckr_ts")).status == sxSat
    releaseSymexThreadState()
    check symexFind(sut, tLabel("s8ckr_ts")).status == sxSat
    releaseSymexThreadState()

  test "a symex run on a Nim thread releases its state when the thread exits":
    let before = releases.load
    var th: Thread[void]
    createThread(th, runOnceOnThread)
    joinThread(th)
    check probe.first == sxSat
    check releases.load == before + 1

  test "a release does not break a later run on a Nim thread":
    let before = releases.load
    var th: Thread[void]
    createThread(th, runTwiceOnThread)
    joinThread(th)
    check probe.first == sxSat
    check probe.armedRuns == 1
    check probe.second == sxSat
    # once mid-thread, once at its exit
    check releases.load == before + 2
