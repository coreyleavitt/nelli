## RFC-fuzzer-nextgen E3a (C4): fork-per-input recycling's captured-once
## snapshot invariant.
##
## This is the ONE process-spawning test the RFC sanctions for this slice
## (everything else in tests/tfuzzreverify.nim is pure algebra over fakes).
## It is still DETERMINISTIC, not a race: every `submit` forks, is read to
## completion, and is reaped before the next `submit` starts — sequential,
## bounded, no timing dependency. Acceptable under `dt-bounded.sh`.
##
## The claim under test: `newForkWorker` always forks from THIS SAME,
## unchanged parent process — never from a previously-forked child — so N
## children in a row are STATE-IDENTICAL (a probe that WOULD differ if state
## leaked between forks, or if a fork were accidentally chained off a prior
## child instead of the pristine parent, stays constant across all N).

import std/[unittest, options]
import nelli

when defined(posix):
  import std/[posix, os]

  # A module-global the dispatch closure reads and mutates. Because
  # `newForkWorker` never runs `dispatch` in the PARENT — only inside a
  # freshly forked (COW) child — any mutation `dispatch` makes is confined
  # to that child's own copy of this process's memory and is invisible to
  # the parent and to every SUBSEQUENT fork. If forking were instead chained
  # off a previously-forked child (state leaking between "generations"),
  # this counter would climb 0, 1, 2, 3, ... across successive `submit`
  # calls instead of staying pinned at 0 forever.
  var execCounter = 0

  proc probeDispatch(input: ChoiceSeq): Observation[void] =
    let seenBeforeThisChildTouchedIt = execCounter   # read the PARENT's pristine value
    inc execCounter                                   # mutate: visible only in THIS child
    Observation[void](verdict: vOk, message: $seenBeforeThisChildTouchedIt)

  suite "fuzz: fork-per-input captured-once snapshot invariant (RFC-fuzzer-nextgen E3a C4)":
    test "N forks from one snapshot are state-identical: every child sees execCounter == 0":
      let w = newForkWorker[void](probeDispatch)
      for i in 0 ..< 5:
        let obs = w.submit(@[])
        check obs.verdict == vOk
        check obs.message == "0"   # NEVER "1", "2", ... -- would mean a fork chained off a prior child
      # The PARENT's own copy was never touched by any child -- confirms the
      # children's mutations really were confined to their own COW copies,
      # not observed here because they ran in separate address spaces.
      check execCounter == 0

    test "newForkWorker maps a dispatch-side process death to vCrashed, not a hang or exception":
      let deadly = proc(input: ChoiceSeq): Observation[void] =
        discard kill(getpid(), SIGSEGV)
        Observation[void](verdict: vOk)   # unreached
      let w = newForkWorker[void](deadly)
      let obs = w.submit(@[])
      check obs.verdict == vCrashed
      check obs.crash.isSome
      check obs.crash.get.kind == ckSignal
      check obs.crash.get.signal == 11

    test "an Orchestrator drives a fork-per-input Worker[T] through the ordinary run/admit seam":
      var frontier = newCoverageFrontier()
      let dispatch = proc(input: ChoiceSeq): Observation[void] =
        Observation[void](verdict: vOk, message: "ok")
      let worker = newForkWorker[int](dispatch)
      let o = newOrchestrator(worker, frontier)
      let obs = o.run(@[])
      check obs.verdict == vOk
      check obs.message == "ok"

  # --- R15: the enforced fork-safety guard ------------------------------------
  #
  # `newForkWorker`'s doc comment states the hazard (fork() only carries the
  # calling thread; a lock held by a sibling thread at fork time can deadlock
  # or corrupt the child) but, before R15, nothing actually enforced it. This
  # keeps a REAL OS thread alive (via `createThread`/`{.thread.}`, not a fake)
  # across a `submit` call and asserts `assertForkSafeSingleThreaded` refuses
  # to fork while it's running -- then that a later `submit`, once that thread
  # has been joined, succeeds normally (the guard doesn't misfire on an
  # ordinary single-threaded caller, which is the shipped default's only
  # supported shape).
  var keepSpinning: bool
  proc idleThreadBody(unused: int) {.thread.} =
    while keepSpinning:
      sleep(10)

  suite "fuzz: newForkWorker's runtime thread-safety guard (RFC-fuzzer-nextgen R15)":
    test "submit raises ForkUnsafeError while another OS thread is alive":
      keepSpinning = true
      var th: Thread[int]
      createThread(th, idleThreadBody, 0)
      sleep(50)   # let the new thread actually register under /proc/self/task

      let dispatch = proc(input: ChoiceSeq): Observation[void] =
        Observation[void](verdict: vOk)
      let w = newForkWorker[void](dispatch)
      var raised = false
      try:
        discard w.submit(@[])
      except ForkUnsafeError:
        raised = true
      check raised

      keepSpinning = false
      joinThread(th)

    test "submit succeeds once this process is single-threaded again":
      # A fresh thread-safety check, independent of the test above (which
      # already joined its own thread back out) -- confirms the guard does
      # NOT misfire for the ordinary, single-threaded caller this worker is
      # actually shipped for.
      let dispatch = proc(input: ChoiceSeq): Observation[void] =
        Observation[void](verdict: vOk, message: "single-threaded-ok")
      let w = newForkWorker[void](dispatch)
      let obs = w.submit(@[])
      check obs.verdict == vOk
      check obs.message == "single-threaded-ok"
