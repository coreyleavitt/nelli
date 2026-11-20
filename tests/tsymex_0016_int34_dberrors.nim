## RFC-0016 INT-34 (0005 review R2-10): a symex DB error belongs to the run
## that made it.
##
## The errors a symex cache read or write hits inside a property used to go to
## one thread-local list (`engineSymexDbErrors`) that the next run to finish
## drained onto its report. So an error made outside any run turned up on the
## report of whichever run finished next, and a nested run's report took the
## enclosing run's errors while the enclosing report lost them. They now ride
## the run's engine frame: the run that made an error reports it, a nested
## run's errors also reach the run it is nested in (as its findings do), and
## an error made outside any run stays with its caller (`consumeSymexDbErrors`).
import std/unittest
import nelli
from nelli/smt/admission import cellKey, axConstruct
import ./s8cu_helpers

var held = true   # cleared by any test of this file that fails

template trackFailure() =
  teardown:
    if testStatusIMPL != TestStatus.OK: held = false

proc quiet(): Settings =
  Settings(maxExamples: 1, seed: 1, flakyRetries: 0, maxShrinks: 1,
           maxRejections: 1)

proc runRecording(tag: string): seq[string] =
  ## One run whose property makes one DB error tagged `tag`.
  var made = false
  let r = forAll(integers(0, 0), proc(x: int) =
                   if not made:
                     made = true
                     recordSymexDbError(tag),
                 quiet())
  r.dbErrors

suite "INT-34: a symex DB error is on the report of the run that made it":
  trackFailure()

  test "an error made outside any run is not on the next run's report":
    discard consumeSymexDbErrors()
    recordSymexDbError("stray")
    let r = forAll(integers(0, 0), proc(x: int) = discard, quiet())
    check "stray" notin r.dbErrors
    # Nor on a failing one's.
    let f = forAll(integers(0, 0), proc(x: int) =
                     raise newException(ValueError, "fails"), quiet())
    check f.outcome == otFalsified
    check "stray" notin f.dbErrors
    # It stays with the caller that made it.
    check consumeSymexDbErrors() == @["stray"]

  test "a nested run reports its own errors, and its enclosing run both":
    var inner: seq[string]
    var made = false
    let outer = forAll(integers(0, 0), proc(x: int) =
                         if not made:
                           made = true
                           recordSymexDbError("outer")
                           inner = runRecording("inner"),
                       quiet())
    check inner == @["inner"]
    check outer.dbErrors == @["outer", "inner"]
    check consumeSymexDbErrors().len == 0

  test "two runs on two threads keep their errors apart":
    var results: array[2, seq[string]]
    proc worker(i: int) {.thread.} =
      {.cast(gcsafe).}:
        results[i] = runRecording("thread" & $i)
    var ts: array[2, Thread[int]]
    for i in 0 .. 1: createThread(ts[i], worker, i)
    joinThreads(ts)
    check results[0] == @["thread0"]
    check results[1] == @["thread1"]

  test "a run's errors are not left for a later run":
    check runRecording("first") == @["first"]
    check runRecording("second") == @["second"]
    check consumeSymexDbErrors().len == 0

  test "the run-scoped error contract holds":
    pinNever(cellKey(axConstruct, "report/dberrors/run-scoped"), held,
      "a symex DB error is on the report of the run that made it: one made " &
      "outside any run is never on the next run's, a nested run reports its " &
      "own errors and its enclosing run both, and runs on two threads keep " &
      "theirs apart")
