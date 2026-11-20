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
import std/[unittest, strutils, json]
import nelli
import nelli/symex
import nelli/db
import nelli/engine/frame
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

proc i34Sut(x: int) =
  if x == 42: symexTarget("alpha")

proc failingCache(): ExampleDatabase =
  ## A cache whose writes raise `DbError`: the symex witness save fails.
  readOnlyDatabase(inMemoryDatabase())

proc recordOnWorker() {.thread.} =
  recordSymexDbError("worker")

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

  test "symexForAll's layer 1 errors are on that run's report":
    discard consumeSymexDbErrors()
    let r = symexForAll(integers(0, 100), i34Sut, failingCache(),
                        forAllSettings = quiet())
    checkpoint $r.dbErrors
    check r.dbErrors.len > 0
    check consumeSymexDbErrors().len == 0

  test "layer 1 errors are not stolen from, or given to, an enclosing run":
    discard consumeSymexDbErrors()
    var inner: Report[int]
    var made = false
    let outer = forAll(integers(0, 0), proc(x: int) =
                         if not made:
                           made = true
                           recordSymexDbError("outer")
                           inner = symexForAll(integers(0, 100), i34Sut,
                                               failingCache(),
                                               forAllSettings = quiet()),
                       quiet())
    check inner.dbErrors.len > 0
    check "outer" notin inner.dbErrors
    # The enclosing run keeps its own, and the nested run's reach it as well.
    check outer.dbErrors[0] == "outer"
    check outer.dbErrors[1 .. ^1] == inner.dbErrors
    check consumeSymexDbErrors().len == 0

  test "strictDb ends a run with symex DB errors in a report":
    let ok = forAll(integers(0, 0), proc(x: int) = discard,
                    Settings(maxExamples: 1, seed: 1, strictDb: true))
    check ok.outcome == otPassed
    var made = false
    let r = forAll(integers(0, 0), proc(x: int) =
                     if not made:
                       made = true
                       recordSymexDbError("cache write failed"),
                   Settings(maxExamples: 1, seed: 1, flakyRetries: 0,
                            maxShrinks: 1, maxRejections: 1, strictDb: true))
    check r.outcome == otFalsified
    check "DB: " in r.message and "cache write failed" in r.message
    check r.dbErrors == @["cache write failed"]
    # Layer 1's errors too (symexForAll), by the same rule.
    let s = symexForAll(integers(0, 100), i34Sut, failingCache(),
                        forAllSettings = Settings(
                          maxExamples: 1, seed: 1, flakyRetries: 0,
                          maxShrinks: 1, maxRejections: 1, strictDb: true))
    check s.outcome == otFalsified
    check "DB: " in s.message

  test "an error made on a thread the property started is counted and shown":
    discard consumeSymexDbErrors()
    let before = droppedSymexDbErrors()
    let rep = forAll(integers(0, 0), proc(x: int) =
      var th: Thread[void]
      createThread(th, recordOnWorker)
      joinThread(th), quiet())
    check droppedSymexDbErrors() == before + 1
    check rep.droppedSymexDbErrors == 1
    check "worker" notin rep.dbErrors
    check "1 symex DB error was dropped" in renderReport(rep, ofText)
    let j = parseJson(renderReport(rep, ofJson))
    check j.hasKey("droppedSymexDbErrors")
    check "1 symex DB error was dropped" in renderReport(rep, ofJunit)
    check "symex db errors dropped" in renderReport(rep, ofGithubAnnotation)
    # A standalone call on the main thread is the caller's, not a drop.
    recordSymexDbError("mine")
    check droppedSymexDbErrors() == before + 1
    check consumeSymexDbErrors() == @["mine"]
    check renderReport(forAll(integers(0, 0), proc(x: int) = discard, quiet()),
                       ofText).count("dropped") == 0

  test "the run-scoped error contract holds":
    pinNever(cellKey(axConstruct, "report/dberrors/run-scoped"), held,
      "a symex DB error is on the report of the run that made it: one made " &
      "outside any run is never on the next run's, a nested run reports its " &
      "own errors and its enclosing run both, and runs on two threads keep " &
      "theirs apart")
