## Wiring audit (wave 4), C-9: the fuzz report carries what `Report` does.
##
## * `FuzzReport.dbErrors`: a `DbError` from the campaign's corpus calls or
##   the orchestrator's `.bin` funnel is recorded, not raised.
## * `FuzzReport.droppedSymexFindings` and `droppedSymexDbErrors`: how far the
##   process's drop counts moved during the campaign.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/engine/frame

proc target(): Target[int] =
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](8)
    c[(x mod 8 + 8) mod 8] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

proc dropOne() {.thread.} =
  recordSymexFinding(FindingOrigin(site: "f.nim(1, 1)", fnId: "f"),
                     SymexFinding(targetDesc: "label(\"t\")", status: sfSat))
  recordSymexDbError("worker")

suite "C-9: fuzz reports database errors":
  test "the funnel records a DbError instead of raising it":
    var fr = newCoverageFrontier()
    let o = newOrchestrator(just(5), target(), fr,
                            db = readOnlyDatabase(inMemoryDatabase()))
    o.requestSave("k", @[integerChoice(1, 0, 100, 0)])
    o.requestRemove("k", @[integerChoice(1, 0, 100, 0)])
    check o.dbErrors.len == 2

  test "a campaign on a read-only corpus reports the errors and completes":
    var fr = newCoverageFrontier("dberr")
    let fs = FuzzSettings(maxIterations: 200, seed: 1, persistKey: "camp",
                          database: readOnlyDatabase(inMemoryDatabase()))
    var rep: FuzzReport
    var escaped = ""
    try:
      rep = fuzz(integers(0, 1000), target(), fr, fs)
    except DbError as e:
      escaped = e.msg
    check escaped == ""
    check rep.iterations > 0
    check rep.dbErrors.len > 0
    check "saveCorpus" in rep.dbErrors[0]

  test "a campaign on a healthy database reports none":
    var fr = newCoverageFrontier("dberr-ok")
    let rep = fuzz(integers(0, 1000), target(), fr,
                   FuzzSettings(maxIterations: 50, seed: 1,
                                persistKey: "camp",
                                database: inMemoryDatabase()))
    check rep.dbErrors.len == 0
    check rep.droppedSymexFindings == 0
    check rep.droppedSymexDbErrors == 0

suite "C-9: fuzz reports the drop counts":
  test "drops made on a thread the property starts during the campaign":
    var fr = newCoverageFrontier("drops")
    var started = false
    let t = Target[int](run: proc(x: int): Observation[int] =
      if not started:
        started = true
        var th: Thread[void]
        createThread(th, dropOne)
        joinThread(th)
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let rep = fuzz(integers(0, 10), t, fr, FuzzSettings(maxIterations: 5, seed: 1))
    check rep.droppedSymexFindings == 1
    check rep.droppedSymexDbErrors == 1

suite "CR4-M1: a campaign owns what its property executions produce":
  test "a main-thread property's symex DB error is on the report, not leaked":
    discard consumeSymexDbErrors()
    var fr = newCoverageFrontier("owned")
    let t = Target[int](run: proc(x: int): Observation[int] =
      recordSymexDbError("cache write failed: " & $x)
      recordSymexFinding(FindingOrigin(site: "f.nim(1, 1)", fnId: "f"),
                         SymexFinding(targetDesc: "label(\"t\")", status: sfSat))
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    let rep = fuzz(integers(0, 10), t, fr,
                   FuzzSettings(maxIterations: 3, seed: 1))
    check rep.dbErrors.len >= 1
    check "cache write failed" in rep.dbErrors[0]
    check consumeSymexDbErrors().len == 0
    check rep.droppedSymexDbErrors == 0
    check rep.droppedSymexFindings == 0
    check rep.symexFindings.len == 1

  test "a campaign nested in a run reaches the enclosing run too":
    discard consumeSymexDbErrors()
    var fr = newCoverageFrontier("owned-nested")
    let t = Target[int](run: proc(x: int): Observation[int] =
      recordSymexDbError("inner")
      Observation[int](verdict: vOk, coverage: Coverage(counters: @[1'u8])))
    var inner: FuzzReport
    let r = forAll(integers(0, 0), proc(x: int) =
      inner = fuzz(integers(0, 10), t, fr,
                   FuzzSettings(maxIterations: 1, seed: 1)),
      Settings(maxExamples: 1, seed: 1))
    check "inner" in inner.dbErrors
    check "inner" in r.dbErrors
