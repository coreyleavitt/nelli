## CR4-M1: under `processIsolation` the property runs in a child process, and
## the symex DB errors and findings it makes cross the pipe in the result
## frame, onto `FuzzReport.dbErrors` and `isolatedSymexFindings`. Exactly ONE
## `fuzz(...)` call site, first in the file (see tests/tfuzzprocessisolation.nim).
import std/[unittest, strutils, os]
import nelli
import nelli/symex
import nelli/engine/frame

disableParamFiltering()

proc childErrorProp(n: int) {.cover.} =
  recordSymexDbError("child-pid=" & $getCurrentProcessId())
  recordSymexFinding(FindingOrigin(site: "f.nim(1, 1)", fnId: "f"),
                     SymexFinding(targetDesc: "label(\"t\")", status: sfSat))

suite "CR4-M1: an isolated campaign reports its child's symex DB errors":
  test "errors and findings made in the child reach the parent's report":
    discard consumeSymexDbErrors()
    let rep = fuzz(integers(-50, 50), childErrorProp,
                   FuzzSettings(maxIterations: 4, seed: 1,
                                executor: ExecutorConfig(processIsolation: true)))
    check rep.iterations == 4
    check rep.dbErrors.len >= 1
    let own = "child-pid=" & $getCurrentProcessId()
    for e in rep.dbErrors:
      check e.startsWith("child-pid=")
      check e != own
    check rep.isolatedSymexFindings >= 1
    check rep.droppedSymexDbErrors == 0
    check consumeSymexDbErrors().len == 0
