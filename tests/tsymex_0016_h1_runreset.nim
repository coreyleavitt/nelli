## RFC-0016 H1 (W-62, CI-01's remainder, CHANGELOG R1-12): the per-run reset of
## the walk's per-expression lowering threadvars is pinned.
##
## `resetSymexRunState` did not clear `pendingPtrCompares`, so a run aborted
## between a pointer comparison and its drain left Z3 terms of the freed context
## for the next run. Eight more per-expression lowering threadvars had the same
## gap. The fix shipped with "no abort shape that reaches it was constructed, so
## there is no test". An abort between a `lower` and its drain cannot be
## provoked from a program, so the pin is by text, the house pattern of
## `tsymex_0016_d3_include_census.nim`: each of the nine names is reset by
## `resetSymexRunState`, directly or through the reset proc of the module that
## owns it. A tenth such threadvar added to the list below without a reset line
## fails here, and so does deleting one of the nine resets.
import std/[unittest, os, strutils]


const
  smt = currentSourcePath().parentDir() / ".." / "src" / "nelli" / "smt"

  ## Reset by an assignment in `resetSymexRunState` itself.
  direct = ["pendingPtrCompares", "closureEnvWrites", "loweringReadNames",
            "lastDrainedClosureExitPc", "lowerAsReceiver", "glUnwrittenCtx",
            "seqConformCounter"]

proc readSmt(f: string): string = readFile(smt / f)

proc bodyFrom(text, header: string): string =
  ## From `header` to the next top-level declaration.
  let at = text.find(header)
  doAssert at >= 0, "missing " & header
  let rest = text[at + header.len .. ^1]
  var stop = rest.len
  for kw in ["\nproc ", "\nfunc ", "\ntemplate ", "\nvar ", "\ntype "]:
    let k = rest.find(kw)
    if k >= 0 and k < stop: stop = k
  rest[0 ..< stop]

suite "RFC-0016 H1 R1-12: per-run lowering state is reset":
  let rt = readSmt("runtime.nim")
  let resetBody = bodyFrom(rt, "proc resetSymexRunState(")

  test "the seven runtime.nim threadvars are reset by assignment":
    for n in direct:
      checkpoint n
      check rt.contains("{.threadvar.}") and
            rt.contains("var " & n & " {.threadvar.}")
      check resetBody.contains("\n  " & n & " = ")

  test "allocEnumZeroLegal is reset through resetHeapModel":
    check resetBody.contains("\n  resetHeapModel()")
    let hm = bodyFrom(readSmt("heap_model.nim"), "proc resetHeapModel*()")
    check hm.contains("\n  allocEnumZeroLegal = false")

  test "strCharsCounter is reset through resetStringLowering":
    check resetBody.contains("\n  resetStringLowering()")
    let sl = bodyFrom(readSmt("runtime_strings.nim"),
                      "proc resetStringLowering*()")
    check sl.contains("\n  strCharsCounter = 0")
