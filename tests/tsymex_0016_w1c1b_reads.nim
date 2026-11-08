## RFC-0016 W1-c1b (section 8.3). The remaining Wave-1 build reads go through
## `buildprofile`, and a refused build is refused by name.
##
## `--mm:refc` (D-0016-7) is not a verified build. Before this slice a refc
## compile of anything importing `nelli/symex` stopped inside nim-z3
## (`z3/ast.nim: signature for '=destroy' must be proc[T: object](x: var T)`),
## which names neither the build nor the field. `symex.nim` now asks
## `admitBuild` before it imports `z3`, so the error is the refusal. That is
## import time, not entry-macro time: the entry macros are unreachable under
## refc, because the module that defines them cannot be imported.
import std/[unittest, strutils, os, options]
import nelli/smt/buildprofile
import nelli/smt/admission
import ./s8cu_helpers

proc codeLines(txt: string): string =
  ## Source text without whole-line comments.
  for l in txt.splitLines:
    if not l.strip.startsWith("#"): result.add l & "\n"

suite "W1-c1b: build reads and the refc refusal":
  test "the Wave-1 reads occur only in buildprofile.nim":
    let root = currentSourcePath().parentDir.parentDir / "src" / "nelli"
    # K5a (`tsymex_0016_k5a_reads`) extends this to every `compileOption(`.
    let moved = ["defined(nimPanics)", "compileOption(\"panics\")",
                 "compileOption(\"exceptions\"", "compileOption(\"stacktrace\")",
                 "compileOption(\"stackTrace\")"]
    var seen: array[5, bool]
    for f in walkDirRec(root):
      if not f.endsWith(".nim"): continue
      let txt = codeLines(readFile(f))
      for i, m in moved:
        if m in txt:
          if f.extractFilename == "buildprofile.nim": seen[i] = true
          else:
            checkpoint f & " still holds " & m
            fail()
    check seen[0] and seen[2] and seen[4]   # moved here, not vanished

  test "admitBuild refuses refc by field; the unpinned models by row":
    var b = buildSemantics
    b.mm = mmRefc
    let r = admitBuild(b)
    check r.isSome
    check r.get.field == bfMm
    check $r.get.field == "mm"
    check "D-0016-7" in r.get.reason
    check "refc" in r.get.reason
    for m in [mmOrc, mmArc, mmAtomicArc]:
      b.mm = m
      check admitBuild(b).isNone
    # K5a: a model no row is pinned on is refused as an unprojectable profile.
    for m in [mmMarkAndSweep, mmBoehm, mmGo, mmNone]:
      b.mm = m
      check admitBuild(b).get.field == bfRow
    check admitBuild().isNone   # this build is admitted, or this test did not run

  test "native: --mm:refc is refused by name at the import":
    pinRefused(cellKey(axBuild, "mm=refc"),
      "import nelli\nimport nelli/symex\n" &
      "proc sut(v: int) =\n  if v == 3: symexTarget(\"h\")\n" &
      "let r = symexFind(sut, tLabel(\"h\"))\necho r.status\n",
      ["--mm:refc", "--path:" & (currentSourcePath().parentDir.parentDir / "src")],
      "mm=refc is not a verified build")

  test "pinRefused fails on a build that compiles":
    var msg = ""
    try:
      pinRefused(cellKey(axBuild, "mm=orc"), "echo 1\n", [], "refused")
    except PinFailure as e: msg = e.msg
    check "was not refused" in msg
