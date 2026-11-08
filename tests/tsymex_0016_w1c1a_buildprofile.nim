## RFC-0016 W1-c1a (section 8.3). `buildprofile.nim` is the one place the
## build's `compileOption` reads for the checks, the memory model, the backend
## and the exception model live, and `buildSegment` renders them for the cache key (RFC-0016 K5a).
import std/[unittest, strutils, os]
import nelli/smt/buildprofile
import nelli/smt/canonicalize

suite "W1-c1a: buildprofile":
  test "buildSegment renders this build (the goldens are CR2's)":
    let seg = buildSegment(buildSemantics, readHost("4.13.4.0"))
    check ("backend=" & (when defined(cpp): "cpp" else: "c")) in seg
    check "mm=orc" in seg
    check seg.startsWith("bs1<build:")

  test "the moved reads occur only in buildprofile.nim":
    let root = currentSourcePath().parentDir.parentDir / "src" / "nelli"
    # `compileOption("assertions")` also stays in dsl_parser.nim until W1-c1b,
    # so it is not asserted here.
    let moved = [
      "compileOption(\"overflowChecks\")",
      "compileOption(\"boundChecks\")", "compileOption(\"fieldChecks\")",
      "compileOption(\"objChecks\")", "compileOption(\"rangeChecks\")",
      "compileOption(\"nanChecks\")", "compileOption(\"infChecks\")",
      "compileOption(\"mm\", \"orc\")", "compileOption(\"exceptions\", \"goto\")",
      "const buildChecksOn", "const buildMemModel", "const buildBackend",
      "const buildExceptions"]
    var seen: array[13, bool]
    var files = 0
    for f in walkDirRec(root):
      if not f.endsWith(".nim"): continue
      inc files
      let txt = readFile(f)
      for i, m in moved:
        if m in txt:
          if f.extractFilename == "buildprofile.nim": seen[i] = true
          else:
            checkpoint f & " still holds " & m
            fail()
    check files > 10
    for i in 0 ..< 9:
      check seen[i]   # the reads moved here, not vanished
