## RFC-0016 W1-c1a (section 8.3). `buildprofile.nim` is the one place the
## build's `compileOption` reads for the checks, the memory model, the backend
## and the exception model live, and `buildSegment` renders the `|bf=` text the
## cache key has always carried, byte for byte.
import std/[unittest, strutils, os]
import nelli/smt/buildprofile
import nelli/smt/canonicalize

const
  goldenC = "ck=assertions,boundChecks,fieldChecks,objChecks,overflowChecks," &
    "rangeChecks+mm=orc+be=c+ex=goto+thr+st+lt"
  goldenCpp = "ck=assertions,boundChecks,fieldChecks,objChecks,overflowChecks," &
    "rangeChecks+mm=orc+be=cpp+ex=cpp+thr+st+lt"

suite "W1-c1a: buildprofile":
  test "buildSegment is the old |bf= text on this leg":
    when defined(cpp):
      check buildSegment() == goldenCpp
    else:
      check buildSegment() == goldenC
    check buildFlagsSegment() == buildSegment()

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
