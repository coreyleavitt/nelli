## RFC-0016 K9d (W-54, F-03): no verdict suite without a native pin.
##
## A symex suite that asserts a definite verdict (`sxSat`, `sxUnsat`,
## `sxRaised`) and never runs its SUT natively states a claim nothing checks.
## F-03 counted 481 such suites at 83c1d304; K9d pins them by family through
## `pinFind` (s8cu_helpers.nim), which reproduces each definite verdict
## natively and writes a K9 record.
##
## The census. A SUITE is a `tests/tsymex_*.nim` file. It is VERDICT-ASSERTING
## when its code (comments stripped) names `sxSat`, `sxUnsat` or `sxRaised`.
## It is PINNED when its code uses a native idiom: a K9 verb (`pinFind`,
## `pinExact`, `pinCrash`, `pinNever`, `pinCap`, `pinUndefined`,
## `pinRefused`), the shared native helpers (`nativeHits`, `nativeRun`,
## `native(`), the capture frame (`symexCaptureBegin`), the engine's replay
## (`replayWitness`, `assertCoveredBy`, `viaCovered`), or a child process
## (`execCmd`, `startProcess`, `nim c`, `prepareProbe`). F-03's idiom list,
## plus the K9 verbs that postdate it. The census is per file: a pinned suite
## may still hold an unpinned call (`pinFind` returns a decline unpinned).
##
## THE RATCHET. `ceiling` is the number of unpinned verdict suites allowed. It
## only falls: the test fails above it (a new unpinned verdict suite) and below
## it (a suite was pinned and the ceiling did not follow).
import std/[unittest, os, strutils, algorithm]

const
  ceiling = 107
  testsDir = currentSourcePath().parentDir()
  verdictWords = ["sxSat", "sxUnsat", "sxRaised"]
  idioms = ["pinFind", "pinExact", "pinCrash", "pinNever", "pinCap",
            "pinUndefined", "pinRefused", "nativeHits", "nativeRun",
            "native(", "symexCaptureBegin", "replayWitness",
            "assertCoveredBy", "viaCovered", "execCmd", "startProcess",
            "nim c", "prepareProbe"]

proc codeOf(text: string): string =
  ## `text` without full-line or trailing comments (a `#` outside a string).
  for line in text.splitLines():
    var inStr = false
    var cut = line.len
    for i, c in line:
      if c == '"': inStr = not inStr
      elif c == '#' and not inStr:
        cut = i
        break
    result.add line[0 ..< cut]
    result.add '\n'

proc hasWord(code, w: string): bool =
  var i = code.find(w)
  while i >= 0:
    let before = i == 0 or code[i - 1] notin IdentChars
    let j = i + w.len
    let after = j >= code.len or code[j] notin IdentChars
    if before and after: return true
    i = code.find(w, i + 1)

proc assertsVerdict*(text: string): bool =
  let code = codeOf(text)
  for w in verdictWords:
    if hasWord(code, w): return true

proc pinned*(text: string): bool =
  let code = codeOf(text)
  for w in idioms:
    if w in code: return true

proc census(): seq[string] =
  var files: seq[string]
  for f in walkFiles(testsDir / "tsymex_*.nim"): files.add f
  files.sort()
  for f in files:
    let t = readFile(f)
    if assertsVerdict(t) and not pinned(t): result.add f.extractFilename

suite "K9d: every verdict suite runs its SUT natively":
  test "the census reads the shapes it claims to":
    check assertsVerdict("check r.status == sxSat\n")
    check assertsVerdict("check r.status in {sxUnsat, sxUnknown}\n")
    check not assertsVerdict("check r.status == sxUnknown\n")
    check not assertsVerdict("# check r.status == sxSat\n")
    check not assertsVerdict("check r.status == sxSatX\n")
    check pinned("let r = pinFind(f, tLabel(\"hit\"))\n")
    check pinned("discard pinExact(f, k)\n")
    check pinned("let h = nativeHits(f(3))\n")
    check not pinned("# pinFind(f)\nlet r = symexFind(f, tLabel(\"hit\"))\n")

  test "no verdict suite is left without a native pin, ratcheted":
    let found = census()
    if found.len != ceiling:
      checkpoint "unpinned verdict suites (" & $found.len & "): " &
                 found.join(" ")
    check found.len <= ceiling   # a new unpinned verdict suite
    check found.len >= ceiling   # suites were pinned: lower `ceiling` to match
