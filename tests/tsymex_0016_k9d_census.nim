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
## A suite's code includes the files it `include`s (a fixture is its text).
##
## EXEMPT (K9d-12): a verdict suite with no native truth to pin, by a reason
## that names why: its verdict words are not a claim about a Nim program (a
## log line's text, a hand-built IR program with no source), or its pins are
## made by code it generates. An exemption is permanent and checked: an exempt
## suite that stops asserting a verdict, or becomes pinned, fails, so the list
## holds only what is still true.
##
## THE RATCHET. `ceiling` is the number of unpinned verdict suites allowed,
## exemptions apart. It only falls: the test fails above it (a new unpinned
## verdict suite) and below it (a suite was pinned and the ceiling did not
## follow).
import std/[unittest, os, strutils, algorithm]

const
  ceiling = 0
  exempt = [
    ("tsymex_0016_d3b_walklog.nim",
     "its verdict words are the walk-units log's text (`renderWalkUnits`): " &
     "it runs no SUT, so no native run can disagree"),
    ("tsymex_0016_k8a_gen.nim",
     "the generator's own suite: every generated program is pinned by the " &
     "`pinExactImpl` call `s0016_k8a_gen` writes into its source; the " &
     "verdict words here are record fields of planted fixtures"),
    ("tsymex_0016_k8b_pairs.nim",
     "it runs no walk: its verdict words are the `walker` field of a " &
     "planted record fixture (`pvExact`, \"sxSat\"), a string the pairwise " &
     "figure reads, so there is no SUT to run natively"),
    ("tsymex_rfc0005_s1_lattice.nim",
     "its one verdict is on a hand-built `SymexProgram` (a bare target node), " &
     "an IR with no Nim source, so there is no native program to run; the " &
     "rest is a source scan")]
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

proc withIncludes*(text, dir: string): string =
  ## `text` and, after it, every file it `include`s from `dir` (one level:
  ## a fixture includes nothing).
  result = text
  for line in codeOf(text).splitLines():
    let l = line.strip()
    if l.startsWith("include "):
      for part in l["include ".len .. ^1].split(','):
        let f = dir / (part.strip() & ".nim")
        if fileExists(f): result.add "\n" & readFile(f)

proc isExempt(name: string): bool =
  for (f, _) in exempt:
    if f == name: return true

proc unpinnedVerdict(f: string): bool =
  let t = withIncludes(readFile(f), testsDir)
  assertsVerdict(t) and not pinned(t)

proc census(): seq[string] =
  var files: seq[string]
  for f in walkFiles(testsDir / "tsymex_*.nim"): files.add f
  files.sort()
  for f in files:
    if unpinnedVerdict(f) and not isExempt(f.extractFilename):
      result.add f.extractFilename

suite "K9d: every verdict suite runs its SUT natively":
  test "the census reads the shapes it claims to":
    check assertsVerdict("check r.status == sxSat\n")
    check assertsVerdict("check r.status in {sxUnsat, sxUnknown}\n")
    # (spelt in two parts: K9c's census reads a whole source line as a
    # decline assertion)
    check not assertsVerdict("check r.status " & "== sxUnknown\n")
    check not assertsVerdict("# check r.status == sxSat\n")
    check not assertsVerdict("check r.status == sxSatX\n")
    check pinned("let r = pinFind(f, tLabel(\"hit\"))\n")
    check pinned("discard pinExact(f, k)\n")
    check pinned("let h = nativeHits(f(3))\n")
    check not pinned("# pinFind(f)\nlet r = symexFind(f, tLabel(\"hit\"))\n")

  test "an included fixture is part of the suite's code":
    let dir = getTempDir() / ("k9d_census_" & $getCurrentProcessId())
    createDir(dir)
    writeFile(dir / "fx.nim", "let r = pinFind(f, tLabel(\"hit\"))\n")
    let t = withIncludes("include fx\ncheck r.status == sxSat\n", dir)
    check assertsVerdict(t) and pinned(t)
    check not pinned(withIncludes("# include fx\ncheck r.status == sxSat\n", dir))
    removeDir(dir)

  test "every exemption is still an unpinned verdict suite, with a reason":
    for (f, why) in exempt:
      checkpoint f
      check fileExists(testsDir / f)
      check unpinnedVerdict(testsDir / f)   # pinned or verdict-free: drop it
      check why.len > 0

  test "no verdict suite is left without a native pin, ratcheted":
    let found = census()
    if found.len != ceiling:
      checkpoint "unpinned verdict suites (" & $found.len & "): " &
                 found.join(" ")
    check found.len <= ceiling   # a new unpinned verdict suite
    check found.len >= ceiling   # suites were pinned: lower `ceiling` to match
