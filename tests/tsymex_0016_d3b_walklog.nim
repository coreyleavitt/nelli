## RFC-0016 review D3b: the walker does no file I/O and reads no environment;
## the walk-units log is `smt/walk_log.nim`'s alone.
import std/[unittest, strutils, os, algorithm]
import nelli/smt/walk_log

const srcDir = currentSourcePath().parentDir.parentDir / "src" / "nelli" / "smt"

## Deliberate sites: (file, token) pairs allowed in `runtime*.nim`. None: the
## stderr banner and the `symexFiberTrace` traces are `writeLine` calls, not
## file or environment access, and are not in the token list.
const allowed: seq[(string, string)] = @[]

const tokens = ["getEnv", "existsEnv", "open(", "writeFile", "readFile",
                "putEnv", "delEnv"]

proc code(line: string): string =
  let h = line.find('#')
  if h < 0: line else: line[0 ..< h]

proc hits(text: string): seq[(int, string)] =
  ## Every token occurrence outside a comment, not part of a longer
  ## identifier (`reopen(`, `isOpen(` do not count).
  var n = 0
  for line in text.splitLines:
    inc n
    let l = code(line)
    for t in tokens:
      var i = l.find(t)
      while i >= 0:
        if i == 0 or l[i-1] notin IdentChars:
          result.add (n, t)
        i = l.find(t, i + 1)

suite "D3b: the walker is pure of I/O":
  test "census: runtime*.nim has no env read or file access outside the allowlist":
    var files: seq[string]
    for p in walkFiles(srcDir / "runtime*.nim"): files.add p
    files.sort()
    check files.len >= 5
    var bad: seq[string]
    for p in files:
      let name = p.extractFilename
      for (n, t) in hits(readFile(p)):
        if (name, t) notin allowed: bad.add name & ":" & $n & " " & t
    check bad == newSeq[string]()

  test "the census sees a site (the scanner is not vacuous)":
    check hits("let p = getEnv(\"X\")\n# open( in a comment\nf.open(a)\nreopen(b)\n").len == 2

suite "D3b: the walk-units log bytes":
  test "a walk line: units, target, status, walker share":
    check renderWalkUnits(WalkUnitsLine(units: 1234, target: "label:hit",
      status: "sxSat", walkerUnits: 56, hasWalkerUnits: true)) ==
      "1234\tlabel:hit\tsxSat\t56\n"

  test "a tail line carries no walker column":
    check renderWalkUnits(WalkUnitsLine(units: 7, target: "k10b-tail",
      status: "{}")) == "7\tk10b-tail\t{}\n"

  test "appended to the file the environment names; off when unset":
    let log = getTempDir() / "d3b_walklog_golden.log"
    removeFile(log)
    delEnv(walkUnitsLogEnv)
    appendWalkUnits(WalkUnitsLine(units: 1, target: "t", status: "s"))
    check not fileExists(log)
    putEnv(walkUnitsLogEnv, log)
    try:
      appendWalkUnits(WalkUnitsLine(units: 1234, target: "label:hit",
        status: "sxSat", walkerUnits: 56, hasWalkerUnits: true))
      appendWalkUnits(WalkUnitsLine(units: 7, target: "k10b-tail",
        status: "{}"))
    finally:
      delEnv(walkUnitsLogEnv)
    check readFile(log) == "1234\tlabel:hit\tsxSat\t56\n7\tk10b-tail\t{}\n"
    removeFile(log)
