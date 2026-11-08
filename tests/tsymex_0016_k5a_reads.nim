## RFC-0016 K5a (section 8.3). Every read of the build occurs in
## `buildprofile.nim` only: `defined(nimPanics)`, `compileOption(` and
## `defined(release)` appear nowhere else in `src/nelli`. Every walker arm that
## depends on the build asks `buildSemantics`, so a new read cannot grow
## outside the profile unnoticed. (`tsymex_0016_w1c1b_reads` pins the Wave-1
## sites by name; this is the whole-tree form.)
import std/[unittest, strutils, os]
import nelli/symex

proc codeLines(txt: string): string =
  ## Source text without whole-line comments.
  for l in txt.splitLines:
    if not l.strip.startsWith("#"): result.add l & "\n"

suite "K5a: the build is read in buildprofile.nim only":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 288

  test "no build read outside buildprofile.nim":
    let root = currentSourcePath().parentDir.parentDir / "src" / "nelli"
    let reads = ["defined(nimPanics)", "compileOption(", "defined(release)"]
    var seen: array[3, bool]
    var scanned = 0
    for f in walkDirRec(root):
      if not f.endsWith(".nim"): continue
      inc scanned
      let txt = codeLines(readFile(f))
      for i, m in reads:
        if m in txt:
          if f.extractFilename == "buildprofile.nim": seen[i] = true
          else:
            checkpoint f & " still holds " & m
            fail()
    check scanned > 50
    check seen[0] and seen[1] and seen[2]   # held there, not vanished

  test "the dsl_parser assertion reads go through the profile":
    let txt = codeLines(readFile(currentSourcePath().parentDir.parentDir /
                                 "src" / "nelli" / "smt" / "dsl_parser.nim"))
    check "coAssert in buildSemantics.checks" in txt
    check "compileOption(\"assertions\")" notin txt
