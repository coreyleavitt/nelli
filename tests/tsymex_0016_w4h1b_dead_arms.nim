## RFC-0016 Wave 4 H1b (HRV-99): the boundary arms removed because they are
## unreachable, pinned by structure. The four string-family carriers
## (`SymexUnsupportedStringOpError`, `SymexUnsupportedRegexError`,
## `SymexZ3VersionMissingError`, `SymexZ3StringIncompleteError`) are raised
## only inside `lowerStrArm`'s call graph and caught in-band at its single
## call site (`degradeStrArm`, N36), so `runSymexCaught` never saw them;
## `SymexRefUnresolvedError` has no raiser at all. The in-band behaviour the
## surviving catches provide is pinned by `tsymex_rfc0005_s5_str.nim`
## (replace-all -> seZ3VersionMissing, regex -> seUnsupportedRegex, toOct ->
## seUnsupportedStringOp) and `tsymex_r6_n36_*`.
import std/[unittest, os, strutils]

const srcRoot = currentSourcePath().parentDir / ".." / "src" / "nelli"

proc codeLines(path: string): seq[string] =
  ## Non-comment source lines (a trimmed line starting with `#` is dropped;
  ## trailing comments are kept, which only makes the scans stricter).
  for l in readFile(path).splitLines:
    if not l.strip.startsWith("#"): result.add l

proc allNimFiles(): seq[string] =
  for f in walkDirRec(srcRoot):
    if f.endsWith(".nim"): result.add f

const stringCarriers = ["SymexUnsupportedStringOpError",
                        "SymexUnsupportedRegexError",
                        "SymexZ3VersionMissingError",
                        "SymexZ3StringIncompleteError"]

suite "RFC-0016 H1b HRV-99 - dead boundary arms stay removed":

  test "every raise of a string carrier is in runtime_strings.nim":
    for f in allNimFiles():
      for l in codeLines(f):
        for c in stringCarriers:
          if "raise (ref " & c & ")" in l or "newException(" & c in l:
            check f.extractFilename == "runtime_strings.nim"

  test "runtime_strings.nim's only exported entry is lowerStrArm, called once":
    var exported: seq[string]
    for l in codeLines(srcRoot / "smt" / "runtime_strings.nim"):
      for kw in ["proc ", "template ", "func "]:
        if l.startsWith(kw):
          let head = l[kw.len .. ^1].split({'(', ':', '='})[0].strip
          if head.endsWith("*"): exported.add head
    # The other two exports neither raise a carrier nor are callers' way in.
    check exported == @["regexFreshName*", "lowerStrArm*", "resetStringLowering*"]
    var callSites = 0
    for f in allNimFiles():
      if f.extractFilename == "runtime_strings.nim": continue
      for l in codeLines(f):
        if "lowerStrArm(" in l: inc callSites
    check callSites == 1

  test "the string carriers are caught once each, at that call site, not at the boundary":
    # RFC-0016 INT-34 B4: the call site moved with `lower` into
    # `lower_expr.nim`; `runtime.nim` is read too, so neither file may add one.
    let rt = codeLines(srcRoot / "smt" / "runtime.nim") &
             codeLines(srcRoot / "smt" / "lower_expr.nim")
    for c in stringCarriers:
      var n = 0
      for l in rt:
        if l.strip.startsWith("except " & c): inc n
      check n == 1

  test "SymexRefUnresolvedError is gone: nothing raised or caught it":
    for f in allNimFiles():
      for l in codeLines(f):
        check "SymexRefUnresolvedError" notin l
