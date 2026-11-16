## RFC-0016 W3-z E6 (F9): the allowlist ratchet. Section 8.2 says an allowlist
## "grows only in the commit that introduces its scope"; review alone held that
## and census.txt grew from 152 to 170 under it.
##
## `tests/0016-allowlist/ceilings.txt` holds one line per allowlist file,
## `file<TAB>ceiling`. A file's DEBT is its count of non-comment lines that
## carry no `rows=` scope (a `rows=` entry is a platform classification, not
## owed work: decision (a) of intro-counts.txt). The `rows=`-scoped entries
## are not free: all of them together sit under their own ceiling (the
## `rowsKey` line), so a scope cannot be added to dodge the debt ceiling and
## the figure only falls (L-M1). The test fails when
##   * the debt is above the ceiling (the list grew);
##   * the debt is below the ceiling (the list shrank and the ceiling did not
##     follow, so a later commit could refill the gap);
##   * an allowlist file has no ceiling line, or a ceiling names no file.
## Not checkable here: that a new cell's own entry is added together with a
## ceiling bump in one commit. The rule is in the ceilings.txt header; review
## holds it, and the bump is visible in the diff of that one small file.
import std/[unittest, os, strutils, tables, algorithm]

const
  root = currentSourcePath().parentDir() / ".."
  dir = root / "tests" / "0016-allowlist"
  ceilingsName = "ceilings.txt"
  noProducerKey* = "no-producer=marked"   ## the ceilings.txt line for L-M3's marker
  noProducerMarker* = "[no-producer]"
  rowsKey* = "rows=scoped"   ## the ceilings.txt line for every rows= entry, all files
  # Not allowlists: these hold other ledgers (introduction counts, the
  # over-introduction blockers, and the ceilings themselves).
  meta = ["ceilings.txt", "intro-counts.txt", "over-intro.txt"]

proc isDebt*(line: string): bool =
  ## A countable line: not blank, not a comment, not `rows=`-scoped.
  let l = line.strip(trailing = true)
  if l.len == 0 or l.startsWith("#"): return false
  let f = l.split('\t')
  for i in 1 .. f.high:
    if f[i].strip.startsWith("rows="): return false
  true

proc isRowScoped*(line: string): bool =
  ## A countable line that carries a `rows=` scope.
  let l = line.strip(trailing = true)
  if l.len == 0 or l.startsWith("#"): return false
  let f = l.split('\t')
  for i in 1 .. f.high:
    if f[i].strip.startsWith("rows="): return true

proc rowScoped*(text: string): int =
  for l in text.splitLines():
    if isRowScoped(l): inc result

proc noProducer*(text: string): int =
  ## Reasons that carry the L-M3 marker (tsymex_0016_noproducer derives the set).
  for l in text.splitLines():
    if isDebt(l) and noProducerMarker in l: inc result

proc debt*(text: string): int =
  for l in text.splitLines():
    if isDebt(l): inc result

proc parseCeilings*(text: string): Table[string, int] =
  for l in text.splitLines():
    let t = l.strip()
    if t.len == 0 or t.startsWith("#"): continue
    let f = t.split('\t')
    if f.len >= 2: result[f[0]] = parseInt(f[1].strip)

proc ceilingProblems*(counts, ceilings: Table[string, int]): seq[string] =
  var names: seq[string]
  for k in counts.keys: names.add k
  names.sort()
  for n in names:
    if n notin ceilings:
      result.add n & ": no line in " & ceilingsName & " (add `" & n & "\t" &
                 $counts[n] & "`, in the commit that introduces the file)"
    elif counts[n] > ceilings[n]:
      result.add n & ": " & $counts[n] & " entries are above the ceiling " &
                 $ceilings[n] & " (the list grew; an entry joins a list only " &
                 "in the commit that introduces its scope)"
    elif counts[n] < ceilings[n]:
      result.add n & ": " & $counts[n] & " entries are below the ceiling " &
                 $ceilings[n] & " (lower the ceiling to " & $counts[n] & ")"
  for n in ceilings.keys:
    if n notin counts:
      result.add n & ": " & ceilingsName & " names no allowlist file"

suite "RFC-0016 E6: the allowlist ratchet (synthetic lists)":
  test "debt counts entries and skips comments, blanks and rows= scopes":
    check debt("# c\n\na\tS\tr\nb\tS\tr\trows=mingw\nc\tS\tr\n") == 2
    check debt("name only\n") == 1

  test "L-M1: rows= entries are counted apart from the debt":
    check rowScoped("# c\n\na\tS\tr\nb\tS\tr\trows=mingw\nc\tS\tr\trows=a,b\n") == 2
    check not isRowScoped("a\tS\tr")

  test "L-M1 RED: a new rows= entry lifts the rows= count above its ceiling":
    let p = ceilingProblems({rowsKey: 13}.toTable, {rowsKey: 12}.toTable)
    check p.len == 1 and "above the ceiling" in p[0]

  test "L-M3 RED: a new no-producer marker lifts the count above its ceiling":
    check noProducer("a\tS\tr [no-producer]\nb\tS\tr\n# [no-producer]\n") == 1
    let p = ceilingProblems({noProducerKey: 13}.toTable,
                            {noProducerKey: 12}.toTable)
    check p.len == 1 and "above the ceiling" in p[0]

  test "RED: a list that grew fails":
    let p = ceilingProblems({"x.txt": 4}.toTable, {"x.txt": 3}.toTable)
    check p.len == 1 and "above the ceiling" in p[0]

  test "RED: a list that shrank without lowering its ceiling fails":
    let p = ceilingProblems({"x.txt": 2}.toTable, {"x.txt": 3}.toTable)
    check p.len == 1 and "below the ceiling" in p[0]

  test "a list at its ceiling is clean":
    check ceilingProblems({"x.txt": 3}.toTable, {"x.txt": 3}.toTable).len == 0

  test "RED: a file with no ceiling line, and a ceiling with no file, fail":
    check ceilingProblems({"x.txt": 1}.toTable, initTable[string, int]()).len == 1
    check ceilingProblems(initTable[string, int](), {"y.txt": 1}.toTable).len == 1

suite "RFC-0016 E6: the allowlist ratchet (the tree)":
  test "every allowlist file sits at its committed ceiling":
    var counts = initTable[string, int]()
    for p in walkFiles(dir / "*.txt"):
      let n = p.extractFilename
      if n in meta: continue
      counts[n] = debt(readFile(p))
      if n == "errorkind.txt":
        counts[noProducerKey] = noProducer(readFile(p))
      counts[rowsKey] = counts.getOrDefault(rowsKey) + rowScoped(readFile(p))
    let ceilings = parseCeilings(readFile(dir / ceilingsName))
    let problems = ceilingProblems(counts, ceilings)
    if problems.len > 0: echo problems.join("\n")
    check problems.len == 0
    check counts.len >= 15   # a rule that finds nothing is broken
