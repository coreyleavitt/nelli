## RFC-0016 K9e: the pin-strength figure is at or above its floor (exit
## criterion 4).
##
## `scripts/pin-strength.sh` applies each mutant `scripts/pin-strength-mutants.py`
## enumerates over the walker's arithmetic and raise arms (operator swaps,
## signedness and bound swaps, dropped forks, swapped defect kinds) and runs
## the pin suites of `tests/0016-pinstrength.suites` against it. Its result is
## committed as `tests/0016-pinstrength.tsv`; the figure is
## killed / (killed + survived). This test reads that file, never runs it:
##
## - the figure, recomputed from the rows, is at or above
##   `tests/0016-pinstrength.floor`, and the header states that same figure
##   (a hand-edited header fails);
## - every row has a known status, and its counts agree with the header;
## - once the floor is above zero the run must be complete: one row per
##   mutant the header counts, no `timeout` left unrerun (a partial run
##   cannot certify a floor);
## - once the floor is above zero, every `survived` row's id is in the
##   "## Equivalent mutants" table of docs/rfc-data/0016-k9e.md (a survivor is
##   closed by a justification or a pin, never left open), and no id in that
##   table is recorded `killed` (a stale justification);
## - once the floor is above zero, the TSV's ids are exactly the ids
##   `python3 scripts/pin-strength-mutants.py list` enumerates for the current
##   tree, and the header's `mutants:` equals that count (a regenerated mutant
##   set cannot leave a stale TSV certifying ids that no longer exist);
## - every suite the measurement runs exists and is registered in
##   `nelli.nimble`, so the list cannot name a suite no CI leg keeps green.
##
## THE RATCHET. The floor only rises: after a full run, raise it to the new
## figure in the same commit as the TSV. A survivor is a finding (a new pin, or
## an equivalent-mutant justification in docs/rfc-data/0016-k9e.md), never a
## lowered floor.
import std/[unittest, os, strutils, tables, osproc, sets]

const
  root = currentSourcePath().parentDir.parentDir
  tsvPath = root / "tests" / "0016-pinstrength.tsv"
  floorPath = root / "tests" / "0016-pinstrength.floor"
  suitesPath = root / "tests" / "0016-pinstrength.suites"
  nimblePath = root / "nelli.nimble"
  docPath = root / "docs" / "rfc-data" / "0016-k9e.md"
  generatorPath = root / "scripts" / "pin-strength-mutants.py"
  statuses = ["killed", "survived", "timeout", "stillborn", "equivalent", "error"]

proc codeLines(path: string): seq[string] =
  for l in readFile(path).splitLines:
    let c = l.split('#')[0].strip
    if c.len > 0: result.add c

proc headerField(header: string; name: string): string =
  ## `name: value` in the header line, the value up to the next blank.
  let i = header.find(name & ": ")
  doAssert i >= 0, "pin-strength header has no `" & name & "`: " & header
  header[i + name.len + 2 .. ^1].split(' ')[0]

proc figureOf(killed, survived: int): float =
  if killed + survived == 0: 0.0 else: 100.0 * killed.float / float(killed + survived)

proc equivalenceIds(doc: string): HashSet[string] =
  ## First-column ids of the table under "## Equivalent mutants", up to the
  ## next "## " heading, backticks stripped.
  var inSection = false
  for l in doc.splitLines:
    if l.startsWith("## "):
      inSection = l.strip == "## Equivalent mutants"
      continue
    if not inSection or not l.startsWith("|"): continue
    let cell = l.split('|')[1].strip.replace("`", "").strip
    if cell.len > 0 and cell != "id" and not cell.startsWith("--"):
      result.incl cell

proc survivorProblems(rows: seq[(string, string)];
                      equiv: HashSet[string]): seq[string] =
  ## Unjustified survivors, and justifications the run shows killed.
  for (id, status) in rows:
    if status == "survived" and id notin equiv:
      result.add "survivor without justification: " & id
    if status == "killed" and id in equiv:
      result.add "stale justification (killed): " & id

proc generatorProblems(rows: seq[(string, string)];
                       gen: HashSet[string]): seq[string] =
  ## The TSV's id set against the generator's, both directions.
  var tsv = initHashSet[string]()
  for (id, _) in rows: tsv.incl id
  for id in tsv - gen: result.add "TSV id the generator no longer lists: " & id
  for id in gen - tsv: result.add "generator id missing from the TSV: " & id

proc generatorIds(): HashSet[string] =
  let (o, rc) = execCmdEx("python3 " & quoteShell(generatorPath) & " list " &
                          quoteShell(root))
  doAssert rc == 0, "pin-strength-mutants.py list failed: " & o
  for l in o.splitLines:
    if l.len > 0: result.incl l.split('\t')[0]

suite "RFC-0016 K9e: survivor and generator checks, on fixtures":
  let eq = toHashSet(["ma", "mb"])
  test "a survivor with no justification fails":
    check survivorProblems(@[("mc", "survived")], eq).len == 1
  test "a justified survivor passes":
    check survivorProblems(@[("ma", "survived")], eq).len == 0
  test "a killed id in the equivalence table fails":
    check survivorProblems(@[("mb", "killed")], eq).len == 1
  test "the equivalence table parses backticked and bare ids, only its section":
    let doc = "## A\n| `mx` | x |\n## Equivalent mutants\n\n| id | site |\n|----|----|\n| `ma` | s |\n| mb | s |\n## B\n| `my` | y |\n"
    check equivalenceIds(doc) == eq
  test "a TSV id missing from the generator fails":
    check generatorProblems(@[("ma", "killed"), ("mz", "killed")],
                            toHashSet(["ma"])).len == 1
  test "a generator id missing from the TSV fails":
    check generatorProblems(@[("ma", "killed")],
                            toHashSet(["ma", "mq"])).len == 1
  test "matching sets pass":
    check generatorProblems(@[("ma", "killed")], toHashSet(["ma"])).len == 0

suite "RFC-0016 K9e: pin strength":
  let floorLines = codeLines(floorPath)
  let floor = parseFloat(floorLines[0])
  var header: seq[string]
  var counts = initCountTable[string]()
  var rows = 0
  var tsvRows: seq[(string, string)]
  for l in readFile(tsvPath).splitLines:
    if l.len == 0: continue
    if l.startsWith("#"):
      header.add l
      continue
    if l.startsWith("id\t"): continue
    let f = l.split('\t')
    check f.len == 7
    check f[0].len == 11 and f[0][0] == 'm'
    check f[3] in statuses
    counts.inc f[3]
    tsvRows.add (f[0], f[3])
    inc rows
  let all = header.join(" ")

  test "the floor file holds one figure":
    check floorLines.len == 1
    check floor >= 0.0 and floor <= 100.0

  test "the figure is at or above its floor, and the header states it":
    let k = counts["killed"]
    let s = counts["survived"]
    let fig = figureOf(k, s)
    check fig >= floor
    var stated = ""
    for h in header:
      if h.startsWith("# figure:"): stated = h.splitWhitespace[^1]
    check stated == formatFloat(fig, ffDecimal, 1)
    check parseInt(headerField(all, "killed")) == k
    check parseInt(headerField(all, "survived")) == s
    check parseInt(headerField(all, "timeout")) == counts["timeout"]
    check parseInt(headerField(all, "run")) == rows

  test "a floor above zero is certified by a complete run":
    if floor > 0.0:
      check rows == parseInt(headerField(all, "mutants"))
      check counts["timeout"] == 0
      check counts["error"] == 0

  test "a floor above zero: every survivor is justified, no justification is stale":
    if floor > 0.0:
      check survivorProblems(tsvRows, equivalenceIds(readFile(docPath))) ==
        newSeq[string]()

  test "a floor above zero: the TSV matches the generator's mutant set":
    if floor > 0.0:
      let gen = generatorIds()
      check generatorProblems(tsvRows, gen) == newSeq[string]()
      check parseInt(headerField(all, "mutants")) == gen.len

  test "every measured suite exists and is registered":
    let nimble = readFile(nimblePath)
    let suites = codeLines(suitesPath)
    check suites.len > 0
    check parseInt(headerField(all, "suites")) == suites.len
    for s in suites:
      check fileExists(root / "tests" / (s & ".nim"))
      check ("\"" & s & "\"") in nimble
