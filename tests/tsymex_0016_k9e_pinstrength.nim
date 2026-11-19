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
## - every suite the measurement runs exists and is registered in
##   `nelli.nimble`, so the list cannot name a suite no CI leg keeps green.
##
## THE RATCHET. The floor only rises: after a full run, raise it to the new
## figure in the same commit as the TSV. A survivor is a finding (a new pin, or
## an equivalent-mutant justification in docs/rfc-data/0016-k9e.md), never a
## lowered floor.
import std/[unittest, os, strutils, tables]

const
  root = currentSourcePath().parentDir.parentDir
  tsvPath = root / "tests" / "0016-pinstrength.tsv"
  floorPath = root / "tests" / "0016-pinstrength.floor"
  suitesPath = root / "tests" / "0016-pinstrength.suites"
  nimblePath = root / "nelli.nimble"
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

suite "RFC-0016 K9e: pin strength":
  let floorLines = codeLines(floorPath)
  let floor = parseFloat(floorLines[0])
  var header: seq[string]
  var counts = initCountTable[string]()
  var rows = 0
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

  test "every measured suite exists and is registered":
    let nimble = readFile(nimblePath)
    let suites = codeLines(suitesPath)
    check suites.len > 0
    check parseInt(headerField(all, "suites")) == suites.len
    for s in suites:
      check fileExists(root / "tests" / (s & ".nim"))
      check ("\"" & s & "\"") in nimble
