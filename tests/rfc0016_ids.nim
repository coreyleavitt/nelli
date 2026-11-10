## RFC-0016 K1a-ids (section 8.2): the work list's id join, and the allowlist
## entry rules it shares with K1a-cells.
##
## An id is EVIDENCED when its row names a pin, which is one of
##   * `cells`: at least one rendered `CellKey` that parses back to a real key
##     (a table's cell, an `errorkind:`, `capkind:` or `build:row/` key the
##     universe derives). The cell then needs its own pin record or
##     allowlist entry in the cell join, so the id is as proven as its cell;
##   * `pins`: a registered test file (in `tests/`, listed in `nelli.nimble`).
## An entry may end in a fourth field `rows=<row>,<row>`: it then applies to
## those build rows only (a cell that only some rows can evidence).
## Only an `open` row needs evidence. An open row with none must be in
## `tests/0016-allowlist/ids.txt` (`id<TAB>slice<TAB>reason`); an entry for a
## row that is not open, or is evidenced, is stale and fails, so entries ratchet
## out. An alias (`F-0001` for W-01) resolves to its row.
import std/[os, strutils, sets, options, sequtils, tables]
import nelli/smt/admission
import ./worklist_toml

const unassigned* = "UNASSIGNED"   ## rejected as a slice id

type Allow* = object
  key*, slice*, reason*: string
  rows*: seq[string]   ## optional row scope; empty means every row

proc sliceIds*(rfcText: string): HashSet[string] =
  ## The ids in the first column of the RFC's tables.
  for line in rfcText.splitLines():
    if line.startsWith("| "):
      let cell = line[2 .. ^1].split('|')[0].strip()
      if cell.len > 0 and ' ' notin cell and not cell.startsWith("-"):
        for part in cell.split('/'): result.incl part.strip(chars = {'`', ' '})
        result.incl cell.strip(chars = {'`', ' '})

proc sliceIds11*(rfcText: string): HashSet[string] =
  ## The slice ids of section 11 alone: the work-list tables (section 5) reuse
  ## some names (INF-05 is a row and a slice), but a work-list id is never a
  ## filling slice by being listed in section 5.
  let lines = rfcText.splitLines()
  var inside = false
  var sect: seq[string]
  for l in lines:
    if l.startsWith("## "): inside = l.startsWith("## §11")
    if inside: sect.add l
  sliceIds(sect.join("\n"))

proc parseAllow*(text: string): seq[Allow] =
  for raw in text.splitLines():
    let l = raw.strip(trailing = true)
    if l.len == 0 or l.startsWith("#"): continue
    let f = l.split('\t')
    var rows: seq[string]
    if f.len > 3 and f[3].strip.startsWith("rows="):
      for r in f[3].strip["rows=".len .. ^1].split(','):
        if r.strip.len > 0: rows.add r.strip
    result.add Allow(key: f[0], slice: (if f.len > 1: f[1].strip else: ""),
                     reason: (if f.len > 2: f[2].strip else: ""), rows: rows)

proc entryProblems*(a: Allow; slices: HashSet[string]): seq[string] =
  ## The rules every allowlist line obeys: a real slice id (never UNASSIGNED)
  ## and a reason.
  if a.slice notin slices:
    result.add "allowlist entry " & a.key & ": slice \"" & a.slice &
               "\" is not a slice id of the RFC (" & unassigned &
               " is not allowed: name the slice that fills it)"
  if a.reason.len == 0:
    result.add "allowlist entry " & a.key & " has no reason"

# --- the id join -----------------------------------------------------------

proc resolve*(w: Worklist; id: string): Option[WRow] =
  ## A row by its id, or by one of its aliases.
  for r in w.rows:
    if r.id == id or id in r.list("aliases"): return some(r)

proc cellProblems*(r: WRow; universeKeys: HashSet[string]): seq[string] =
  ## A `cells` entry must parse back to a real key (a typo names nothing).
  for c in r.list("cells"):
    let real =
      if c.startsWith("errorkind:") or c.startsWith("capkind:") or
         c.startsWith("build:row/"): c in universeKeys
      else: parseCellKey(c).isSome and c in universeKeys
    if not real:
      result.add r.id & ": cell \"" & c & "\" is not a cell of the universe"

proc registeredTests*(nimbleText: string): HashSet[string] =
  for l in nimbleText.splitLines():
    let t = l.strip()
    if t.startsWith("\"") and t.endsWith("\","):
      result.incl t[1 ..< t.len - 2]

proc pinProblems*(r: WRow; registered: HashSet[string]; testsDir: string):
    seq[string] =
  for p in r.list("pins"):
    if p notin registered:
      result.add r.id & ": pin \"" & p & "\" is not registered in nelli.nimble"
    if not fileExists(testsDir / (p & ".nim")):
      result.add r.id & ": pin \"" & p & "\" is not a file in tests/"

func evidenced*(r: WRow): bool =
  r.list("cells").len > 0 or r.list("pins").len > 0

func needsEvidence*(r: WRow): bool = r.get("state") == "open"

proc joinIds*(w: Worklist; allow: seq[Allow]; slices: HashSet[string];
              universeKeys, registered: HashSet[string]; testsDir: string):
    seq[string] =
  ## One message per failing id or entry.
  result.add w.validate()
  for r in w.rows:
    result.add r.cellProblems(universeKeys)
    result.add r.pinProblems(registered, testsDir)
    if r.get("slice").len > 0 and r.get("state") != "moved" and
       r.get("slice") notin slices:
      result.add r.id & ": slice \"" & r.get("slice") & "\" is not a slice id of the RFC"
  var listed = initHashSet[string]()
  for a in allow:
    result.add entryProblems(a, slices)
    let row = w.resolve(a.key)
    if row.isNone:
      result.add "allowlist entry " & a.key & " names no work-list id"
      continue
    let r = row.get
    if r.id in listed:
      result.add "allowlist entry " & a.key & " is listed twice (id " & r.id & ")"
    listed.incl r.id
    if not r.needsEvidence:
      result.add "stale allowlist entry " & a.key & ": row " & r.id &
                 " is " & r.get("state") & ", only an open id is listed; remove the line"
    elif r.evidenced:
      result.add "stale allowlist entry " & a.key & ": row " & r.id &
                 " names a cell or pin now; remove the line"
  for r in w.rows:
    if r.needsEvidence and not r.evidenced and r.id notin listed:
      result.add "open id " & r.id & " has no cell or pin and no ids.txt entry"

# --- the F ledger (RFC section 8.2) ----------------------------------------

proc isFId*(s: string): bool =
  ## `F-` and exactly four digits.
  s.len == 6 and s.startsWith("F-") and s[2 .. 5].allIt(it in {'0' .. '9'})

proc fLedger*(w: Worklist): seq[(string, string)] =
  ## Every (F id, row id) the work list names: a row id of the form F-NNNN, an
  ## alias of that form, or a `source` that is exactly one. The F ledger lives
  ## in the TOML (a finding is its own open row, or an alias of the row it
  ## duplicates); the handoff's markdown table is history, not a source.
  for r in w.rows:
    var ids: seq[string]
    if r.id.startsWith("F-"): ids.add r.id
    for a in r.list("aliases"):
      if a.startsWith("F-"): ids.add a
    if r.get("source").startsWith("F-") and ' ' notin r.get("source"):
      ids.add r.get("source")
    for f in ids.deduplicate: result.add (f, r.id)

proc fLedgerProblems*(w: Worklist): seq[string] =
  ## Each F id is well-formed and names exactly one row. Nothing else: an F
  ## row may alias a closed row, alias an open one, or be its own open row.
  var owner = initTable[string, string]()
  for (f, row) in fLedger(w):
    if not f.isFId:
      result.add "F ledger id \"" & f & "\" (row " & row &
                 ") is not of the form F-NNNN"
    elif f in owner:
      result.add "F ledger id " & f & " names two rows: " & owner[f] &
                 " and " & row
    else: owner[f] = row
