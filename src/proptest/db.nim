## The example database — "remembers your bugs."
##
## Stores the choice sequences of falsified properties keyed by an opaque test
## id, so the engine's reuse phase can replay known failures first and report a
## known counterexample instantly. Also stores high-scoring non-failing examples
## (the secondary corpus) so targeted PBT can resume across runs.
##
## On-disk layout — one file `<dbPath>/<safeKey>.bin` per test id:
##   [version: u8 = 1]
##   [nPrimary: u64]
##   [nSecondary: u64]
##   [primary entries: for each, u64 size then `size` bytes of toBytes(seq)]
##   [secondary entries: for each, f64 score then u64 size then `size` bytes]
##
## Writes are atomic: contents land in `<file>.tmp` then `moveFile` renames it
## over the target so a crash during write can't half-corrupt the entry.

import std/[os, strutils, tables]
import ./choice, ./serialize

type
  ExampleDB* = object
    path*: string

  ScoredEntry* = tuple[choices: seq[ChoiceNode], score: float,
                       scores: Table[string, float]]
    ## Single-objective `score` is preserved for back-compat; multi-objective
    ## targeted PBT writes a label-keyed `scores` table alongside it. The
    ## summary `score` is the max across labels (so legacy single-objective
    ## consumers see the same value).

const
  dbFormatVersion = 2'u8
  legacyFormatVersion = 1'u8

proc newExampleDB*(path: string): ExampleDB =
  ## A database rooted at `path` (a directory; created on first save).
  ExampleDB(path: path)

# --- safe-key + little-endian primitives ---

proc safeKey(testId: string): string =
  result = newStringOfCap(testId.len)
  for c in testId:
    if c.isAlphaAscii or c.isDigit or c in {'.', '_', '-'}:
      result.add c
    else:
      result.add '_'

proc keyPath(db: ExampleDB, testId: string): string =
  db.path / (safeKey(testId) & ".bin")

proc putU8(buf: var seq[byte], x: uint8) = buf.add x
proc getU8(data: openArray[byte], pos: var int): uint8 =
  result = data[pos]; inc pos

proc putU64(buf: var seq[byte], x: uint64) =
  for i in 0 ..< 8:
    buf.add byte((x shr (8 * i)) and 0xFF'u64)
proc getU64(data: openArray[byte], pos: var int): uint64 =
  for i in 0 ..< 8:
    result = result or (uint64(data[pos + i]) shl (8 * i))
  pos += 8

proc putF64(buf: var seq[byte], x: float64) = buf.putU64(cast[uint64](x))
proc getF64(data: openArray[byte], pos: var int): float64 =
  cast[float64](getU64(data, pos))

proc putBlob(buf: var seq[byte], b: seq[byte]) =
  buf.putU64(uint64(b.len)); buf.add b
proc getBlob(data: openArray[byte], pos: var int): seq[byte] =
  let n = int(getU64(data, pos))
  result = newSeq[byte](n)
  for i in 0 ..< n: result[i] = data[pos + i]
  pos += n

proc bytesToStr(b: seq[byte]): string =
  result = newString(b.len)
  for i, v in b: result[i] = char(v)
proc strToBytes(s: string): seq[byte] =
  result = newSeq[byte](s.len)
  for i, c in s: result[i] = byte(c)

# --- read / write whole file ---

type DbContents = object
  primary: seq[seq[ChoiceNode]]
  secondary: seq[ScoredEntry]

proc putString(buf: var seq[byte], s: string) =
  buf.putU64(uint64(s.len))
  for c in s: buf.add byte(c)
proc getString(data: openArray[byte], pos: var int): string =
  let n = int(getU64(data, pos))
  result = newString(n)
  for i in 0 ..< n: result[i] = char(data[pos + i])
  pos += n

proc readContents(db: ExampleDB, testId: string): DbContents =
  let p = db.keyPath(testId)
  if not fileExists(p): return
  let raw = strToBytes(readFile(p))
  var pos = 0
  let ver = getU8(raw, pos)
  if ver != dbFormatVersion and ver != legacyFormatVersion:
    return  # unknown version — treat as empty, future-compat
  let nP = int(getU64(raw, pos))
  let nS = int(getU64(raw, pos))
  for _ in 0 ..< nP:
    result.primary.add fromBytes(getBlob(raw, pos))
  for _ in 0 ..< nS:
    let score = getF64(raw, pos)
    let cs = fromBytes(getBlob(raw, pos))
    var scores: Table[string, float]
    if ver == dbFormatVersion:
      let nLabels = int(getU64(raw, pos))
      for _ in 0 ..< nLabels:
        let k = getString(raw, pos)
        let v = getF64(raw, pos)
        scores[k] = v
    result.secondary.add (choices: cs, score: score, scores: scores)

proc writeContents(db: ExampleDB, testId: string, c: DbContents) =
  createDir(db.path)
  var buf: seq[byte]
  buf.putU8(dbFormatVersion)
  buf.putU64(uint64(c.primary.len))
  buf.putU64(uint64(c.secondary.len))
  for cs in c.primary:
    buf.putBlob(toBytes(cs))
  for entry in c.secondary:
    buf.putF64(entry.score)
    buf.putBlob(toBytes(entry.choices))
    buf.putU64(uint64(entry.scores.len))
    for k, v in entry.scores:
      buf.putString(k)
      buf.putF64(v)
  let final = db.keyPath(testId)
  let tmp = final & ".tmp"
  writeFile(tmp, bytesToStr(buf))
  moveFile(tmp, final)

# --- public API ---

proc save*(db: ExampleDB, testId: string, choices: seq[ChoiceNode],
           maxEntries = 16) =
  ## Add `choices` to the primary corpus for `testId`. If already present
  ## (by byte-equality), it is moved to the front (most-recent). If after
  ## prepending the corpus exceeds `maxEntries`, the oldest is dropped.
  var c = db.readContents(testId)
  # Dedup: drop any existing copy first, then prepend.
  var deduped: seq[seq[ChoiceNode]]
  for old in c.primary:
    if old != choices:
      deduped.add old
  c.primary = @[choices] & deduped
  if c.primary.len > maxEntries:
    c.primary.setLen(maxEntries)
  db.writeContents(testId, c)

proc loadPrimary*(db: ExampleDB, testId: string): seq[seq[ChoiceNode]] =
  ## All primary entries for `testId`, most-recent first; `@[]` if none.
  db.readContents(testId).primary

proc remove*(db: ExampleDB, testId: string, choices: seq[ChoiceNode]) =
  ## Drop a specific entry from the primary corpus (used by the engine to
  ## auto-prune stored failures that no longer reproduce).
  var c = db.readContents(testId)
  var kept: seq[seq[ChoiceNode]]
  for old in c.primary:
    if old != choices: kept.add old
  c.primary = kept
  db.writeContents(testId, c)

proc saveSecondary*(db: ExampleDB, testId: string,
                    choices: seq[ChoiceNode], score: float,
                    scores: Table[string, float] = initTable[string, float](),
                    maxEntries = 16) =
  ## Add a non-failing example with its score to the secondary corpus.
  ## The corpus is kept sorted highest-score first; entries beyond
  ## `maxEntries` are dropped (LRU-on-score eviction). `scores` is the
  ## optional multi-label score map for targeted-PBT Pareto persistence;
  ## leaving it empty keeps the legacy single-objective behavior.
  var c = db.readContents(testId)
  var deduped: seq[ScoredEntry]
  for e in c.secondary:
    if e.choices != choices: deduped.add e
  deduped.add (choices: choices, score: score, scores: scores)
  # Sort by score descending.
  for i in 1 ..< deduped.len:
    var j = i
    while j > 0 and deduped[j].score > deduped[j - 1].score:
      swap(deduped[j], deduped[j - 1])
      dec j
  if deduped.len > maxEntries:
    deduped.setLen(maxEntries)
  c.secondary = deduped
  db.writeContents(testId, c)

proc loadSecondary*(db: ExampleDB, testId: string): seq[ScoredEntry] =
  ## All secondary entries for `testId`, highest-score first; `@[]` if none.
  db.readContents(testId).secondary
