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
import ./choice, ./serialize, ./binaryio

type
  ExampleDB* = object
    path*: string

  ScoredEntry* = tuple[choices: seq[ChoiceNode], score: float,
                       scores: Table[string, float]]
    ## Single-objective `score` is preserved for back-compat; multi-objective
    ## targeted PBT writes a label-keyed `scores` table alongside it. The
    ## summary `score` is the max across labels (so legacy single-objective
    ## consumers see the same value).

  DbCorrupt* = object of CatchableError
    ## Raised by the DB readers when an on-disk file is truncated, has a
    ## bogus length field, or otherwise can't be safely decoded. Callers
    ## should treat it as "no usable corpus" — `readContents` catches it
    ## internally and continues with an empty result.

const
  dbFormatVersion = 2'u8
  legacyFormatVersion = 1'u8
  maxBlobBytes = 64 * 1024 * 1024
    ## Hard cap on any single length-prefixed blob/string in the DB file —
    ## a hostile or corrupted length field can't drive an unbounded
    ## allocation. Real recorded sequences are tiny relative to this.

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

template needBytes(data: openArray[byte], pos: int, n: int) =
  ## Raise `DbCorrupt` if `data` doesn't have `n` more bytes at `pos`. The
  ## template form keeps the cheap-path inlined in every primitive reader.
  if pos < 0 or n < 0 or pos + n > data.len:
    raise newException(DbCorrupt,
      "DB truncated: need " & $n & " bytes at pos " & $pos &
      " in a " & $data.len & "-byte file")

proc putU8(buf: var seq[byte], x: uint8) = buf.add x
proc getU8(data: openArray[byte], pos: var int): uint8 =
  needBytes(data, pos, 1)
  result = data[pos]; inc pos

# Bounds-checked wrappers around the shared LE primitives — every multi-byte
# read goes through `needBytes` first so a truncated DB file becomes a
# DbCorrupt at the entry point rather than an IndexDefect deep in a loop.
proc getU64(data: openArray[byte], pos: var int): uint64 =
  needBytes(data, pos, 8)
  binaryio.getU64(data, pos)

proc getF64(data: openArray[byte], pos: var int): float64 =
  cast[float64](getU64(data, pos))

proc safeLen(data: openArray[byte], pos: var int): int =
  ## Read a length-prefix and validate it against (a) the cap and (b) the
  ## bytes remaining in `data`. Refusing the read here means the subsequent
  ## allocation/copy is always safe.
  let raw = getU64(data, pos)
  if raw > uint64(maxBlobBytes):
    raise newException(DbCorrupt, "DB blob length " & $raw & " exceeds cap")
  let n = int(raw)
  needBytes(data, pos, n)
  n

proc putBlob(buf: var seq[byte], b: seq[byte]) =
  buf.putU64(uint64(b.len)); buf.add b
proc getBlob(data: openArray[byte], pos: var int): seq[byte] =
  let n = safeLen(data, pos)
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

proc putString(buf: var seq[byte], s: string) = buf.putRawStr s
proc getString(data: openArray[byte], pos: var int): string =
  let n = safeLen(data, pos)
  result = newString(n)
  for i in 0 ..< n: result[i] = char(data[pos + i])
  pos += n

proc parseContents(raw: openArray[byte]): DbContents =
  ## Pure decode of a DB file image — raises `DbCorrupt` on any bounds or
  ## length-cap violation. Separating this from I/O makes the failure
  ## modes testable without filesystem fixtures.
  var pos = 0
  let ver = getU8(raw, pos)
  if ver != dbFormatVersion and ver != legacyFormatVersion:
    raise newException(DbCorrupt,
      "unknown DB format version " & $ver & " (supported: " &
      $legacyFormatVersion & ", " & $dbFormatVersion & ")")
  let nPRaw = getU64(raw, pos)
  let nSRaw = getU64(raw, pos)
  # Per-entry minimum byte cost is a u64 length-prefix; a count that can't
  # possibly fit even that many length-prefixes in the remaining bytes is
  # certainly corrupt.
  let bytesLeft = uint64(raw.len - pos)
  if nPRaw > bytesLeft div 8'u64 or nSRaw > bytesLeft div 8'u64:
    raise newException(DbCorrupt,
      "DB entry counts (" & $nPRaw & " primary + " & $nSRaw &
      " secondary) exceed remaining file size")
  let nP = int(nPRaw); let nS = int(nSRaw)
  for _ in 0 ..< nP:
    result.primary.add fromBytes(getBlob(raw, pos))
  for _ in 0 ..< nS:
    let score = getF64(raw, pos)
    let cs = fromBytes(getBlob(raw, pos))
    var scores: Table[string, float]
    if ver == dbFormatVersion:
      let nLabelsRaw = getU64(raw, pos)
      if nLabelsRaw > uint64(raw.len - pos):
        raise newException(DbCorrupt,
          "DB secondary entry label count " & $nLabelsRaw &
          " exceeds remaining bytes")
      for _ in 0 ..< int(nLabelsRaw):
        let k = getString(raw, pos)
        let v = getF64(raw, pos)
        scores[k] = v
    result.secondary.add (choices: cs, score: score, scores: scores)

proc readContents(db: ExampleDB, testId: string): DbContents =
  let p = db.keyPath(testId)
  if not fileExists(p): return
  var raw: seq[byte]
  try:
    raw = strToBytes(readFile(p))
  except IOError as e:
    stderr.writeLine "proptest: cannot read example DB at " & p & ": " & e.msg
    return
  try:
    result = parseContents(raw)
  except DbCorrupt as e:
    stderr.writeLine "proptest: example DB at " & p &
                     " appears corrupted; ignoring (" & e.msg & ")"
    result = DbContents()
  except IndexDefect, RangeDefect:
    # Defensive: a bug in a primitive that bypassed `needBytes` would still
    # land here; treat the same as DbCorrupt rather than crash the run.
    stderr.writeLine "proptest: example DB at " & p &
                     " hit a decode panic; ignoring"
    result = DbContents()

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
                    entries: openArray[ScoredEntry],
                    maxEntries = 16) =
  ## Persist a batch of non-failing examples (typically the engine's Pareto
  ## front) to the secondary corpus in one read-modify-write. The corpus is
  ## kept sorted highest-score first; entries beyond `maxEntries` are dropped
  ## (LRU-on-score eviction). Saving N entries with the old single-entry API
  ## was O(N) full DB cycles; the batch form is one.
  var c = db.readContents(testId)
  # Dedup-by-content against existing entries: any new entry replaces an old
  # one with identical `choices`. Within the incoming batch we keep the last
  # mention so callers get "add or update" semantics for repeated keys.
  var dedupChoices: seq[seq[ChoiceNode]]
  var merged: seq[ScoredEntry]
  for e in c.secondary:
    var supersededBy = -1
    for i, ne in entries:
      if ne.choices == e.choices: supersededBy = i
    if supersededBy < 0:
      merged.add e
  for e in entries:
    var alreadyAdded = false
    for m in merged:
      if m.choices == e.choices:
        alreadyAdded = true
        break
    if not alreadyAdded:
      merged.add e
  # Sort by score descending (stable insertion sort — N ≤ a couple dozen).
  for i in 1 ..< merged.len:
    var j = i
    while j > 0 and merged[j].score > merged[j - 1].score:
      swap(merged[j], merged[j - 1])
      dec j
  if merged.len > maxEntries:
    merged.setLen(maxEntries)
  c.secondary = merged
  db.writeContents(testId, c)

proc loadSecondary*(db: ExampleDB, testId: string): seq[ScoredEntry] =
  ## All secondary entries for `testId`, highest-score first; `@[]` if none.
  db.readContents(testId).secondary
