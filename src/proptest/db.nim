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
import ./choice, ./serialize  # `serialize` re-exports `binaryio`'s primitives + `DbCorrupt`

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
# `DbCorrupt`, `needBytes`, `safeLen`, `maxBlobBytes`, and the LE primitives
# are visible to this file via the `serialize` import (which re-exports
# `binaryio`). They are *not* part of the public proptest API.

proc newExampleDB*(path: string): ExampleDB =
  ## A database rooted at `path` (a directory; created on first save).
  ## Sweeps orphaned `.tmp.<pid>.<tid>` files from prior runs that crashed
  ## between `writeFile` and `moveFile` — the PID-in-name makes them safe
  ## to delete unconditionally (any crashed writer is gone).
  result = ExampleDB(path: path)
  if dirExists(path):
    for kind, p in walkDir(path, relative = false):
      if kind == pcFile and ".tmp." in p:
        try: removeFile(p)
        except OSError: discard

# --- safe-key + little-endian primitives ---

proc safeKey(testId: string): string =
  ## Map a user-supplied test id to a filesystem-safe filename. Filesystem-
  ## safe chars (`[A-Za-z0-9._-]`) pass through; any other byte becomes
  ## `%XX` (two hex digits) so the encoding is **reversible** and
  ## collision-free. The previous lossy `_`-substitution caused `"a/b"` and
  ## `"a_b"` to share the same `.bin` file — cross-test DB contamination.
  const hex = "0123456789abcdef"
  result = newStringOfCap(testId.len)
  for c in testId:
    if c.isAlphaAscii or c.isDigit or c in {'.', '-'}:
      result.add c
    else:
      result.add '%'
      result.add hex[(ord(c) shr 4) and 0xf]
      result.add hex[ord(c) and 0xf]

proc keyPath(db: ExampleDB, testId: string): string =
  db.path / (safeKey(testId) & ".bin")

# The `binaryio` primitives are already bounds-checked (every multi-byte
# read goes through `needBytes`); this file uses them directly via the
# `serialize` re-export — no wrapping layer needed.

proc bytesToStr(b: seq[byte]): string =
  ## Bit-copy a `seq[byte]` to a `string`. Used to bridge `writeFile`'s
  ## `string` argument from the binary buffer we build up.
  result = newString(b.len)
  if b.len > 0:
    copyMem(addr result[0], unsafeAddr b[0], b.len)
proc strToBytes(s: string): seq[byte] =
  ## Inverse of `bytesToStr`. `readFile` returns `string`; we treat its
  ## bytes as a raw buffer for binary decoding.
  result = newSeq[byte](s.len)
  if s.len > 0:
    copyMem(addr result[0], unsafeAddr s[0], s.len)

# --- read / write whole file ---

type DbContents = object
  primary: seq[seq[ChoiceNode]]
  secondary: seq[ScoredEntry]

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
  # 32-bit-target safety: `int(uint64)` raises RangeDefect when > high(int).
  # 64-bit hosts can't trigger this (bytesLeft div 8 << high(int64)), but
  # the guard keeps the code total.
  if nPRaw > uint64(high(int)) or nSRaw > uint64(high(int)):
    raise newException(DbCorrupt, "DB entry counts exceed int range")
  let nP = int(nPRaw); let nS = int(nSRaw)
  for _ in 0 ..< nP:
    result.primary.add fromBytes(getRawBytes(raw, pos))
  for _ in 0 ..< nS:
    let score = getF64(raw, pos)
    let cs = fromBytes(getRawBytes(raw, pos))
    var scores: Table[string, float]
    if ver == dbFormatVersion:
      let nLabelsRaw = getU64(raw, pos)
      # Each label entry is at minimum 16 bytes: u64 key-length prefix +
      # f64 value (an empty key still costs the 8-byte length-zero header).
      if nLabelsRaw > uint64(raw.len - pos) div 16'u64 or
         nLabelsRaw > uint64(high(int)):
        raise newException(DbCorrupt,
          "DB secondary entry label count " & $nLabelsRaw &
          " exceeds remaining bytes")
      for _ in 0 ..< int(nLabelsRaw):
        let k = getRawStr(raw, pos)
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
    buf.putRawBytes(toBytes(cs))
  for entry in c.secondary:
    buf.putF64(entry.score)
    buf.putRawBytes(toBytes(entry.choices))
    buf.putU64(uint64(entry.scores.len))
    for k, v in entry.scores:
      buf.putRawStr(k)
      buf.putF64(v)
  let final = db.keyPath(testId)
  # `<file>.tmp.<pid>.<tid>` — process *and* thread id together. Cross-
  # process races (e.g. `testament -j N` workers) and intra-process thread
  # races (`--threads:on`) both target a fixed `.tmp` otherwise, where one
  # writer's `writeFile` silently clobbers another's between the two
  # writers' `writeFile` + `moveFile` pairs.
  let tmp = final & ".tmp." & $getCurrentProcessId() & "." & $getThreadId()
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
  ## auto-prune stored failures that no longer reproduce). Prefer
  ## `removeMany` when dropping multiple entries — that batches into one
  ## file read-modify-write.
  var c = db.readContents(testId)
  var kept: seq[seq[ChoiceNode]]
  for old in c.primary:
    if old != choices: kept.add old
  c.primary = kept
  db.writeContents(testId, c)

proc removeMany*(db: ExampleDB, testId: string,
                 staleChoices: openArray[seq[ChoiceNode]]) =
  ## Drop every entry in `staleChoices` from the primary corpus in a single
  ## read-modify-write. Used by the engine's DB-reuse phase to prune stale
  ## entries without doing N full file rewrites.
  if staleChoices.len == 0: return
  var c = db.readContents(testId)
  var kept: seq[seq[ChoiceNode]]
  for old in c.primary:
    var isStale = false
    for s in staleChoices:
      if s == old: isStale = true; break
    if not isStale: kept.add old
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
  # Dedup-by-content with **last-wins** semantics: when the same `choices`
  # appears twice (either across existing+incoming or twice within the
  # batch), the later mention's score replaces the earlier one. Callers
  # get clean "add or update" without bookkeeping at their layer.
  var merged: seq[ScoredEntry]
  proc upsert(merged: var seq[ScoredEntry], e: ScoredEntry) =
    for i in 0 ..< merged.len:
      if merged[i].choices == e.choices:
        merged[i] = e
        return
    merged.add e
  for e in c.secondary:
    upsert(merged, e)
  for e in entries:
    upsert(merged, e)
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
