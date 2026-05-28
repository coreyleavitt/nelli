## The example database — "remembers your bugs."
##
## `ExampleDatabase` is a closure-record (a struct of proc fields), not an
## inheritance hierarchy: factories like `directoryBasedDatabase(path)`,
## `inMemoryDatabase()`, `multiplexedDatabase(local, shared)`, and
## `readOnlyDatabase(inner)` each return a value whose closures capture
## the backend state. The engine and the user-facing wrapper procs
## (`save`, `loadPrimary`, etc.) only see the record — they don't know
## or care which backend they're talking to.
##
## **Built-in backends**
##
## * **`directoryBasedDatabase(path)`** — one file `<path>/<safeKey>.bin`
##   per test id. Atomic writes (tmp + rename). Survives crashes mid-write.
##   This is the default and what `newExampleDB(path)` returns.
## * **`inMemoryDatabase()`** — a per-process table. Useful for testing the
##   engine and for ephemeral CI runs.
## * **`multiplexedDatabase(primary, secondary)`** — reads union both;
##   writes to `primary`. Lets a CI run pull from a shared reference
##   corpus (read-only mount) and write back to a local one.
## * **`readOnlyDatabase(inner)`** — wraps any backend so `save` /
##   `remove` / `saveSecondary` raise `DbError`. Useful for the
##   reference-corpus half of a multiplex.
##
## On-disk layout (directory backend), one file per test id:
##   [version: u8 = 2]
##   [nPrimary: u64]
##   [nSecondary: u64]
##   [primary entries: for each, u64 size then `size` bytes of toBytes(seq)]
##   [secondary entries: for each, f64 score then u64 size then `size` bytes,
##                       then u64 label-count + (u64 keylen + str + f64)*]
##
## Writes are atomic: contents land in `<file>.tmp.<pid>.<tid>` then
## `moveFile` renames it over the target so a crash during write can't
## half-corrupt the entry.

import std/[os, strutils, tables]
import ./choice, ./serialize  # `serialize` re-exports `binaryio`'s primitives + `DbCorrupt`

type
  DbError* = object of CatchableError
    ## Raised by `readOnlyDatabase` on write attempts; backends may also
    ## raise this for irrecoverable I/O conditions. The engine catches
    ## these and surfaces them via `Report.dbErrors` (or, with
    ## `Settings.strictDb = true`, propagates as a fatal report).

  ScoredEntry* = tuple[choices: seq[ChoiceNode], score: float,
                       scores: Table[string, float]]
    ## Single-objective `score` is preserved for back-compat; multi-objective
    ## targeted PBT writes a label-keyed `scores` table alongside it. The
    ## summary `score` is the max across labels (so legacy single-objective
    ## consumers see the same value).

  ExampleDatabase* = object
    ## A closure-record interface to an example-DB backend. Procs are
    ## bound once at factory time and carry their backend state in the
    ## closure environment. The record is a value type (copies are cheap;
    ## the closures themselves are reference-typed).
    saveImpl*:           proc(testId: string, choices: seq[ChoiceNode],
                              maxEntries: int) {.closure.}
    loadPrimaryImpl*:    proc(testId: string): seq[seq[ChoiceNode]] {.closure.}
    removeImpl*:         proc(testId: string, choices: seq[ChoiceNode]) {.closure.}
    removeManyImpl*:     proc(testId: string,
                              staleChoices: seq[seq[ChoiceNode]]) {.closure.}
    saveSecondaryImpl*:  proc(testId: string, entries: seq[ScoredEntry],
                              maxEntries: int) {.closure.}
    loadSecondaryImpl*:  proc(testId: string): seq[ScoredEntry] {.closure.}

  ExampleDB* = ExampleDatabase
    ## Legacy alias — `ExampleDB` predates the closure-record refactor.
    ## New code should use `ExampleDatabase`.

# --- public wrapper procs (one per closure field) ----------------------------
#
# These keep call-site syntax (`db.save(testId, choices)`) unchanged from
# before the refactor, and give the engine a single set of names regardless
# of which backend is plugged in.

proc save*(db: ExampleDatabase, testId: string, choices: seq[ChoiceNode],
           maxEntries = 16) =
  db.saveImpl(testId, choices, maxEntries)

proc loadPrimary*(db: ExampleDatabase, testId: string): seq[seq[ChoiceNode]] =
  db.loadPrimaryImpl(testId)

proc remove*(db: ExampleDatabase, testId: string,
             choices: seq[ChoiceNode]) =
  db.removeImpl(testId, choices)

proc removeMany*(db: ExampleDatabase, testId: string,
                 staleChoices: openArray[seq[ChoiceNode]]) =
  ## Wrapper converts `openArray` callers to the closure's `seq` param —
  ## closures can't take `openArray`, so the wrapper layer pays the copy.
  db.removeManyImpl(testId, @staleChoices)

proc saveSecondary*(db: ExampleDatabase, testId: string,
                    entries: openArray[ScoredEntry], maxEntries = 16) =
  db.saveSecondaryImpl(testId, @entries, maxEntries)

proc loadSecondary*(db: ExampleDatabase, testId: string): seq[ScoredEntry] =
  db.loadSecondaryImpl(testId)

# --- shared serialization layer (used by directory backend) ------------------

const
  dbFormatVersion = 2'u8
  legacyFormatVersion = 1'u8

type DbContents = object
  primary: seq[seq[ChoiceNode]]
  secondary: seq[ScoredEntry]

proc parseContents(raw: openArray[byte]): DbContents =
  var pos = 0
  let ver = getU8(raw, pos)
  if ver != dbFormatVersion and ver != legacyFormatVersion:
    raise newException(DbCorrupt,
      "unknown DB format version " & $ver & " (supported: " &
      $legacyFormatVersion & ", " & $dbFormatVersion & ")")
  let nPRaw = getU64(raw, pos)
  let nSRaw = getU64(raw, pos)
  let bytesLeft = uint64(raw.len - pos)
  if nPRaw > bytesLeft div 8'u64 or nSRaw > bytesLeft div 8'u64:
    raise newException(DbCorrupt,
      "DB entry counts (" & $nPRaw & " primary + " & $nSRaw &
      " secondary) exceed remaining file size")
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

proc encodeContents(c: DbContents): seq[byte] =
  result.putU8(dbFormatVersion)
  result.putU64(uint64(c.primary.len))
  result.putU64(uint64(c.secondary.len))
  for cs in c.primary:
    result.putRawBytes(toBytes(cs))
  for entry in c.secondary:
    result.putF64(entry.score)
    result.putRawBytes(toBytes(entry.choices))
    result.putU64(uint64(entry.scores.len))
    for k, v in entry.scores:
      result.putRawStr(k)
      result.putF64(v)

proc applySave(c: var DbContents, choices: seq[ChoiceNode], maxEntries: int) =
  var deduped: seq[seq[ChoiceNode]]
  for old in c.primary:
    if old != choices: deduped.add old
  c.primary = @[choices] & deduped
  if c.primary.len > maxEntries:
    c.primary.setLen(maxEntries)

proc applyRemoveMany(c: var DbContents, stale: seq[seq[ChoiceNode]]) =
  var kept: seq[seq[ChoiceNode]]
  for old in c.primary:
    var isStale = false
    for s in stale:
      if s == old: isStale = true; break
    if not isStale: kept.add old
  c.primary = kept

proc applySaveSecondary(c: var DbContents, entries: seq[ScoredEntry],
                        maxEntries: int) =
  var merged: seq[ScoredEntry]
  proc upsert(merged: var seq[ScoredEntry], e: ScoredEntry) =
    for i in 0 ..< merged.len:
      if merged[i].choices == e.choices:
        merged[i] = e
        return
    merged.add e
  for e in c.secondary: upsert(merged, e)
  for e in entries:     upsert(merged, e)
  for i in 1 ..< merged.len:
    var j = i
    while j > 0 and merged[j].score > merged[j - 1].score:
      swap(merged[j], merged[j - 1])
      dec j
  if merged.len > maxEntries:
    merged.setLen(maxEntries)
  c.secondary = merged

# --- directory backend -------------------------------------------------------

proc bytesToStr(b: seq[byte]): string =
  result = newString(b.len)
  if b.len > 0:
    copyMem(addr result[0], unsafeAddr b[0], b.len)
proc strToBytes(s: string): seq[byte] =
  result = newSeq[byte](s.len)
  if s.len > 0:
    copyMem(addr result[0], unsafeAddr s[0], s.len)

proc safeKey(testId: string): string =
  const hex = "0123456789abcdef"
  result = newStringOfCap(testId.len)
  for c in testId:
    if c.isAlphaAscii or c.isDigit or c in {'.', '-'}:
      result.add c
    else:
      result.add '%'
      result.add hex[(ord(c) shr 4) and 0xf]
      result.add hex[ord(c) and 0xf]

proc directoryBasedDatabase*(path: string): ExampleDatabase =
  ## File-backed DB rooted at `path` (created on first save). One file per
  ## test id (`<path>/<safeKey>.bin`); writes are atomic via tmp + rename.
  ## Sweeps orphaned `.tmp.<pid>.<tid>` files from prior crashes.
  if dirExists(path):
    for kind, p in walkDir(path, relative = false):
      if kind == pcFile and ".tmp." in p:
        try: removeFile(p)
        except OSError: discard

  proc keyPath(testId: string): string = path / (safeKey(testId) & ".bin")

  proc readContents(testId: string): DbContents =
    let p = keyPath(testId)
    if not fileExists(p): return
    var raw: seq[byte]
    try:
      raw = strToBytes(readFile(p))
    except IOError as e:
      raise newException(DbError,
        "cannot read example DB at " & p & ": " & e.msg)
    try:
      result = parseContents(raw)
    except DbCorrupt as e:
      raise newException(DbError,
        "example DB at " & p & " is corrupted (" & e.msg & ")")
    except IndexDefect, RangeDefect:
      raise newException(DbError,
        "example DB at " & p & " hit a decode panic")

  proc writeContents(testId: string, c: DbContents) =
    createDir(path)
    let buf = encodeContents(c)
    let final = keyPath(testId)
    let tmp = final & ".tmp." & $getCurrentProcessId() & "." & $getThreadId()
    writeFile(tmp, bytesToStr(buf))
    moveFile(tmp, final)

  result.saveImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    var c: DbContents
    try: c = readContents(testId)
    except DbError: discard   # start fresh on corrupted reads when writing
    applySave(c, choices, maxEntries)
    writeContents(testId, c)
  result.loadPrimaryImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    readContents(testId).primary
  result.removeImpl = proc(testId: string, choices: seq[ChoiceNode]) =
    var c: DbContents
    try: c = readContents(testId)
    except DbError: discard
    applyRemoveMany(c, @[choices])
    writeContents(testId, c)
  result.removeManyImpl = proc(testId: string,
                               stale: seq[seq[ChoiceNode]]) =
    if stale.len == 0: return
    var c: DbContents
    try: c = readContents(testId)
    except DbError: discard
    applyRemoveMany(c, stale)
    writeContents(testId, c)
  result.saveSecondaryImpl = proc(testId: string,
                                  entries: seq[ScoredEntry],
                                  maxEntries: int) =
    var c: DbContents
    try: c = readContents(testId)
    except DbError: discard
    applySaveSecondary(c, entries, maxEntries)
    writeContents(testId, c)
  result.loadSecondaryImpl = proc(testId: string): seq[ScoredEntry] =
    readContents(testId).secondary

proc newExampleDB*(path: string): ExampleDatabase =
  ## Legacy constructor — delegates to `directoryBasedDatabase(path)`.
  directoryBasedDatabase(path)

# --- in-memory backend -------------------------------------------------------

proc inMemoryDatabase*(): ExampleDatabase =
  ## Process-local DB held in a `Table`. Useful for engine self-tests and
  ## for ephemeral CI runs where persistence isn't wanted.
  var primary  = initTable[string, seq[seq[ChoiceNode]]]()
  var secondary = initTable[string, seq[ScoredEntry]]()

  result.saveImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    var c = DbContents(primary: primary.getOrDefault(testId),
                       secondary: secondary.getOrDefault(testId))
    applySave(c, choices, maxEntries)
    primary[testId] = c.primary
  result.loadPrimaryImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    primary.getOrDefault(testId)
  result.removeImpl = proc(testId: string, choices: seq[ChoiceNode]) =
    var c = DbContents(primary: primary.getOrDefault(testId))
    applyRemoveMany(c, @[choices])
    primary[testId] = c.primary
  result.removeManyImpl = proc(testId: string, stale: seq[seq[ChoiceNode]]) =
    if stale.len == 0: return
    var c = DbContents(primary: primary.getOrDefault(testId))
    applyRemoveMany(c, stale)
    primary[testId] = c.primary
  result.saveSecondaryImpl = proc(testId: string, entries: seq[ScoredEntry], maxEntries: int) =
    var c = DbContents(secondary: secondary.getOrDefault(testId))
    applySaveSecondary(c, entries, maxEntries)
    secondary[testId] = c.secondary
  result.loadSecondaryImpl = proc(testId: string): seq[ScoredEntry] =
    secondary.getOrDefault(testId)

# --- multiplexed backend -----------------------------------------------------

proc multiplexedDatabase*(primaryBackend, secondaryBackend: ExampleDatabase): ExampleDatabase =
  ## Reads union both backends; writes to `primaryBackend` only. Use case:
  ## CI run with a shared read-only reference corpus mounted as
  ## `secondaryBackend` and a writable local corpus as `primaryBackend`.
  ## A bug found in the primary is added there; reference-corpus bugs
  ## stay frozen in the shared store.
  let p = primaryBackend
  let s = secondaryBackend
  result.saveImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    p.saveImpl(testId, choices, maxEntries)
  result.loadPrimaryImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    result = p.loadPrimaryImpl(testId)
    for entry in s.loadPrimaryImpl(testId):
      if entry notin result: result.add entry
  result.removeImpl = proc(testId: string, choices: seq[ChoiceNode]) =
    p.removeImpl(testId, choices)
  result.removeManyImpl = proc(testId: string, stale: seq[seq[ChoiceNode]]) =
    p.removeManyImpl(testId, stale)
  result.saveSecondaryImpl = proc(testId: string, entries: seq[ScoredEntry], maxEntries: int) =
    p.saveSecondaryImpl(testId, entries, maxEntries)
  result.loadSecondaryImpl = proc(testId: string): seq[ScoredEntry] =
    result = p.loadSecondaryImpl(testId)
    for entry in s.loadSecondaryImpl(testId):
      var seen = false
      for r in result:
        if r.choices == entry.choices: seen = true; break
      if not seen: result.add entry

# --- read-only wrapper -------------------------------------------------------

proc readOnlyDatabase*(inner: ExampleDatabase): ExampleDatabase =
  ## Wraps any backend so writes raise `DbError`. Intended for the
  ## reference-corpus half of a `multiplexedDatabase`.
  let i = inner
  result.saveImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    raise newException(DbError, "save to read-only example database")
  result.loadPrimaryImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    i.loadPrimaryImpl(testId)
  result.removeImpl = proc(testId: string, choices: seq[ChoiceNode]) =
    raise newException(DbError, "remove from read-only example database")
  result.removeManyImpl = proc(testId: string, stale: seq[seq[ChoiceNode]]) =
    raise newException(DbError, "removeMany on read-only example database")
  result.saveSecondaryImpl = proc(testId: string, entries: seq[ScoredEntry], maxEntries: int) =
    raise newException(DbError, "saveSecondary on read-only example database")
  result.loadSecondaryImpl = proc(testId: string): seq[ScoredEntry] =
    i.loadSecondaryImpl(testId)
