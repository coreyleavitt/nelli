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
##   `remove` / `saveSecondary` / `saveCorpus` raise `DbError`. Useful
##   for the reference-corpus half of a multiplex.
##
## **Three independent sections per test id** — `primary` (regression
## witnesses; `dbReusePhase` replays and prunes-on-pass/reject),
## `secondary` (scored Pareto-front entries for targeted PBT; never
## touched by `dbReusePhase`), and `corpus` (coverage-guided fuzz
## seeds; also never touched by `dbReusePhase` — see below). The
## `corpus` section (F1, RFC-chapulin-hardening) exists because the
## `primary` section's contract is "replay and discard once it no
## longer falsifies" — correct for regression witnesses, but WRONG for
## a fuzzer's coverage corpus: a coverage seed that currently passes
## still exercised a useful path and earns its keep across runs. Prior
## to F1 the fuzz loop (`fuzz.nim`) persisted its corpus into
## `primary` under its own testId, which happened to dodge
## `dbReusePhase`'s pruning only because that phase reads a
## *different* testId (`Settings.testId`) by convention — nothing
## structural prevented the two roles from colliding on one testId
## and losing the corpus to prune-on-pass. `saveCorpus`/`loadCorpus`
## give the fuzzer its own section with no prune path at all, so the
## non-pruning guarantee holds even if a corpus testId and a
## regression testId are ever the same string.
##
## **Per-primary-entry metadata (F6, RFC-chapulin-hardening).** Each
## `primary` entry may carry an opaque `Table[string, string]` alongside
## its choice-seq — a slot for a caller to attach descriptive tags to a
## regression witness (e.g. a crash message, an origin/verdict label)
## without inventing a side-channel keyed on the choice-seq bytes. It
## mirrors `secondary`'s per-entry label table but is string-valued
## (primary entries are witnesses, not scored candidates — `secondary`
## already owns the numeric-score use case). `save(db, testId, choices)`
## is unchanged and defaults an entry's metadata to empty;
## `save(db, testId, choices, meta)` attaches/overwrites it;
## `loadPrimary` is unchanged (choices only); `loadPrimaryWithMeta`
## returns the same entries paired with their metadata. Dedup semantics
## (below) are STICKY: a plain `save()` re-saving an existing choice-seq
## carries its stored metadata forward rather than clearing it — only an
## explicit `save(..., meta)` (non-empty `meta`) overwrites. Passing an
## explicit empty table behaves identically to omitting `meta`; there is
## no dedicated "clear metadata" op — remove + re-save the entry instead.
##
## On-disk layout (directory backend), one file per test id:
##   [version: u8 = 4]
##   [nPrimary: u64]
##   [nSecondary: u64]
##   [primary entries: for each, u64 size then `size` bytes of toBytes(seq),
##                     then (version >= 4) u64 meta-count +
##                     (u64 keylen + str + u64 vallen + str)*]
##   [secondary entries: for each, f64 score then u64 size then `size` bytes,
##                       then u64 label-count + (u64 keylen + str + f64)*]
##   [nCorpus: u64]                                        -- version >= 3 only
##   [corpus entries: for each, u64 size then `size` bytes of toBytes(seq)]
##
## Versions 1 (legacy) and 2 lack the corpus section; reading either
## yields an empty `corpus`. Versions 1-3 lack per-primary-entry
## metadata; reading any of them yields an empty metadata table for
## every primary entry. Any write re-encodes at the current version, so
## an old file is transparently upgraded to carry a (possibly
## still-empty) corpus section and per-entry metadata on first save.
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

  PrimaryEntry* = tuple[choices: seq[ChoiceNode], meta: Table[string, string]]
    ## F6 (RFC-chapulin-hardening): a `primary` regression-witness entry
    ## paired with its opaque string-keyed metadata (empty by default).
    ## Returned by `loadPrimaryWithMeta`; see the module doc's F6 section.

  ExampleDatabase* = object
    ## A closure-record interface to an example-DB backend. Procs are
    ## bound once at factory time and carry their backend state in the
    ## closure environment. The record is a value type (copies are cheap;
    ## the closures themselves are reference-typed).
    saveImpl*:           proc(testId: string, choices: seq[ChoiceNode],
                              maxEntries: int) {.closure.}
    loadPrimaryImpl*:    proc(testId: string): seq[seq[ChoiceNode]] {.closure.}
    saveWithMetaImpl*:   proc(testId: string, choices: seq[ChoiceNode],
                              meta: Table[string, string],
                              maxEntries: int) {.closure.}
    loadPrimaryWithMetaImpl*: proc(testId: string): seq[PrimaryEntry] {.closure.}
    removeImpl*:         proc(testId: string, choices: seq[ChoiceNode]) {.closure.}
    removeManyImpl*:     proc(testId: string,
                              staleChoices: seq[seq[ChoiceNode]]) {.closure.}
    saveSecondaryImpl*:  proc(testId: string, entries: seq[ScoredEntry],
                              maxEntries: int) {.closure.}
    loadSecondaryImpl*:  proc(testId: string): seq[ScoredEntry] {.closure.}
    saveCorpusImpl*:     proc(testId: string, choices: seq[ChoiceNode],
                              maxEntries: int) {.closure.}
    loadCorpusImpl*:     proc(testId: string): seq[seq[ChoiceNode]] {.closure.}

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

proc save*(db: ExampleDatabase, testId: string, choices: seq[ChoiceNode],
           meta: Table[string, string], maxEntries = 16) =
  ## F6 (RFC-chapulin-hardening): overload that attaches/overwrites
  ## per-entry metadata alongside `choices`. A non-empty `meta` replaces
  ## any metadata already stored for this exact choice-seq; an empty
  ## `meta` behaves like the 4-arg `save` above (existing metadata, if
  ## any, carries forward — see the module doc's F6 section).
  db.saveWithMetaImpl(testId, choices, meta, maxEntries)

proc loadPrimary*(db: ExampleDatabase, testId: string): seq[seq[ChoiceNode]] =
  db.loadPrimaryImpl(testId)

proc loadPrimaryWithMeta*(db: ExampleDatabase, testId: string): seq[PrimaryEntry] =
  ## F6 (RFC-chapulin-hardening): `loadPrimary`'s entries paired with
  ## their per-entry metadata, same order (most-recent first, per F5).
  db.loadPrimaryWithMetaImpl(testId)

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

proc saveCorpus*(db: ExampleDatabase, testId: string, choices: seq[ChoiceNode],
                 maxEntries = 256) =
  ## F1 (RFC-chapulin-hardening): persist a coverage-corpus entry. Lives in
  ## its own section — `dbReusePhase` never reads or prunes it, so a seed
  ## kept purely for the coverage it exercises survives across runs even
  ## after it stops falsifying anything. `maxEntries` default (256) mirrors
  ## `FuzzSettings.corpusLimit`'s "0 -> 256" convention.
  db.saveCorpusImpl(testId, choices, maxEntries)

proc loadCorpus*(db: ExampleDatabase, testId: string): seq[seq[ChoiceNode]] =
  db.loadCorpusImpl(testId)

# --- shared serialization layer (used by directory backend) ------------------

const
  dbFormatVersion = 4'u8
  primaryMetaFormatVersion = 4'u8
    ## Per-primary-entry metadata (F6) was added at version 4. Versions 1-3
    ## (all still readable) predate it and parse every primary entry to an
    ## empty metadata table.
  corpusFormatVersion = 3'u8
    ## The corpus section (F1) was added at version 3. Versions 1 and 2
    ## (both still readable) predate it and parse to an empty `corpus`.
  legacyFormatVersion = 1'u8
  secondaryLabelsFormatVersion = 2'u8
    ## Versions >= 2 carry the per-secondary-entry label table.

type DbContents = object
  primary: seq[PrimaryEntry]
  secondary: seq[ScoredEntry]
  corpus: seq[seq[ChoiceNode]]

proc parseContents(raw: openArray[byte]): DbContents =
  var pos = 0
  let ver = getU8(raw, pos)
  if ver != legacyFormatVersion and ver != secondaryLabelsFormatVersion and
     ver != corpusFormatVersion and ver != dbFormatVersion:
    raise newException(DbCorrupt,
      "unknown DB format version " & $ver & " (supported: " &
      $legacyFormatVersion & ", " & $secondaryLabelsFormatVersion & ", " &
      $corpusFormatVersion & ", " & $dbFormatVersion & ")")
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
    let cs = fromBytes(getRawBytes(raw, pos))
    var meta: Table[string, string]
    if ver >= primaryMetaFormatVersion:
      let nMetaRaw = getU64(raw, pos)
      if nMetaRaw > uint64(raw.len - pos) div 16'u64 or
         nMetaRaw > uint64(high(int)):
        raise newException(DbCorrupt,
          "DB primary entry metadata count " & $nMetaRaw &
          " exceeds remaining bytes")
      for _ in 0 ..< int(nMetaRaw):
        let k = getRawStr(raw, pos)
        let v = getRawStr(raw, pos)
        meta[k] = v
    result.primary.add (choices: cs, meta: meta)
  for _ in 0 ..< nS:
    let score = getF64(raw, pos)
    let cs = fromBytes(getRawBytes(raw, pos))
    var scores: Table[string, float]
    if ver >= secondaryLabelsFormatVersion:
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
  if ver >= corpusFormatVersion:
    let nCRaw = getU64(raw, pos)
    if nCRaw > uint64(raw.len - pos) div 8'u64 or nCRaw > uint64(high(int)):
      raise newException(DbCorrupt,
        "DB corpus entry count " & $nCRaw & " exceeds remaining file size")
    for _ in 0 ..< int(nCRaw):
      result.corpus.add fromBytes(getRawBytes(raw, pos))

proc encodeContents(c: DbContents): seq[byte] =
  result.putU8(dbFormatVersion)
  result.putU64(uint64(c.primary.len))
  result.putU64(uint64(c.secondary.len))
  for entry in c.primary:
    result.putRawBytes(toBytes(entry.choices))
    result.putU64(uint64(entry.meta.len))
    for k, v in entry.meta:
      result.putRawStr(k)
      result.putRawStr(v)
  for entry in c.secondary:
    result.putF64(entry.score)
    result.putRawBytes(toBytes(entry.choices))
    result.putU64(uint64(entry.scores.len))
    for k, v in entry.scores:
      result.putRawStr(k)
      result.putF64(v)
  result.putU64(uint64(c.corpus.len))
  for cs in c.corpus:
    result.putRawBytes(toBytes(cs))

proc dedupPrepend(list: seq[seq[ChoiceNode]], choices: seq[ChoiceNode],
                  maxEntries: int): seq[seq[ChoiceNode]] =
  ## Shared "keep most-recent, deduped, capped" admission policy behind both
  ## `applySave` (primary) and `applySaveCorpus` (F1 corpus section).
  ##
  ## F5 (RFC-chapulin-hardening) — INSERTION-ORDER CONTRACT (was implicit):
  ## the list is stored **newest-first**. A save (1) drops any existing entry
  ## equal to `choices` (structural `!=`), (2) PREPENDS the new entry at index
  ## 0, and (3) truncates the TAIL to `maxEntries`. Consequences a caller can
  ## rely on:
  ##   * the most-recently-saved entry is always `result[0]`; on reload,
  ##     `parseContents` preserves this order, so entries come back in
  ##     REVERSE insertion order (most-recent first). `dbReusePhase`
  ##     (`engine/phases.nim`) depends on this — it replays the freshest
  ##     regression witnesses first.
  ##   * a re-save of an existing entry MOVES it to the front (dedup + prepend),
  ##     refreshing its recency rather than duplicating it.
  ##   * the cap evicts the OLDEST entries (the tail), never the newest — so a
  ##     hot recent corpus is never dropped in favor of stale history.
  var deduped: seq[seq[ChoiceNode]]
  for old in list:
    if old != choices: deduped.add old
  result = @[choices] & deduped
  if result.len > maxEntries:
    result.setLen(maxEntries)   # truncate the TAIL → evicts oldest, keeps newest

proc dedupPrependEntry(list: seq[PrimaryEntry], choices: seq[ChoiceNode],
                       meta: Table[string, string],
                       maxEntries: int): seq[PrimaryEntry] =
  ## `dedupPrepend`'s F5 admission policy (dedup + prepend + cap-the-tail),
  ## specialized to `primary`'s `PrimaryEntry` (F6): metadata is STICKY on
  ## re-save. An empty `meta` (the plain `save()` path) carries the
  ## existing entry's metadata forward instead of clearing it; a non-empty
  ## `meta` (the `save(..., meta)` overload) overwrites it. See the module
  ## doc's F6 section.
  var carried = meta
  var deduped: seq[PrimaryEntry]
  for old in list:
    if old.choices != choices:
      deduped.add old
    elif meta.len == 0:
      carried = old.meta
  result = @[(choices: choices, meta: carried)] & deduped
  if result.len > maxEntries:
    result.setLen(maxEntries)

proc applySave(c: var DbContents, choices: seq[ChoiceNode], maxEntries: int) =
  c.primary = dedupPrependEntry(c.primary, choices, initTable[string, string](),
                                maxEntries)

proc applySaveWithMeta(c: var DbContents, choices: seq[ChoiceNode],
                       meta: Table[string, string], maxEntries: int) =
  c.primary = dedupPrependEntry(c.primary, choices, meta, maxEntries)

proc applySaveCorpus(c: var DbContents, choices: seq[ChoiceNode],
                     maxEntries: int) =
  c.corpus = dedupPrepend(c.corpus, choices, maxEntries)

proc applyRemoveMany(c: var DbContents, stale: seq[seq[ChoiceNode]]) =
  var kept: seq[PrimaryEntry]
  for old in c.primary:
    var isStale = false
    for s in stale:
      if s == old.choices: isStale = true; break
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
    for entry in readContents(testId).primary: result.add entry.choices
  result.saveWithMetaImpl = proc(testId: string, choices: seq[ChoiceNode],
                                 meta: Table[string, string], maxEntries: int) =
    var c: DbContents
    try: c = readContents(testId)
    except DbError: discard   # start fresh on corrupted reads when writing
    applySaveWithMeta(c, choices, meta, maxEntries)
    writeContents(testId, c)
  result.loadPrimaryWithMetaImpl = proc(testId: string): seq[PrimaryEntry] =
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
  result.saveCorpusImpl = proc(testId: string, choices: seq[ChoiceNode],
                               maxEntries: int) =
    var c: DbContents
    try: c = readContents(testId)
    except DbError: discard   # start fresh on corrupted reads when writing
    applySaveCorpus(c, choices, maxEntries)
    writeContents(testId, c)
  result.loadCorpusImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    readContents(testId).corpus

proc newExampleDB*(path: string): ExampleDatabase =
  ## Legacy constructor — delegates to `directoryBasedDatabase(path)`.
  directoryBasedDatabase(path)

# --- in-memory backend -------------------------------------------------------

proc inMemoryDatabase*(): ExampleDatabase =
  ## Process-local DB held in a `Table`. Useful for engine self-tests and
  ## for ephemeral CI runs where persistence isn't wanted.
  var primary  = initTable[string, seq[PrimaryEntry]]()
  var secondary = initTable[string, seq[ScoredEntry]]()
  var corpus = initTable[string, seq[seq[ChoiceNode]]]()

  result.saveImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    var c = DbContents(primary: primary.getOrDefault(testId),
                       secondary: secondary.getOrDefault(testId))
    applySave(c, choices, maxEntries)
    primary[testId] = c.primary
  result.loadPrimaryImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    for entry in primary.getOrDefault(testId): result.add entry.choices
  result.saveWithMetaImpl = proc(testId: string, choices: seq[ChoiceNode],
                                 meta: Table[string, string], maxEntries: int) =
    var c = DbContents(primary: primary.getOrDefault(testId))
    applySaveWithMeta(c, choices, meta, maxEntries)
    primary[testId] = c.primary
  result.loadPrimaryWithMetaImpl = proc(testId: string): seq[PrimaryEntry] =
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
  result.saveCorpusImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    var c = DbContents(corpus: corpus.getOrDefault(testId))
    applySaveCorpus(c, choices, maxEntries)
    corpus[testId] = c.corpus
  result.loadCorpusImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    corpus.getOrDefault(testId)

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
  result.saveWithMetaImpl = proc(testId: string, choices: seq[ChoiceNode],
                                 meta: Table[string, string], maxEntries: int) =
    p.saveWithMetaImpl(testId, choices, meta, maxEntries)
  result.loadPrimaryWithMetaImpl = proc(testId: string): seq[PrimaryEntry] =
    result = p.loadPrimaryWithMetaImpl(testId)
    for entry in s.loadPrimaryWithMetaImpl(testId):
      var seen = false
      for r in result:
        if r.choices == entry.choices: seen = true; break
      if not seen: result.add entry
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
  result.saveCorpusImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    p.saveCorpusImpl(testId, choices, maxEntries)
  result.loadCorpusImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    result = p.loadCorpusImpl(testId)
    for entry in s.loadCorpusImpl(testId):
      if entry notin result: result.add entry

# --- read-only wrapper -------------------------------------------------------

proc readOnlyDatabase*(inner: ExampleDatabase): ExampleDatabase =
  ## Wraps any backend so writes raise `DbError`. Intended for the
  ## reference-corpus half of a `multiplexedDatabase`.
  let i = inner
  result.saveImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    raise newException(DbError, "save to read-only example database")
  result.loadPrimaryImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    i.loadPrimaryImpl(testId)
  result.saveWithMetaImpl = proc(testId: string, choices: seq[ChoiceNode],
                                 meta: Table[string, string], maxEntries: int) =
    raise newException(DbError, "save to read-only example database")
  result.loadPrimaryWithMetaImpl = proc(testId: string): seq[PrimaryEntry] =
    i.loadPrimaryWithMetaImpl(testId)
  result.removeImpl = proc(testId: string, choices: seq[ChoiceNode]) =
    raise newException(DbError, "remove from read-only example database")
  result.removeManyImpl = proc(testId: string, stale: seq[seq[ChoiceNode]]) =
    raise newException(DbError, "removeMany on read-only example database")
  result.saveSecondaryImpl = proc(testId: string, entries: seq[ScoredEntry], maxEntries: int) =
    raise newException(DbError, "saveSecondary on read-only example database")
  result.loadSecondaryImpl = proc(testId: string): seq[ScoredEntry] =
    i.loadSecondaryImpl(testId)
  result.saveCorpusImpl = proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
    raise newException(DbError, "saveCorpus on read-only example database")
  result.loadCorpusImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    i.loadCorpusImpl(testId)
