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
## RFC-fuzzer-nextgen S6 adds a FOURTH, independent per-test-id artifact —
## the `sched` checkpoint (`saveSched`/`loadSched`) — a single opaque
## `LearnedState` blob (`nelli/learnedstate`) capturing a fuzz campaign's
## in-memory scheduling state (S1 rarity/energy, S2 bandit weights, G5's
## dictionary) so it survives a restart alongside the corpus. Unlike the
## three sections above it is NOT append/dedup/cap semantics — a whole-
## value overwrite, since a campaign has exactly one current checkpoint.
## The directory backend stores it as a sibling file, `<path>/<safeKey>.sched`.
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
## **Section-size introspection (F8, RFC-chapulin-hardening).**
## `sectionSizes(db, testId)` returns the entry count of each of the three
## sections as `tuple[primary, secondary, corpus: int]` — a cheap way for
## CI dashboards / corpus-management tooling to track corpus growth without
## hand-rolling `db.loadCorpus(id).len` (and the analogous calls for the
## other two sections) at every call site. It is a thin wrapper over the
## existing `loadPrimary`/`loadSecondary`/`loadCorpus` accessors, so it
## works identically across every backend (directory, in-memory,
## multiplexed, read-only) with no closure-record changes.
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
##
## Versions 1 (legacy) and 2 lack the corpus section (see below); reading
## either yields an empty `corpus`. Versions 1-3 lack per-primary-entry
## metadata; reading any of them yields an empty metadata table for
## every primary entry. Any write re-encodes at the current version, so
## an old file is transparently upgraded to carry per-entry metadata on
## first save.
##
## Writes are atomic: contents land in `<file>.tmp.<pid>.<tid>` then
## `moveFile` renames it over the target so a crash during write can't
## half-corrupt the entry.
##
## **Corpus delta log (E3b, RFC-fuzzer-nextgen).** `saveCorpus`/`loadCorpus`
## no longer live inside `<safeKey>.bin` — that file (versions 3-4 read a
## legacy inline corpus section for backward compat, but no longer WRITE
## one) now carries only `primary`+`secondary`. The corpus lives in its own
## per-testId append-only stream, one file per generation,
## `<safeKey>.corpus.<gen>.log` (gen >= 1, implicitly 1 until the first
## compaction):
##   header  := "NLC0" (4B magic)  u16 formatVersion  u16 flags
##   record  := u32 recLen  u8 op  payload   -- recLen = len(op byte+payload)
##     op=addCorpus (0): payload := toBytes(choices)
##     op=tombstone (1): payload := toBytes(choices)          -- logical delete
##     op=resetBulk (2): payload := u32 n  (u32 len  bytes)*  -- compaction fold
## `loadCorpus` replays the log with the same `dedupPrepend` admission policy
## (newest-first, dedup, cap-the-tail) that has always governed this section,
## so a corpus read through the log is byte-order-identical to the old
## in-file corpus — only the transport changed. Splitting the corpus out of
## `.bin` means the fuzzer's hot corpus-admit append (single writer: the
## orchestrator) never shares a rewrite target with the shrinker's `.bin`
## RMW. A pre-E3b `.bin` that still carries an inline corpus section is
## migrated into the log the first time that test id's corpus is touched
## (one-time, idempotent — no corpus data is lost, only relocated).
##
## Compaction never rewrites a generation in place: it writes a fresh
## `<safeKey>.corpus.<gen+1>.log` and atomically publishes it by tmp+rename
## of an 8-byte pointer file, `<safeKey>.corpus.head` ("NLCH" magic + u32
## gen). A reader resolves `head` once and pins that generation
## (`openCorpusSnapshot`, the `(generation, offset)` cut point future `U2`
## consumes) — a later compaction can't move data out from under it while
## the reader's lease is held. Superseded generations are reclaimed once
## unpinned: mid-campaign right after each compaction and again when a
## lease is released (`closeCorpusSnapshot`), plus an unconditional
## backstop sweep at the next campaign's startup — so a long-running
## campaign's corpus directory does not accumulate superseded generation
## files without bound.

import std/[os, strutils, tables, sets]
import ./choice, ./serialize  # `serialize` re-exports `binaryio`'s primitives + `DbCorrupt`

type
  DbError* = object of CatchableError
    ## Raised by `readOnlyDatabase` on write attempts; backends may also
    ## raise this for irrecoverable I/O conditions. The engine catches
    ## these and surfaces them via `Report.dbErrors` (or, with
    ## `Settings.strictDb = true`, propagates as a fatal report).
    ##
    ## `DbError` is the ONE documented corruption type for every read path
    ## in this file — both the `.bin` primary/secondary/corpus-legacy file
    ## (`readContents`) and the corpus delta log (`readCorpusLogFile` /
    ## `replayCorpusLog`) wrap any decode-time `DbCorrupt` (raised by
    ## `binaryio`/`serialize`'s bounds-checked decoders on truncated,
    ## malformed, or out-of-range bytes — whether that's the outer framing
    ## or the payload the framing wraps) into `DbError` before it reaches a
    ## caller. A caller only ever needs `except DbError` to catch every
    ## corruption shape this module produces; `DbCorrupt` itself is an
    ## internal decode-layer signal, not part of this module's public
    ## error contract.

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
    saveSchedImpl*:      proc(testId: string, data: seq[byte]) {.closure.}
    loadSchedImpl*:      proc(testId: string): seq[byte] {.closure.}

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

proc saveSched*(db: ExampleDatabase, testId: string, data: seq[byte]) =
  ## RFC-fuzzer-nextgen S6: persist a fuzz campaign's serialized
  ## `LearnedState` checkpoint (`nelli/learnedstate`) — a single opaque
  ## blob, keyed like the corpus but in its OWN section (never read/pruned
  ## by `dbReusePhase` or corpus logic). Whole-value overwrite, no
  ## dedup/cap semantics: unlike `primary`/`corpus` (many historical
  ## entries), a campaign has exactly ONE current checkpoint at a time.
  ## `db.nim` stays domain-agnostic here — it stores/loads bytes; encoding
  ## the bytes into/out of a `LearnedState` is `nelli/learnedstate`'s job,
  ## and deciding WHEN to call this is `fuzz.nim`'s (`FuzzSettings.
  ## checkpointCadence`).
  db.saveSchedImpl(testId, data)

proc loadSched*(db: ExampleDatabase, testId: string): seq[byte] =
  ## Inverse of `saveSched`. Returns `@[]` (empty) when no checkpoint has
  ## ever been saved under `testId` — indistinguishable, by design, from
  ## "nothing to resume" at the call site (`fuzz.nim` treats an empty
  ## result the same as a decode failure: cold-start, never an error).
  db.loadSchedImpl(testId)

proc sectionSizes*(db: ExampleDatabase,
                   testId: string): tuple[primary, secondary, corpus: int] =
  ## F8 (RFC-chapulin-hardening): cheap entry-count introspection for a test
  ## id's three sections, e.g. for CI dashboards / corpus-management tooling
  ## that want to track corpus growth without materializing (or diffing) every
  ## entry.
  ##
  ## DESIGN CHOICE: this is a thin wrapper over the existing `loadPrimary` /
  ## `loadSecondary` / `loadCorpus` accessors (`.len` of each) rather than a
  ## new `ExampleDatabase` closure field. A dedicated `Impl` closure could let
  ## the directory backend answer from the section's on-disk entry count
  ## without decoding every `ChoiceNode` sequence — cheaper for a very large
  ## file — but it would need a matching field wired through all four
  ## backends (directory, in-memory, multiplexed, read-only) for a size-S
  ## slice whose stated purpose is "how many entries," not "avoid all
  ## decode cost." The wrapper gets that answer correctly and for free on
  ## every backend (including third-party ones — no closure-record ABI
  ## change), at the cost of decoding entries it then only counts. If a
  ## profiled hot path ever needs count-without-decode, add a
  ## `sectionSizesImpl` closure then; nothing about this signature would
  ## need to change to grow one.
  (primary: db.loadPrimary(testId).len,
   secondary: db.loadSecondary(testId).len,
   corpus: db.loadCorpus(testId).len)

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

# --- corpus delta log (E3b, RFC-fuzzer-nextgen) ------------------------------
#
# The directory backend's `corpus` section lives in its own append-only log
# (one file per generation from C3 onward — see "generation files + head
# pointer" below), split OUT of `<safeKey>.bin` (E0-findings, Move 1): `.bin`
# retains only primary+secondary (written by the shrinker / `dbReusePhase`);
# the corpus log is written solely by the fuzz orchestrator's hot admit path.
# Splitting the two means the corpus append path never shares a rewrite
# target with the shrinker's `.bin` RMW — E0's race (a) is eliminated
# structurally rather than mediated by a lock.
#
# On-disk layout:
#   header  := "NLC0" (4B magic)  u16 formatVersion  u16 flags
#   record  := u32 recLen  u8 op  payload    -- recLen = len(op byte + payload)
#     op = opAddCorpus (0): payload := toBytes(choices)   -- admit a corpus entry
#     op = opTombstone (1): payload := toBytes(choices)   -- logical delete
#     op = opResetBulk (2): payload := u32 n  (u32 len  bytes)*  -- compaction fold
#
# `loadCorpus` reconstructs the live set the same way `dedupPrepend` always
# has (newest-first, deduped, cap-the-tail): each `addCorpus` record folds
# via `dedupPrepend` during replay (uncapped — see below), and each
# `tombstone` record removes its victim. The *cap* is enforced live, at save
# time, by `saveCorpusImpl`'s in-memory per-testId cache (the same
# `dedupPrepend` call the old whole-file RMW made); any entry that call's
# cap evicts is ALSO appended as a `tombstone` record (E3b C2), so a cold
# replay — a different handle/process, or no live cache at all — folds to
# the exact same capped set a same-handle read would, not just an unbounded
# history. `tombstone` doubles as the general logical-delete op a future
# disk-eviction policy (RFC's S4) would use; E3b wires only the cap-eviction
# caller, but the on-disk mechanism and replay fold are already general.

const
  corpusLogMagic = "NLC0"
  corpusLogFormatVersion = 1'u16

  opAddCorpus = 0'u8
  opTombstone = 1'u8
  opResetBulk = 2'u8

proc encodeCorpusLogHeader(): seq[byte] =
  for c in corpusLogMagic: result.add byte(c)
  result.putU16(corpusLogFormatVersion)
  result.putU16(0'u16)   # flags: reserved, unused at v1

proc checkCorpusLogHeader(raw: openArray[byte], pos: var int) =
  ## Validates magic and applies the SW-floor-pin-style version rule (E3b
  ## C5): a log newer than this build understands is refused (never silently
  ## misread); a log older than current is read as-is (the next compaction
  ## rewrites it at the current version — forward auto-migration); an
  ## unrecognized magic is refused.
  needBytes(raw, pos, 4)
  for i, c in corpusLogMagic:
    if raw[pos + i] != byte(c):
      raise newException(DbCorrupt,
        "corpus log: bad magic (not an NLC0 corpus log)")
  pos += 4
  let ver = getU16(raw, pos)
  discard getU16(raw, pos)   # flags: reserved, unused at v1
  if ver > corpusLogFormatVersion:
    raise newException(DbCorrupt,
      "corpus log format v" & $ver &
      " is newer than this build supports (v" & $corpusLogFormatVersion &
      "); upgrade nelli or point at a separate corpus directory")

proc putCorpusRecord(buf: var seq[byte], op: uint8, payload: seq[byte]) =
  buf.putU32(uint32(1 + payload.len))
  buf.add op
  buf.add payload

proc readCorpusRecords(raw: openArray[byte],
                       pos: var int): seq[tuple[op: uint8, payload: seq[byte]]] =
  while pos < raw.len:
    let recLen = getU32(raw, pos)
    needBytes(raw, pos, int(recLen))
    if recLen < 1:
      raise newException(DbCorrupt,
        "corpus log record length " & $recLen &
        " is too small to hold an op byte")
    let op = raw[pos]
    var payload = newSeq[byte](int(recLen) - 1)
    for i in 0 ..< payload.len: payload[i] = raw[pos + 1 + i]
    pos += int(recLen)
    result.add (op: op, payload: payload)

proc buildResetBulkPayload(list: seq[seq[ChoiceNode]]): seq[byte] =
  ## `resetBulk` payload := u32 n  (u32 len  bytes)* — the folded live set a
  ## compaction emits as the sole record of a fresh log (E0-findings item 2:
  ## "a compacted file is just a log that begins with resetBulk").
  result.putU32(uint32(list.len))
  for cs in list:
    let b = toBytes(cs)
    result.putU32(uint32(b.len))
    result.add b

proc decodeResetBulkPayload(payload: openArray[byte]): seq[seq[ChoiceNode]] =
  var pos = 0
  let n = getU32(payload, pos)
  for _ in 0 ..< int(n):
    let entryLen = getU32(payload, pos)
    needBytes(payload, pos, int(entryLen))
    var entryBytes = newSeq[byte](int(entryLen))
    for i in 0 ..< entryBytes.len: entryBytes[i] = payload[pos + i]
    pos += int(entryLen)
    result.add fromBytes(entryBytes)

proc replayCorpusRecords(records: seq[tuple[op: uint8, payload: seq[byte]]]):
                         seq[seq[ChoiceNode]] =
  ## Folds the log's records into the live corpus set, newest-first, exactly
  ## as repeated `dedupPrepend` calls with no cap (the raw log is a full,
  ## uncapped history — see the module-level note above on where the cap is
  ## actually enforced).
  for r in records:
    case r.op
    of opAddCorpus:
      result = dedupPrepend(result, fromBytes(r.payload), high(int))
    of opTombstone:
      let victim = fromBytes(r.payload)
      var kept: seq[seq[ChoiceNode]]
      for e in result:
        if e != victim: kept.add e
      result = kept
    of opResetBulk:
      result = decodeResetBulkPayload(r.payload)
    else:
      discard   # unrecognized op byte: forward-compat no-op (C5)

proc readCorpusLogFile(p: string): seq[tuple[op: uint8, payload: seq[byte]]] =
  if not fileExists(p): return
  var raw: seq[byte]
  try:
    raw = strToBytes(readFile(p))
  except IOError as e:
    raise newException(DbError,
      "cannot read corpus log at " & p & ": " & e.msg)
  try:
    var pos = 0
    checkCorpusLogHeader(raw, pos)
    result = readCorpusRecords(raw, pos)
  except DbCorrupt as e:
    raise newException(DbError,
      "corpus log at " & p & " is corrupted (" & e.msg & ")")
  except IndexDefect, RangeDefect:
    raise newException(DbError,
      "corpus log at " & p & " hit a decode panic")

proc replayCorpusLog(p: string): seq[seq[ChoiceNode]] =
  ## R46: `readCorpusLogFile` already folds a FRAMING corruption (bad
  ## magic/version, a torn record length) into `DbError`. `replayCorpusRecords`
  ## additionally decodes each record's PAYLOAD via `fromBytes`, which raises
  ## `DbCorrupt` (not `DbError`) on a structurally-valid record whose payload
  ## isn't a valid encoded `ChoiceSeq`. Left unwrapped, that `DbCorrupt` would
  ## escape past every other corruption shape in this file, which is
  ## uniformly `DbError` — this wrap makes payload corruption match framing
  ## corruption, mirroring `readContents`' own `DbCorrupt -> DbError` wrap
  ## around `parseContents` (the `.bin` file's analogous framing+payload
  ## decode) below.
  try:
    replayCorpusRecords(readCorpusLogFile(p))
  except DbCorrupt as e:
    raise newException(DbError,
      "corpus log at " & p & " has a corrupted record payload (" & e.msg & ")")

proc appendCorpusRecord(p: string, op: uint8, payload: seq[byte]) =
  createDir(parentDir(p))
  var buf: seq[byte]
  if not fileExists(p):
    buf.add encodeCorpusLogHeader()
  putCorpusRecord(buf, op, payload)
  var f: File
  if not open(f, p, fmAppend):
    raise newException(DbError, "cannot open corpus log at " & p & " for append")
  try:
    if buf.len > 0:
      discard f.writeBuffer(addr buf[0], buf.len)
  finally:
    f.close()

const compactionRatio = 4
  ## E0-findings item 2: compact when `logBytes > compactionRatio *
  ## liveSetBytes`. Checked on every append (amortized O(1) per admit, never
  ## the O(corpus) cost of a whole-file rewrite on the hot path); the actual
  ## fold only runs once the ratio trips.

proc estimateLiveSetBytes(list: seq[seq[ChoiceNode]]): int =
  for cs in list: result += toBytes(cs).len

# --- generation files + head pointer (E3b C3) --------------------------------
#
# Compaction does NOT rewrite the corpus log in place. Replacing bytes a
# reader may have an open fd on is safe on POSIX (rename/unlink over an open
# fd keeps the old inode's content intact for that fd) but NOT on Windows
# (sharing-mode / MOVEFILE_REPLACE_EXISTING semantics don't preserve old
# bytes for an existing handle) — so neither platform gets an in-place swap.
# Instead: each generation of the corpus lives at its own path,
# `<safeKey>.corpus.<gen>.log` (gen >= 1); the compactor writes a fresh
# generation file, then atomically publishes it by tmp+rename-ing a tiny
# (8-byte) pointer file, `<safeKey>.corpus.head` ("NLCH" magic + u32 gen). A
# reader resolves `head` ONCE at snapshot-open and pins that generation for
# the life of its snapshot (`openCorpusSnapshot` below) — a later compaction
# publishes a NEW generation and never mutates or unlinks the one a pinned
# reader is holding, so its already-open fd (or a `CorpusCutPoint` captured
# at open time) stays valid regardless of what compactions happen after.
# This is correct-by-construction on both platforms (E0-findings item 3);
# the POSIX arm is the testable one here (a real open fd never sees its
# bytes move), the Windows arm is design-complete and coded at E4a/E4b.
#
# Old generations are retained until they are safe to reclaim (R10 fix,
# post-E3b): `openCorpusSnapshot`/`closeCorpusSnapshot` below implement the
# reader-lease the RFC's E3b section specified — a generation is reclaimed
# only once no open lease pins it, and never while it is the current head.
# Reclaim itself runs from two places: `sweepSupersededCorpusGenerations`
# (unconditional, campaign-startup only — no reader from a PRIOR process
# can hold a lease in THIS process's lease table) and
# `reclaimUnpinnedGenerations` (lease-aware, runs mid-campaign right after
# a compaction publishes a new head, and again whenever a lease is
# released). Nothing yet in `src/` calls `openCorpusSnapshot` — it is
# reachable machinery for the future U2 corpus reader — so today every
# generation is unpinned the instant it is superseded and reclaim is
# effectively immediate; the lease exists so that remains true once a real
# reader starts holding cut points across time.
#
# R54 fix: R10's lease was a bare refcount keyed only by generation, with no
# way to tell two opens of the same generation apart — a double release of
# one logical open could free a lease a second, still-live reader depended
# on. `openCorpusSnapshot` now mints each call an unforgeable
# `CorpusSnapshotLease` token; `closeCorpusSnapshot` takes only that token,
# and a repeat release of the same token is a detectable no-op. See
# `CorpusSnapshotLease`'s doc comment below for the full account.

const corpusHeadMagic = "NLCH"

proc corpusGenPath(dbPath, testId: string, gen: int): string =
  dbPath / (safeKey(testId) & ".corpus." & $gen & ".log")

proc corpusHeadPath(dbPath, testId: string): string =
  dbPath / (safeKey(testId) & ".corpus.head")

proc readHeadGen(dbPath, testId: string): int =
  ## Generation 1 is implicit until the first compaction ever publishes a
  ## head pointer — no head file is written on the plain append hot path.
  let p = corpusHeadPath(dbPath, testId)
  if not fileExists(p): return 1
  var raw: seq[byte]
  try: raw = strToBytes(readFile(p))
  except IOError: return 1
  if raw.len < 8: return 1
  for i, c in corpusHeadMagic:
    if raw[i] != byte(c): return 1
  var pos = 4
  result = int(getU32(raw, pos))
  if result < 1: result = 1

proc publishCorpusHead(dbPath, testId: string, gen: int) =
  var buf: seq[byte]
  for c in corpusHeadMagic: buf.add byte(c)
  buf.putU32(uint32(gen))
  let final = corpusHeadPath(dbPath, testId)
  createDir(dbPath)
  let tmp = final & ".tmp." & $getCurrentProcessId() & "." & $getThreadId()
  writeFile(tmp, bytesToStr(buf))
  moveFile(tmp, final)

type CorpusCutPoint* = object
  ## RFC-fuzzer-nextgen E3b/U2: the record-atomic snapshot cut a corpus
  ## reader captures at open time — `(pinned generation, byte offset)`. A
  ## later compaction publishes a new generation but never mutates or
  ## reclaims the one this cut point names while a lease pins it (see
  ## `openCorpusSnapshot`/`closeCorpusSnapshot` below), so replaying
  ## `generation` up to `offset` reproduces exactly the entries
  ## `openCorpusSnapshot` returned, no matter what compactions run
  ## afterward — right up until the lease is released. Delivered here so
  ## U2 (the `forAll` replay-only corpus reader) doesn't invent this seam
  ## itself.
  ##
  ## Pure data — a cut point carries no lease identity of its own (see
  ## `CorpusSnapshotLease` for that). It can be copied, stored, or handed
  ## to another part of the caller freely; only the separate lease handle
  ## `openCorpusSnapshot` also returns is single-use and required to
  ## release the generation this cut point names.
  generation*: int
  offset*: int64

type CorpusLeaseKey = tuple[dbPath, testId: string, gen: int]

type CorpusLeaseToken = int64
  ## R54 fix: monotonic per-open identity. See `CorpusSnapshotLease`.

type CorpusSnapshotLease* = object
  ## R54 fix (closes an R10 gap): an unforgeable handle to exactly ONE
  ## `openCorpusSnapshot` open, returned alongside the call's
  ## `CorpusCutPoint` and required by `closeCorpusSnapshot`.
  ##
  ## R10's original lease was a bare `Table[(dbPath, testId, gen), int]`
  ## refcount — `openCorpusSnapshot` incremented it, `closeCorpusSnapshot`
  ## decremented it, and nothing distinguished WHICH open a given close
  ## corresponded to. Two legitimate concurrent readers of the same
  ## generation raised the shared count to 2; if any caller's release path
  ## fired twice for the same logical open (an explicit close AND an
  ## exception-path close, say), the count collapsed to 0 one release
  ## early and the still-live second reader's generation was deleted out
  ## from under it — silently, since `readCorpusLogFile` treats a missing
  ## file as an empty read rather than an error.
  ##
  ## Fixed by minting a fresh `id` per call (`nextCorpusLeaseToken` below)
  ## and keying the lease table by that id instead of by generation, so
  ## presence-of-id IS "this exact open is still holding its lease" — there
  ## is no shared count two opens of the same generation could collide on.
  ## The handle also carries its own `dbPath`/`testId`/`generation`, so
  ## `closeCorpusSnapshot` takes only the lease: there is no way to release
  ## the wrong key by passing mismatched arguments. All fields are private
  ## to this module — a caller can only ever obtain a value of this type
  ## from `openCorpusSnapshot`, never construct or forge one, so a
  ## `closeCorpusSnapshot` call can never target an open it wasn't handed.
  id: CorpusLeaseToken
  dbPath: string
  testId: string
  generation: int

var nextCorpusLeaseToken = 0'i64
  ## Mints `CorpusSnapshotLease.id` — see its doc comment. Monotonic for
  ## the life of the process; never reused, so a stale token from an
  ## already-released (or never-existent) lease can never alias a
  ## currently-open one.

var corpusSnapshotLeases = initTable[CorpusLeaseToken, CorpusLeaseKey]()
  ## R10 fix, refined by R54: open-`openCorpusSnapshot`-lease table, keyed
  ## by the unique per-open token minted into each returned
  ## `CorpusSnapshotLease` (NOT by `(dbPath, testId, generation)` — that
  ## was the R10 shape this replaces, and it could not tell two opens of
  ## the same generation apart; see `CorpusSnapshotLease`'s doc comment for
  ## the failure that shape allowed). `openCorpusSnapshot` inserts one
  ## entry per call; `closeCorpusSnapshot` deletes it by token, so this
  ## table only ever holds currently-open leases, never a history of past
  ## ones, and never a shared count two different opens could both decrement.
  ## A generation with ANY entry here naming it is ineligible for
  ## mid-campaign reclaim regardless of how superseded it is.
  ##
  ## Lives at module scope rather than inside an `ExampleDatabase` closure
  ## because `openCorpusSnapshot` is itself deliberately free-standing
  ## directory-backend machinery reachable by path (see its own doc below),
  ## not a closure field — so there is no per-handle closure environment to
  ## put this in. A bare `Table` is sufficient because F-1 (RFC-fuzzer-
  ## nextgen E0) guarantees exactly one `ExampleDatabase` handle is ever
  ## constructed per campaign/process and shared — nothing in this codebase
  ## constructs two handles over the same path concurrently to race this
  ## table, and a fresh OS process (a new campaign) always starts with an
  ## empty table regardless of what a prior campaign's process leaked (a
  ## lease left open by a hard-killed process has no recovery path WITHIN
  ## that dead process, but costs nothing beyond one unreclaimed generation
  ## file until the next campaign's unconditional startup sweep,
  ## `sweepSupersededCorpusGenerations`, removes it — see that proc's doc).

proc openCorpusSnapshot*(dbPath, testId: string):
    tuple[cutPoint: CorpusCutPoint, entries: seq[seq[ChoiceNode]],
          lease: CorpusSnapshotLease] =
  ## Resolves `head` once, pins that generation, and replays it up to its
  ## current end-of-file. Free-standing (not part of `ExampleDatabase` —
  ## the closure-record interface is unchanged): this is directory-backend
  ## machinery, reachable by path for the callers (future U2, this
  ## module's own reader-safety tests) that need the cut point itself
  ## rather than just the folded entries `loadCorpus` returns.
  ##
  ## Takes out a lease on the returned generation and mints it a fresh,
  ## unforgeable `CorpusSnapshotLease` identifying THIS call alone (R54;
  ## see that type's doc comment for why identity per-open, not a shared
  ## per-generation refcount, is required for correctness). Every call MUST
  ## be paired with exactly one `closeCorpusSnapshot(lease)` once the
  ## caller is done with `entries` and with replaying anything past
  ## `offset` later — pass the `lease` field of this proc's result, not the
  ## `cutPoint` (the cut point alone no longer carries lease identity).
  ## Forgetting to close a lease leaks a generation FILE (it is simply
  ## never reclaimed) — not a crash, not data loss, and not a leak of
  ## anything beyond that one file, which is the deliberately-conservative
  ## failure mode here; a leaked lease from a hard-killed process is
  ## recovered at the next campaign's startup sweep (see
  ## `corpusSnapshotLeases`'s doc comment and `sweepSupersededCorpusGenerations`)
  ## — there is no in-process recovery for a lease a live caller simply
  ## never releases, and deliberately no timeout-based reclaim that could
  ## yank a generation out from under a slow-but-live reader.
  let gen = readHeadGen(dbPath, testId)
  let p = corpusGenPath(dbPath, testId, gen)
  let offset = if fileExists(p): int64(getFileSize(p)) else: 0'i64
  let entries = replayCorpusRecords(readCorpusLogFile(p))
  inc nextCorpusLeaseToken
  let token = nextCorpusLeaseToken
  corpusSnapshotLeases[token] = (dbPath: dbPath, testId: testId, gen: gen)
  result = (cutPoint: CorpusCutPoint(generation: gen, offset: offset),
            entries: entries,
            lease: CorpusSnapshotLease(id: token, dbPath: dbPath,
                                        testId: testId, generation: gen))

proc pinnedCorpusGenerations(dbPath, testId: string): HashSet[int] =
  ## Every generation `testId` (at `dbPath`) currently has at least one live
  ## `openCorpusSnapshot` lease on. Consulted by mid-campaign reclaim so it
  ## never removes a generation a live reader is still holding.
  for _, k in corpusSnapshotLeases:
    if k.dbPath == dbPath and k.testId == testId:
      result.incl k.gen

proc reclaimUnpinnedGenerations(dbPath, testId: string, headGen: int) =
  ## Removes every `<safeKey(testId)>.corpus.<gen>.log` at `dbPath` other
  ## than the current head generation and any generation
  ## `pinnedCorpusGenerations` reports as leased. This is the MID-CAMPAIGN
  ## reclaim path (R10 fix) — called right after a compaction publishes a
  ## new head, and again whenever a lease is released, so growth is bounded
  ## within a single long-running campaign rather than only reclaimed at
  ## the next campaign's startup. Deliberately distinct from
  ## `sweepSupersededCorpusGenerations` below, which is unconditional
  ## (ignores leases entirely) because it only ever runs at a moment where
  ## no lease in THIS process's table can legitimately apply — a brand new
  ## campaign's constructor, before this campaign's own readers exist.
  let pinned = pinnedCorpusGenerations(dbPath, testId)
  let prefix = safeKey(testId) & ".corpus."
  for kind, p in walkDir(dbPath, relative = false):
    if kind != pcFile: continue
    let name = extractFilename(p)
    if not name.startsWith(prefix) or not name.endsWith(".log"): continue
    let genStr = name[prefix.len ..< name.len - 4]
    var gen: int
    try: gen = parseInt(genStr)
    except ValueError: continue    # not a `<key>.corpus.<n>.log` name — leave alone
    if gen == headGen or gen in pinned: continue
    try: removeFile(p)
    except OSError: discard

proc closeCorpusSnapshot*(lease: CorpusSnapshotLease): bool {.discardable.} =
  ## Releases exactly the lease `openCorpusSnapshot` minted for `lease`'s
  ## call (R54: identity is per-open, via `lease.id` — not a shared
  ## per-generation refcount; see `CorpusSnapshotLease`'s doc comment).
  ## Because `lease` carries its own `dbPath`/`testId`/`generation`, this
  ## takes no other arguments — there is no way to release the wrong key by
  ## passing mismatched arguments, and no `CorpusCutPoint` value alone is
  ## ever accepted here (a cut point never carried lease identity).
  ##
  ## Returns `true` if this call actually released a still-open lease,
  ## `false` if `lease`'s token was already released (or, since the type is
  ## unforgeable, could otherwise not be found) — a detectable no-op rather
  ## than silent success. Safe to call MORE than once on the same `lease`
  ## value: the second and later calls each see the token already gone and
  ## return `false` without touching any OTHER lease's entry — a double
  ## release of one logical open (an explicit close and an exception-path
  ## close of the same open, say) can therefore never free a lease a
  ## legitimate concurrent reader of the same generation still depends on,
  ## because that reader holds a different token entirely.
  ##
  ## Also finishes reclaiming the released generation immediately if it is
  ## no longer the head: covers the case where a compaction superseded it
  ## WHILE the lease was held (mid-campaign reclaim saw it pinned back then
  ## and skipped it), so growth doesn't have to wait for the *next*
  ## compaction to notice the lease is gone.
  if not corpusSnapshotLeases.hasKey(lease.id):
    return false
  corpusSnapshotLeases.del(lease.id)
  reclaimUnpinnedGenerations(lease.dbPath, lease.testId,
                              readHeadGen(lease.dbPath, lease.testId))
  true

const nelliShmPrefix* = "nelli_"
  ## RFC-fuzzer-nextgen E-cleanup: the namespace token every nelli-owned
  ## POSIX `shm_open` segment name carries (see `nelli_shm.c`, and the E2b
  ## test suites' own `/nelli_..._<pid>` names). Shared here so the
  ## campaign-startup sweep below can identify nelli's own leaked shm
  ## segments by PREFIX ALONE — mirroring the `.tmp.` sweep's own
  ## prefix-only scoping — and never touch a foreign process's segment.

when defined(posix):
  proc sweepStaleShmSegments() =
    ## RFC-fuzzer-nextgen E-cleanup: a crashed/hard-killed prior campaign's
    ## `shm_open` coverage segments (E2b) are NOT reclaimed by the OS on
    ## process death — unlike an ordinary fd, a `shm_open` segment persists
    ## in `/dev/shm` until explicitly unlinked. Swept here by name-prefix
    ## match only: safe because this runs at campaign-startup construction
    ## time, before this campaign (or any worker of it) has created its OWN
    ## shm segments, so every `nelli_`-prefixed entry found here is
    ## necessarily left over from a PRIOR run. A foreign process's segment
    ## never carries this prefix and is left untouched. (On Linux,
    ## `shm_open("/foo", ...)` materializes as an ordinary file at
    ## `/dev/shm/foo` — the same mechanism `nelli_shm.c` itself relies on —
    ## so an ordinary `removeFile` here is exactly `shm_unlink`, no extra
    ## FFI needed.) Known scope limit: this is a GLOBAL OS namespace, not
    ## scoped to this DB's `path` — two DIFFERENT nelli campaigns running
    ## concurrently on the same host would need distinguishable names to
    ## avoid this sweep racing a live sibling campaign; not a new problem
    ## this slice introduces (every current shm-name caller already
    ## self-selects a unique suffix, e.g. `$pid`), just not itself enforced
    ## here.
    const shmDir = "/dev/shm"
    if not dirExists(shmDir): return
    for kind, p in walkDir(shmDir, relative = false):
      if kind == pcFile and extractFilename(p).startsWith(nelliShmPrefix):
        try: removeFile(p)
        except OSError: discard

proc sweepSupersededCorpusGenerations(path: string) =
  ## RFC-fuzzer-nextgen E-cleanup, unconditional backstop for whatever the
  ## mid-campaign lease-aware reclaim (`reclaimUnpinnedGenerations`, R10
  ## fix) didn't get to — a crash mid-reclaim, or a lease from a
  ## hard-killed PRIOR campaign's process that (being a different process)
  ## left no trace in THIS process's `corpusSnapshotLeases` table at all.
  ## At campaign STARTUP no reader from the PRIOR campaign can possibly
  ## still be alive to legitimately pin a generation — the exact same
  ## one-time-safe-to-reclaim moment the `.tmp.` sweep above already
  ## exploits — so every generation OTHER than the one
  ## `<safeKey>.corpus.head` currently names is safe to remove
  ## unconditionally, no lease check needed (and none would mean anything
  ## here: any lease found in the table at this point could only be a
  ## same-process artifact, e.g. a test harness reusing this process across
  ## simulated campaigns — never a real prior campaign's reader). A key
  ## with no head file yet (never compacted) has only its implicit
  ## generation 1 and nothing to sweep.
  if not dirExists(path): return
  var genFilesByKey = initTable[string, seq[tuple[gen: int, p: string]]]()
  for kind, p in walkDir(path, relative = false):
    if kind != pcFile: continue
    let name = extractFilename(p)
    if not name.endsWith(".log"): continue
    let idx = name.find(".corpus.")
    if idx <= 0: continue
    let key = name[0 ..< idx]
    let genStr = name[idx + ".corpus.".len ..< name.len - 4]
    var gen: int
    try: gen = parseInt(genStr)
    except ValueError: continue    # not a `<key>.corpus.<n>.log` name — leave alone
    genFilesByKey.mgetOrPut(key, @[]).add (gen: gen, p: p)
  for key, files in genFilesByKey:
    if files.len <= 1: continue    # only one generation on disk — nothing superseded
    let headGen = readHeadGen(path, key)
    for f in files:
      if f.gen != headGen:
        try: removeFile(f.p)
        except OSError: discard

proc directoryBasedDatabase*(path: string): ExampleDatabase =
  ## File-backed DB rooted at `path` (created on first save). One file per
  ## test id (`<path>/<safeKey>.bin`); writes are atomic via tmp + rename.
  ## Sweeps orphaned `.tmp.<pid>.<tid>` files from prior crashes, plus (RFC-
  ## fuzzer-nextgen E-cleanup) superseded corpus generation files and stale
  ## nelli shm segments left by a hard-killed prior campaign — all at this
  ## one campaign-startup construction moment (F-1: this backend is
  ## constructed exactly once per campaign).
  if dirExists(path):
    for kind, p in walkDir(path, relative = false):
      if kind == pcFile and ".tmp." in p:
        try: removeFile(p)
        except OSError: discard
    sweepSupersededCorpusGenerations(path)
  when defined(posix):
    sweepStaleShmSegments()
  # RFC-fuzzer-nextgen E4b: deliberately NOT ported to Windows, not merely
  # unimplemented. `sweepStaleShmSegments` exists because a POSIX
  # `shm_open` segment is a NAMED, independently-persistent kernel object —
  # it survives in `/dev/shm` until an explicit `shm_unlink`, even after
  # every process that ever mapped it (including a hard-killed campaign)
  # has exited, which is exactly the orphan this sweep reclaims. A Windows
  # named file-mapping section (`nelli_shm.c`'s `CreateFileMapping` arm) has
  # no such independent lifetime: the OS destroys it the moment its LAST
  # `HANDLE` (across every process, live or dead — a crashed/hard-killed
  # process's handles are closed by the OS as part of process teardown) is
  # gone, with no unlink step for anyone to skip. So a hard-killed Windows
  # campaign cannot leak a stale segment for a later campaign to sweep in
  # the first place — a no-op sweep would only add dead code, not parity.

  proc keyPath(testId: string): string = path / (safeKey(testId) & ".bin")
  proc schedPath(testId: string): string = path / (safeKey(testId) & ".sched")
    ## RFC-fuzzer-nextgen S6: a sibling file next to the corpus (`.bin`/
    ## `.corpus.*.log`), NOT folded into either — the checkpoint has none
    ## of the corpus's append-log/generation/compaction machinery (it is
    ## always exactly ONE current blob, overwritten whole), so reusing
    ## that machinery would be pure overhead for a value this simple.
    ## Same atomic tmp+rename discipline as `.bin`'s `writeContents`; the
    ## constructor's existing `.tmp.` sweep (above) already covers a
    ## crash-orphaned `.sched.tmp.*` — no separate sweep needed.

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

  # --- corpus delta log wiring (E3b) ------------------------------------
  var corpusCache = initTable[string, seq[seq[ChoiceNode]]]()
    ## Per-handle live-set cache (F-1: this backend is meant to be
    ## constructed once and shared, so the cache lives exactly as long as
    ## the discipline it depends on). A same-handle save/load sequence
    ## reads its own cap-accurate writes straight out of this table; a
    ## cold key falls back to `replayCorpusLog`.
  var migratedTestIds: Table[string, bool]
  var corpusGenCache = initTable[string, int]()
    ## This handle's cached notion of "the generation I'm currently
    ## appending to" per testId (C3). Resolved from the head pointer once,
    ## then only ever advanced by THIS handle's own compactions — matching
    ## F-1 (one long-lived writer; nothing else publishes a head this
    ## handle doesn't already know about).

  proc currentCorpusGen(testId: string): int =
    if corpusGenCache.hasKey(testId): return corpusGenCache[testId]
    result = readHeadGen(path, testId)
    corpusGenCache[testId] = result

  proc activeCorpusLogPath(testId: string): string =
    corpusGenPath(path, testId, currentCorpusGen(testId))

  proc ensureCorpusMigrated(testId: string) =
    ## Backward compat: a pre-E3b `.bin` (db-format v3/v4) still carries its
    ## corpus section inline. On first corpus access for `testId`, move any
    ## such entries into the real log and strip them from `.bin` — one-time,
    ## idempotent (a second call finds an already-empty `.bin` corpus
    ## section and no-ops). No data is lost; the transport just changes.
    if migratedTestIds.hasKey(testId): return
    migratedTestIds[testId] = true
    var c: DbContents
    try: c = readContents(testId)
    except DbError: return
    if c.corpus.len == 0: return
    let logPath = activeCorpusLogPath(testId)
    # `c.corpus` is stored newest-first (F5); append oldest-first so the
    # log's replay order reconstructs the same newest-first result.
    for i in countdown(c.corpus.len - 1, 0):
      appendCorpusRecord(logPath, opAddCorpus, toBytes(c.corpus[i]))
    c.corpus = @[]
    writeContents(testId, c)

  proc loadCorpusCached(testId: string): seq[seq[ChoiceNode]] =
    ensureCorpusMigrated(testId)
    if corpusCache.hasKey(testId): return corpusCache[testId]
    result = replayCorpusLog(activeCorpusLogPath(testId))
    corpusCache[testId] = result

  proc maybeCompactCorpusLog(testId: string, liveList: seq[seq[ChoiceNode]]) =
    if liveList.len == 0: return   # nothing to fold to; avoid pointless churn
    let liveBytes = estimateLiveSetBytes(liveList)
    if liveBytes == 0: return
    let curPath = activeCorpusLogPath(testId)
    if not fileExists(curPath): return
    let logBytes = int(getFileSize(curPath))
    if logBytes <= compactionRatio * liveBytes: return
    # Fold to a fresh generation (never rewrite the one a reader might have
    # pinned), then publish it as the new head — the atomic moment a
    # snapshot opened after this call sees the compacted view (E3b C3).
    let newGen = currentCorpusGen(testId) + 1
    var buf = encodeCorpusLogHeader()
    putCorpusRecord(buf, opResetBulk, buildResetBulkPayload(liveList))
    writeFile(corpusGenPath(path, testId, newGen), bytesToStr(buf))
    publishCorpusHead(path, testId, newGen)
    corpusGenCache[testId] = newGen
    # R10 fix: reclaim mid-campaign, not just at the next campaign's
    # startup, so a long-running campaign's superseded generations don't
    # accumulate without bound. Ordering matters for crash-safety: this
    # runs strictly AFTER `publishCorpusHead` above has durably renamed the
    # head pointer onto `newGen`, so `readHeadGen` inside
    # `reclaimUnpinnedGenerations` always resolves to `newGen` here and
    # `newGen`'s own file (already fully written by `writeFile` above) can
    # never be the one removed. Anything this call DOES remove was already
    # superseded and already unreferenced by the (now-published) head
    # before this call even started. If the process dies partway through
    # this loop, some already-superseded, already-unreferenced files are
    # simply left unswept — no data loss, no unreadable corpus, just
    # deferred cleanup that the next compaction or the next campaign's
    # startup sweep (`sweepSupersededCorpusGenerations`) finishes.
    reclaimUnpinnedGenerations(path, testId, newGen)

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
    ## E3b: appends ONE `addCorpus` record to the current corpus generation
    ## — `.bin` is never touched, so this can never race the shrinker's
    ## `.bin` RMW (E0 race (a)). The cap (`dedupPrepend`'s
    ## dedup+prepend+cap-the-tail) is applied in memory exactly as it
    ## always was; any entry the cap evicts is also logged as a
    ## `tombstone` (E3b C2), so a COLD replay — a different handle/process,
    ## or this same handle after eviction with no live cache — reconstructs
    ## the identical capped set, not just the same-handle cache does.
    let old = loadCorpusCached(testId)
    let newList = dedupPrepend(old, choices, maxEntries)
    corpusCache[testId] = newList
    let logPath = activeCorpusLogPath(testId)
    appendCorpusRecord(logPath, opAddCorpus, toBytes(choices))
    for entry in old:
      if entry notin newList:
        appendCorpusRecord(logPath, opTombstone, toBytes(entry))
    maybeCompactCorpusLog(testId, newList)
  result.loadCorpusImpl = proc(testId: string): seq[seq[ChoiceNode]] =
    loadCorpusCached(testId)
  result.saveSchedImpl = proc(testId: string, data: seq[byte]) =
    createDir(path)
    let final = schedPath(testId)
    let tmp = final & ".tmp." & $getCurrentProcessId() & "." & $getThreadId()
    writeFile(tmp, bytesToStr(data))
    moveFile(tmp, final)
  result.loadSchedImpl = proc(testId: string): seq[byte] =
    let p = schedPath(testId)
    if not fileExists(p): return @[]
    try: strToBytes(readFile(p))
    except IOError: @[]   # unreadable checkpoint: treated as none (cold start)

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
  var sched = initTable[string, seq[byte]]()

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
  result.saveSchedImpl = proc(testId: string, data: seq[byte]) =
    sched[testId] = data
  result.loadSchedImpl = proc(testId: string): seq[byte] =
    sched.getOrDefault(testId)

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
      var seenAt = -1
      for idx, r in result:
        if r.choices == entry.choices: seenAt = idx; break
      if seenAt == -1:
        result.add entry
      elif result[seenAt].meta.len == 0 and entry.meta.len > 0:
        # Primary's entry carried no meta but the secondary's did for the same
        # choice-sequence: carry the secondary's meta forward rather than
        # silently dropping it. Never overwrites a non-empty primary meta.
        result[seenAt].meta = entry.meta
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
  result.saveSchedImpl = proc(testId: string, data: seq[byte]) =
    p.saveSchedImpl(testId, data)
  result.loadSchedImpl = proc(testId: string): seq[byte] =
    ## RFC-fuzzer-nextgen S6: unlike corpus/primary/secondary reads (which
    ## UNION both backends — many entries can coexist), a checkpoint is a
    ## single current blob, so "union" has no meaning here. Primary wins
    ## when it has one (it's the writable, actively-checkpointed side);
    ## the secondary's checkpoint (e.g. a shared read-only reference
    ## corpus's own prior learned state) is a fallback only when primary
    ## has none.
    result = p.loadSchedImpl(testId)
    if result.len == 0: result = s.loadSchedImpl(testId)

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
  result.saveSchedImpl = proc(testId: string, data: seq[byte]) =
    raise newException(DbError, "saveSched on read-only example database")
  result.loadSchedImpl = proc(testId: string): seq[byte] =
    i.loadSchedImpl(testId)
