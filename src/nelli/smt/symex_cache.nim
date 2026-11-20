## nelli/smt/symex_cache -- the content-addressed records behind the symex DB
## API: the keys and the save/load of witnesses, verdicts, raised-exception
## entries and the `:notes` record, through `ExampleDatabase`. What each
## entry's metadata holds is `symex_codec`'s (RFC-0016 INT-34 C1).
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The `*Impl` procs are
## re-exported by `symex.nim` (generated code and the cache tests name them);
## the macro forms that call them stay in the facade.

import std/[tables, sets, options, strutils]
from z3 import z3FullVersion
import ../choice
import ../db
import ./dsl
import ./canonicalize
import ../engine/types as engineTypes
import ./symex_codec   ## RFC-0016 INT-34 C1: the record encodings

type
  CachedWitness* = tuple[choices: seq[ChoiceNode], soundness: Soundness,
                        gaps: seq[FindingGap]]
    ## RFC-0005 S11/S8az. One `:sat` cache entry: the witness's choice
    ## sequence, the soundness of the verdict that produced it, and (S8az)
    ## the per-cause `gaps()` view from the run that produced it. `gaps` is
    ## `@[]` on an entry written before S8az or by a writer that never
    ## recorded it — see `storedGaps`.
  CachedVerdict* = tuple[status: SymexFindingStatus, soundness: Soundness,
                        gaps: seq[FindingGap]]
    ## RFC-0005 S11/S8av. A `:unsat` / `:unk` cache hit: the status, the
    ## soundness it was persisted with, and (S8av) the per-cause `gaps()`
    ## view from the run that produced it. `gaps` is `@[]` on an entry
    ## written before S8av or by a writer that never recorded it — see
    ## `storedGaps`.
  CachedRaised* = tuple[raw: RawResult, gaps: seq[FindingGap],
                       choices: seq[ChoiceNode]]
    ## RFC-0005 S11/S8az. A `:raised:<type>` cache hit: the reconstructed
    ## `RawResult` (status `sxRaised`, `raisedTypeId`, `soundness` and, since
    ## RFC-0005 W1, `isDefect`; its `raisedWitness` is not rebuilt) and
    ## (S8az) the per-cause `gaps()` view of the run that produced it. `gaps`
    ## is `@[]` on an entry written before S8az or by a writer that never
    ## recorded it — see `storedGaps`. RFC-0005 W1: `choices` is the raise's
    ## witness as `renderAsChoices` rendered it (what `SymexFinding.
    ## witnessChoices` carries), `@[]` when the writer passed none.
  CachedNotes* = tuple[hints: seq[FindingHint],
                      diagnostics: seq[FindingDiagnostic],
                      undefined: seq[FindingUndefined]]
    ## RFC-0005 W1. The `:notes` record of a cached verdict: the run's hints
    ## and its non-winning diagnostics (`SymexFinding.hints`/`.diagnostics`).
    ## Both `@[]` when the record is absent, the same best-effort rule as
    ## `gaps` (`storedNotes`).

proc metaReady(db: ExampleDatabase, who: string,
               errors: var seq[string]): bool =
  ## RFC-0005 S11. The soundness rides the entry metadata, so the symex cache
  ## reads and writes through `saveWithMetaImpl` / `loadPrimaryWithMetaImpl`.
  ## A hand-built `ExampleDatabase` may leave them nil, and calling a nil
  ## closure is a SIGSEGV, not an exception the best-effort `try` below can
  ## absorb. Such a backend is reported once per call and the cache is
  ## skipped: a save is not persisted, a load is a miss.
  result = not db.saveWithMetaImpl.isNil and
           not db.loadPrimaryWithMetaImpl.isNil
  if not result:
    errors.add who & ": the ExampleDatabase backend has no " &
      "saveWithMetaImpl/loadPrimaryWithMetaImpl, which the symex cache " &
      "needs to store a result's Soundness (RFC-0005 S11); not cached"

# ---- RFC-0005 W1: the `:notes` record --------------------------------------
#
# A finding's `hints` and `diagnostics` are the cold run's, so a cache hit must
# serve them or the warm report says less than the cold one. They ride one
# record beside the verdict's slot, under the same base key: `:notes`, an
# empty-valued entry whose metadata holds the hints (one key set per entry, as
# `gapsMeta` does, so no message needs escaping) and the diagnostic count, and
# `:notes:diag:<i>`, one entry per diagnostic whose VALUE is its witness and
# whose metadata holds its type, defect-ness and message. Each slot keeps one
# entry (`verdictCacheMaxEntries`), and a cold run rewrites them all, so the
# record always describes the most recent cold run, as the verdict slots do.
# Missing or malformed, it degrades to empty (best-effort, like `gaps`).

const cacheKeyNotes = ":notes"

proc notesKey(baseKey: string; diag: int): string =
  baseKey & cacheKeyNotes & ":diag:" & $diag

proc saveSymexNotesImpl*(db: ExampleDatabase, prog: SymexProgram,
                         target: SymexTarget, settings: SymexSettings,
                         hints: seq[FindingHint],
                         diagnostics: seq[FindingDiagnostic],
                         undefined: seq[FindingUndefined],
                         errors: var seq[string]) =
  ## RFC-0005 W1. Persist a cold run's hints and diagnostics beside its
  ## verdict (see the section comment). Save errors are appended to `errors`
  ## and the call returns normally.
  if not metaReady(db, "saveSymexNotesImpl", errors): return
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  let meta = notesHeadMeta(hints, diagnostics.len, undefined.len)
  try:
    # RFC-0016 INT-38 (R6-07): a head the loader refuses first, so a re-save
    # that fails part-way never serves the earlier record's head over a mix
    # of its slots and this save's. A failure of this first write leaves the
    # earlier record whole.
    db.save(baseKey & cacheKeyNotes, @[],
            {notesVersionMetaKey: "-"}.toTable, verdictCacheMaxEntries)
    for i, u in undefined:
      db.save(notesKey(baseKey, i).replace(":diag:", ":undef:"),
              u.witnessChoices, undefinedMeta(u), verdictCacheMaxEntries)
    for i, d in diagnostics:
      db.save(notesKey(baseKey, i), d.witnessChoices, diagnosticMeta(d),
              verdictCacheMaxEntries)
    # The count last: a reader never trusts a count whose entries were not
    # all written first.
    db.save(baseKey & cacheKeyNotes, @[], meta, verdictCacheMaxEntries)
  except CatchableError as e:
    errors.add "saveSymexNotesImpl: " & $e.name & ": " & e.msg

proc loadSymexNotesImpl*(db: ExampleDatabase, prog: SymexProgram,
                         target: SymexTarget, settings: SymexSettings,
                         errors: var seq[string]): CachedNotes =
  ## RFC-0005 W1. The inverse of `saveSymexNotesImpl`; empty when the record
  ## is absent or not in this encoding (never a miss of the verdict itself).
  if not metaReady(db, "loadSymexNotesImpl", errors): return
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  try:
    let head = db.loadPrimaryWithMeta(baseKey & cacheKeyNotes)
    if head.len != 1: return
    let meta = head[0].meta
    let counts = storedNotesCounts(meta)
    if counts.isNone: return
    let n = counts.get
    for i in 0 ..< n.undefined:
      let e = db.loadPrimaryWithMeta(
        notesKey(baseKey, i).replace(":diag:", ":undef:"))
      if e.len != 1: break
      let u = storedUndefined(e[0].meta, e[0].choices)
      if u.isNone: break
      result.undefined.add u.get
    result.hints = storedHints(meta, n.hints)
    for i in 0 ..< n.diagnostics:
      let e = db.loadPrimaryWithMeta(notesKey(baseKey, i))
      if e.len != 1: break
      let d = storedDiagnostic(e[0].meta, e[0].choices)
      if d.isNone: break
      result.diagnostics.add d.get
  except CatchableError as e:
    errors.add "loadSymexNotesImpl: " & $e.name & ": " & e.msg
    result = (hints: @[], diagnostics: @[], undefined: @[])

func replayedUnkeyed*(prog: SymexProgram; s: Soundness): bool =
  ## RFC-0016 INT-31 (W-18). A claim a replay settled (`rsConfirmed`,
  ## `rsUnconfirmed`, `witnessUnsafe`) is a fact about every body the replay
  ## ran. Where the key cannot see one of them (`SymexProgram.implOpen`: a
  ## foreign body, a proc variable's target), a stored claim would be served
  ## after that body changed: not stored, and the next run replays again.
  prog.implOpen.len > 0 and
    (s.replay in {rsConfirmed, rsUnconfirmed} or s.witnessUnsafe)

proc saveSymexWitnessImpl*(db: ExampleDatabase, prog: SymexProgram,
                           target: SymexTarget, settings: SymexSettings,
                           finding: SymexFinding,
                           errors: var seq[string],
                           maxEntries = 64): bool {.discardable.} =
  ## Runtime body of `saveSymexWitness`. Review R5 (D4a): true only when it
  ## wrote the entry (the `:notes` record rides a saved verdict, nothing else). Skips non-Sat findings (no
  ## witness to persist), otherwise saves the choice array under the
  ## content-addressed key with `:sat` suffix, with `finding.soundness` in
  ## the entry's metadata (RFC-0005 S11). RFC-0005 S8az: also carries
  ## `finding.gaps` (the run's per-cause view) via the shared
  ## `gapsMeta`/`storedGaps` encoding `CachedVerdict` already uses, so a
  ## `:sat` cache hit can report the same `gaps()` a cold run would.
  ##
  ## DB save errors are appended to `errors` and the call returns
  ## normally — symmetric with `saveSymexVerdictImpl`. Closes a
  ## pre-existing inconsistency where `db.nim`'s module promise
  ## ("errors flow to Report.dbErrors") was violated here by
  ## propagating exceptions. Callers route `errors` into
  ## `Report.dbErrors`.
  if finding.status != sfSat: return false
  # RFC-0005 0.9.1 (WA-7, WA-9): a lossy winner the replay did not confirm for
  # a reason of the run is not stored as unconfirmed for good. Read off the
  # finding (review R1-07), never off the thread.
  if not finding.soundness.cacheable: return false
  if replayedUnkeyed(prog, finding.soundness): return false   # INT-31
  if not metaReady(db, "saveSymexWitnessImpl", errors): return false
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & cacheKeySat
  let meta = verdictMeta(finding.soundness, finding.gaps)   ## RFC-0005 S8az
  try:
    db.save(key, finding.witnessChoices, meta, maxEntries)
    result = true
  except CatchableError as e:
    errors.add "saveSymexWitnessImpl: " & $e.name & ": " & e.msg

proc loadSymexWitnessesImpl*(db: ExampleDatabase, prog: SymexProgram,
                             target: SymexTarget,
                             settings: SymexSettings,
                             errors: var seq[string]
                            ): seq[CachedWitness] =
  ## Runtime body of `loadSymexWitnesses`. Returns the persisted
  ## witnesses for *exactly* this SUT/target/settings/Z3/Nim/walker
  ## combination, each with its stored `Soundness` (RFC-0005 S11) and
  ## (RFC-0005 S8az) `gaps` (`@[]` for a pre-S8az entry or a writer that
  ## never recorded it — see `storedGaps`). Mismatched key → empty seq. An
  ## entry without soundness metadata is skipped (a miss, with a note in
  ## `errors`) — soundness stays load-bearing; gaps stays best-effort.
  ##
  ## Load errors append to `errors` and the call degrades to an
  ## empty seq (treated as "miss") — symmetric with
  ## `loadSymexVerdictImpl`. The cache is best-effort.
  if not metaReady(db, "loadSymexWitnessesImpl", errors): return
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & cacheKeySat
  try:
    for e in db.loadPrimaryWithMeta(key):
      let s = storedSoundness(e.meta)
      let g = storedGaps(e.meta)   ## RFC-0005 S8az; INT-32: malformed is a miss
      if s.isSome and g.isSome:
        result.add (choices: e.choices, soundness: s.get, gaps: g.get)
      elif s.isSome:
        errors.add "loadSymexWitnessesImpl: an entry with malformed gaps " &
          "metadata is treated as a miss"
      else:
        errors.add "loadSymexWitnessesImpl: an entry without soundness " &
          "metadata (pre-RFC-0005-S11 format) is treated as a miss"
  except CatchableError as e:
    errors.add "loadSymexWitnessesImpl: " & $e.name & ": " & e.msg
    result = @[]

proc saveSymexVerdictImpl*(db: ExampleDatabase, prog: SymexProgram,
                            target: SymexTarget, settings: SymexSettings,
                            status: SymexFindingStatus,
                            soundness: Soundness,
                            errors: var seq[string],
                            gaps: seq[FindingGap] = @[]): bool {.discardable.} =
  ## Review R5 (D4a): true only when it wrote the entry.
  ## Phase 13 cycle 3. Persist a non-SAT verdict (sfUnsat /
  ## sfUnknown) under the content-addressed key with the
  ## appropriate suffix. The stored value is the sentinel empty
  ## `seq[ChoiceNode]`; `verdictCacheMaxEntries = 1` keeps the
  ## slot to a single entry so the positional load invariant
  ## `result[0] == @[]` cannot break. RFC-0005 S11: the sentinel
  ## carries `soundness` in its metadata, and a load serves it back.
  ## RFC-0005 S8av: it also carries `gaps` (the run's per-cause
  ## view, `@[]` by default for callers that have none to offer),
  ## so a verdict cache hit can report the same `gaps()` a cold run
  ## would (see `gapsMeta`/`storedGaps`).
  ##
  ## No-op for `sfSat` (use `saveSymexWitnessImpl`) and for
  ## `sfNotApplicable` (verdict is local context, not a Z3 outcome
  ## worth caching).
  ##
  ## DB save errors are appended to `errors` and the call returns
  ## normally. The cache is best-effort: a failure to persist must
  ## never abort the analysis. Callers route `errors` into
  ## `Report.dbErrors` per the documented `db.nim` contract.
  let suffix =
    case status
    of sfUnsat:   cacheKeyUnsat
    of sfUnknown: cacheKeyUnknown
    of sfSat, sfNotApplicable, sfReplayMiss: return false
      # `sfReplayMiss` (Phase 14 B5) is a per-replay diagnostic;
      # it's not a verdict and has no cache representation.
    of sfRaised: return false
      # Phase 15 E2a. An `sfRaised` finding carries a per-type id and is
      # persisted by `saveSymexRaisedImpl` (multi-finding protocol), not by
      # this single-sentinel verdict path. No-op here.
  # RFC-0005 S8bu: an `sxUnknown` some solve of whose run the wall clock
  # cut off (`queryTimeoutMs`) is the machine's, not only the program's:
  # another machine may decide it. Not cached.
  # RFC-0005 S8ca: likewise one a call declined for want of native stack
  # (`rdNativeStack`): a thread with a larger stack goes deeper.
  # RFC-0005 0.9.1 (WA-7): likewise one a replay left undecided for a reason
  # of the run (`rdReplay`): a child stopped at a resource limit, ended at the
  # replay's memory limit or by a signal from outside it, or one that could
  # not be started or handed its state at that moment. The next run tries the
  # replay again. RFC-0016 INT-32: a child killed at `replayTimeoutMs` is not
  # among them (the bound is keyed), so its verdict is stored.
  # Review R1-07: read off the `soundness` the verdict was decided under, so a
  # save after other work on this thread still reads its own run's.
  if status == sfUnknown and soundness.runDependence != {}:
    return false
  if not metaReady(db, "saveSymexVerdictImpl", errors): return false
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & suffix
  let meta = verdictMeta(soundness, gaps)
  try:
    db.save(key, @[], meta, verdictCacheMaxEntries)
    result = true
  except CatchableError as e:
    errors.add "saveSymexVerdictImpl: " & $e.name & ": " & e.msg

proc loadSymexVerdictImpl*(db: ExampleDatabase, prog: SymexProgram,
                            target: SymexTarget, settings: SymexSettings,
                            errors: var seq[string]
                           ): Option[CachedVerdict] =
  ## Phase 13 cycle 3. Cache lookup for non-SAT verdicts. Checks
  ## the `:unsat` suffix first, then `:unk` — UNSAT-first
  ## **load-order** tie-break: when both verdicts have been
  ## persisted under the same `H` (possible across `queryRLimit`
  ## bumps that turned a prior UNKNOWN into UNSAT), the stronger
  ## verdict wins regardless of save order.
  ##
  ## Returns the status (`sfUnsat` / `sfUnknown`) with its stored
  ## `Soundness` and (RFC-0005 S8av) `gaps` on hit; `none` on full
  ## miss. A sentinel without soundness metadata is a miss (S11) —
  ## soundness is load-bearing. A sentinel WITH soundness but
  ## without gaps metadata (pre-S8av, or a third-party writer) is
  ## still a HIT, served with `gaps: @[]` (`storedGaps` degrades
  ## rather than misses — see its own doc comment). Never exposes
  ## the raw `seq[seq[ChoiceNode]]` to callers — the sentinel must
  ## not leak into any code path that might pass it to
  ## `db.removeMany`.
  ##
  ## Load errors are appended to `errors` and the call degrades
  ## to a miss so the analysis can re-derive cold.
  if not metaReady(db, "loadSymexVerdictImpl", errors):
    return none(CachedVerdict)
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  template tryLoad(suffix: string, verdict: SymexFindingStatus): untyped =
    try:
      let entries = db.loadPrimaryWithMeta(baseKey & suffix)
      if entries.len == 1 and entries[0].choices.len == 0:
        let s = storedSoundness(entries[0].meta)
        let g = storedGaps(entries[0].meta)   # RFC-0016 INT-32
        if s.isSome and g.isSome:
          return some((status: verdict, soundness: s.get, gaps: g.get))
        if s.isSome:
          errors.add "loadSymexVerdictImpl: a sentinel with malformed gaps " &
            "metadata is treated as a miss"
          return none(CachedVerdict)
        errors.add "loadSymexVerdictImpl: a sentinel without soundness " &
          "metadata (pre-RFC-0005-S11 format) is treated as a miss"
    except CatchableError as e:
      errors.add "loadSymexVerdictImpl: " & $e.name & ": " & e.msg
  tryLoad(cacheKeyUnsat, sfUnsat)
  tryLoad(cacheKeyUnknown,   sfUnknown)
  none(CachedVerdict)

const cacheKeyRaisedIndex = ":raised2"
  ## Phase 15 E2a. Index slot for the multi-`sxRaised` cache protocol. The
  ## per-type sentinels live under `cacheKeyRaised(typeId)` (e.g.
  ## `:raised:ValueError`); the index here enumerates which type ids were
  ## persisted (the general example-DB has no key-prefix scan, so the set of
  ## raised types must be recorded explicitly to be reloadable).
  ## The suffix is `:raised2`, not `:raised`: records written before the
  ## all-or-nothing index format (a single-type `:raised` index was
  ## byte-identical to this one, a multi-type one was not) are never read,
  ## so every pre-existing record is a clean miss.

proc saveSymexRaisedImpl*(db: ExampleDatabase, prog: SymexProgram,
                          target: SymexTarget, settings: SymexSettings,
                          found: seq[RawResult],
                          errors: var seq[string],
                          gaps: seq[seq[FindingGap]] = @[],
                          witnesses: seq[seq[ChoiceNode]] = @[]
                         ): bool {.discardable.} =
  ## Review R5 (D4a): true only when it wrote the sentinels.
  ## Phase 15 E2a. Persist every `sxRaised` finding in `found` under the
  ## content-addressed key. STRUCTURAL multi-finding protocol: each distinct
  ## raised type id is written
  ##   (a) as a per-type sentinel under `cacheKeyRaised(typeId)` (RFC: one DB
  ##       slot per `(exnType)` finding), and
  ##   (b) as an index entry under `cacheKeyRaisedIndex` so `loadSymexRaisedImpl`
  ##       can enumerate the persisted type ids without a DB key-prefix scan.
  ## Scope: production (`symexFindAllWitnesses`) only ever saves ONE type and
  ## loads `cachedRaised[0]`; the multi-type all-or-nothing rule below serves
  ## this exported Impl API and its multi-type tests.
  ##
  ## Atomicity (none of it relies on the DB being transactional). Before any
  ## sentinel is touched an EMPTY index is written, which the loader reads as
  ## a miss; the real index, one entry listing every type id, is written
  ## last. So a save or re-save that fails part-way reads back as a MISS
  ## (the previous set is dropped as soon as the first write lands), except
  ## that a failure of the very first write leaves the previous complete
  ## set intact. It never reads back as a partial set, nor as a mix of old
  ## and new sentinels. Only a fully successful save reads back as a hit.
  ## A SUT with two distinct raise paths (e.g. ValueError, IOError) round-trips
  ## both findings through save/load. The witness rides the sentinel since
  ## RFC-0005 W1 (`witnesses`, below).
  ##
  ## RFC-0005 S8az: `gaps[i]` is `found[i]`'s per-cause view (default `@[]`
  ## for a caller that has none to offer, e.g. the hand-built multi-finding
  ## tests that construct `found` directly) — paired by INDEX into `found`,
  ## the same way `RawResult.soundness` already is, and persisted onto the
  ## same per-type sentinel the soundness rides, via `gapsMeta`/`storedGaps`.
  ##
  ## RFC-0005 W1: `witnesses[i]` is `found[i]`'s witness as `renderAsChoices`
  ## rendered it (paired by index like `gaps`, default `@[]`). It is the
  ## per-type sentinel's VALUE, and `found[i].isDefect` rides its metadata, so
  ## a hit rebuilds the finding the cold run reported (its `raised(<type>)`
  ## descriptor, `defectTypeId` and witness), not only its status.
  ##
  ## Caveat: the all-or-nothing guarantee holds for a SINGLE writer that
  ## crashes part-way. Concurrent writers to one directory DB, or a power loss
  ## without fsync, can still interleave sentinel and index writes. Every
  ## slot stays self-consistent (one entry, carrying its own soundness), so
  ## the single-type production path is unaffected; a multi-type set saved
  ## through this API by racing writers can pair one writer's sentinel for
  ## one type with another writer's for the next.
  ##
  ## DB save errors are appended to `errors` and the call returns normally — the
  ## cache is best-effort (symmetric with `saveSymexVerdictImpl`).
  # RFC-0005 0.9.1 (WA-7, WA-9): as `saveSymexWitnessImpl`.
  for raw in found:
    if not raw.soundness.cacheable: return false
    if replayedUnkeyed(prog, raw.soundness): return false   # INT-31
  if not metaReady(db, "saveSymexRaisedImpl", errors): return false
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  # Distinct type ids in first-seen order (duplicate raise paths of the same
  # type collapse to a single DB slot — the per-type key is the unit of record).
  var typeIds: seq[string] = @[]
  # RFC-0016 INT-32 (R1-33): per type, the STRONGEST finding (`claimRank`;
  # a tie keeps the earlier), with its own gaps, witness and defect-ness. It
  # kept the first, so a weaker earlier finding hid a trusted later one.
  var sounds: seq[Soundness] = @[]             ## RFC-0005 S11
  var gapsByType: seq[seq[FindingGap]] = @[]   ## RFC-0005 S8az
  var witsByType: seq[seq[ChoiceNode]] = @[]   ## RFC-0005 W1
  var defectByType: seq[bool] = @[]            ## RFC-0005 W1
  for i, raw in found:
    if raw.status != sxRaised: continue
    let g = (if i < gaps.len: gaps[i] else: @[])
    let w = (if i < witnesses.len: witnesses[i] else: @[])
    let j = typeIds.find(raw.raisedTypeId)
    if j < 0:
      typeIds.add raw.raisedTypeId
      sounds.add raw.soundness
      gapsByType.add g
      witsByType.add w
      defectByType.add raw.isDefect
    elif claimRank(raw.soundness) > claimRank(sounds[j]):
      sounds[j] = raw.soundness
      gapsByType[j] = g
      witsByType[j] = w
      defectByType[j] = raw.isDefect
  if typeIds.len == 0: return false
  try:
    # Invalidate first: the old index (if any) must not outlive the first
    # sentinel rewrite, or a torn re-save would serve new and old sentinels
    # together. An empty id list loads as a miss.
    db.save(baseKey & cacheKeyRaisedIndex, newSeq[ChoiceNode](), 1)
    for i, tid in typeIds:
      # (a) per-type sentinel slot, carrying the finding's soundness,
      # (RFC-0005 S8az) its gaps and (RFC-0005 W1) its witness, as the
      # value, and defect-ness.
      let meta = raisedMeta(sounds[i], gapsByType[i], defectByType[i])
      # Exactly ONE entry per slot: the db dedups by witness, so a roomier
      # cap would let a re-save with a different witness add a second entry,
      # which the loader (`sentinel.len == 1`) reads as a permanent miss.
      # Hardening, not a fix: `verdictCacheMaxEntries` is also 1 today; the
      # literal keeps this true if that constant moves.
      db.save(baseKey & cacheKeyRaised(tid), witsByType[i], meta, 1)
    # (b) the index, last and as ONE entry listing every type id (each as its
    # raw bytes): a reader trusts only a complete index, and one save is all
    # or nothing, so a throw above leaves the previous index (or none).
    var idx: seq[ChoiceNode] = @[]
    for tid in typeIds:
      idx.add bytesChoice(cast[seq[byte]](tid), 0, tid.len)
    db.save(baseKey & cacheKeyRaisedIndex, idx, 1)
    result = true
  except CatchableError as e:
    errors.add "saveSymexRaisedImpl: " & $e.name & ": " & e.msg

proc loadSymexRaisedImpl*(db: ExampleDatabase, prog: SymexProgram,
                          target: SymexTarget, settings: SymexSettings,
                          errors: var seq[string]): seq[CachedRaised] =
  ## Phase 15 E2a / RFC-0005 S8az. Reconstruct the full set of `sxRaised`
  ## findings from the DB without re-invoking Z3, each paired with its
  ## stored `gaps()` view. Reads the index slot (`cacheKeyRaisedIndex`) to
  ## enumerate the persisted type ids and rebuilds one
  ## `(raw: RawResult{status: sxRaised, raisedTypeId, isDefect, soundness},
  ## gaps, choices)` per entry (RFC-0005 W1: `choices` is the stored witness,
  ## `isDefect` its stored defect-ness). The index is the enumeration source; RFC-0005 S11: the
  ## per-type sentinel (`cacheKeyRaised(typeId)`) carries the finding's
  ## `Soundness`, and a type whose sentinel is missing or has no soundness
  ## metadata is a miss. RFC-0005 S8az: the SAME sentinel also carries
  ## `gaps` metadata (`gapsMeta`/`storedGaps`); missing/pre-S8az gaps
  ## metadata degrades to `@[]` rather than a miss — gaps stays
  ## best-effort on top of the load-bearing soundness. Returns `@[]` on a
  ## miss; a sentinel missing for any indexed type makes it a full miss.
  ##
  ## Load errors are appended to `errors` and the call degrades to a miss
  ## (symmetric with `loadSymexVerdictImpl`). Best-effort.
  if not metaReady(db, "loadSymexRaisedImpl", errors): return
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  try:
    let entries = db.loadPrimary(baseKey & cacheKeyRaisedIndex)
    # One entry lists every type id; anything else is not this encoding.
    if entries.len != 1: return
    var loaded: seq[CachedRaised] = @[]
    for node in entries[0]:
      if node.kind != ckBytes:
        errors.add "loadSymexRaisedImpl: malformed raised index; a miss"
        return
      let tid = cast[string](node.bytesVal)
      for prev in loaded:
        if prev.raw.raisedTypeId == tid:
          errors.add "loadSymexRaisedImpl: raised index lists " & tid &
            " twice; a miss"
          return
      let sentinel = db.loadPrimaryWithMeta(baseKey & cacheKeyRaised(tid))
      # RFC-0005 W1: the value is the raise's witness (it was `@[]`), so a
      # sentinel is any single entry; its soundness still decides a hit.
      let s =
        if sentinel.len == 1: storedSoundness(sentinel[0].meta)
        else: none(Soundness)
      let g =
        if sentinel.len == 1: storedGaps(sentinel[0].meta)
        else: none(seq[FindingGap])
      if s.isSome and g.isNone:
        # RFC-0016 INT-32: a sentinel whose gaps are malformed is no record.
        errors.add "loadSymexRaisedImpl: raised(" & tid & ") has malformed " &
          "gaps metadata; a miss"
        return
      if s.isNone:
        # A hit needs the complete set the index describes.
        errors.add "loadSymexRaisedImpl: raised(" & tid & ") has no " &
          "soundness-carrying sentinel, or more than one entry (torn " &
          "save); a miss"
        return
      loaded.add (raw: RawResult(status: sxRaised, raisedTypeId: tid,
                                 isDefect: storedRaisedDefect(
                                   sentinel[0].meta),
                                 soundness: s.get),
                  gaps: g.get,
                  choices: sentinel[0].choices)
    result = loaded
  except CatchableError as e:
    errors.add "loadSymexRaisedImpl: " & $e.name & ": " & e.msg
    result = @[]

proc toFindingStatus*(s: SymexStatusKind): SymexFindingStatus =
  case s
  of sxSat:     sfSat
  of sxUnsat:   sfUnsat
  of sxUnknown: sfUnknown
  of sxRaised:  sfRaised   ## Phase 15 E2a

# ---- RFC-0016 INT-38 (0005 review R8-04): the opt-in prune ------------------

proc pruneForeignSymexRecords*(db: ExampleDatabase): int =
  ## RFC-0016 INT-38 (0005 review R8-04). Removes every symex cache record
  ## `db` holds that a walker other than this build's wrote, and returns how
  ## many records (DB keys) it emptied. A record's walker is read off its key
  ## (`walkerVersionOfKey`): the `sx:`/`sx2:` keys before RFC-0016 INT-34
  ## (their `:raised` indexes and slots among them) and every `w<n>:` key of
  ## another `n` are foreign. A key that is not a symex record (a test id) and
  ## this walker's records are left alone.
  ##
  ## Explicit and opt-in: no run calls it. A walker bump makes every earlier
  ## record a miss, never a deletion, so a build rolled back to an earlier
  ## walker still finds its records. On a `multiplexedDatabase` it sweeps the
  ## writable side only. Raises `DbError` for a backend that cannot list its
  ## keys (`primaryKeysImpl`) or cannot be written (`readOnlyDatabase`).
  for key in db.primaryKeys():
    let v = walkerVersionOfKey(key)
    if v.isNone or v.get == symexWalkerVersion: continue
    let entries = db.loadPrimary(key)
    if entries.len == 0: continue
    db.removeMany(key, entries)
    inc result
