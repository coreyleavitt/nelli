## nelli/smt/symex_cache -- the content-addressed record codecs behind the
## symex DB API: the stored `Soundness` and `gaps()`, the `:notes` record, and
## the save/load of witnesses, verdicts and raised-exception entries.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The `*Impl` procs are
## re-exported by `symex.nim` (generated code and the cache tests name them);
## the macro forms that call them stay in the facade.

import std/[tables, sets, options, strutils]
from z3 import z3FullVersion
import ../choice
import ./witness_render
import ../db
import ./dsl
import ./canonicalize
import ../engine/types as engineTypes

# ---- RFC-0005 S11 (§7): the cache value carries the Soundness ---------------
#
# Every persisted verdict -- a `:sat` witness, the `:unsat` / `:unk`
# sentinel, each `:raised:<type>` sentinel -- carries its `Soundness` in the
# entry's metadata (`db.save(..., meta)`), under `soundnessMetaKey`. The
# stored value KEEPS its pre-S11 shape (the choices, or the `@[]` sentinel);
# only the metadata is new. A hit serves the stored record unchanged, so a
# replay-confirmed SAT stays `rsConfirmed` and an UNKNOWN keeps its run
# coordinate; an entry WITHOUT the metadata (the pre-S11 format) cannot say
# what it was proved under, so it is a miss -- never a clean verdict. The
# walker-version segment of the key (`symexWalkerVersion`, bumped by S11)
# already orphans every pre-S11 entry; the miss rule is the backstop for a
# third-party write under a current key. Replay precedes persist (S10): only
# a settled result is ever saved.

const soundnessMetaKey = "soundness"
  ## The metadata key of the stored `Soundness`.
const soundnessMetaVersion = "4"
  ## The encoding's own version:
  ## `"4:<pathTaint>:<runTaint>:<replay>:<unsafe>:<undefined>"`, each taint a
  ## bitmask over `SoundnessChannel` ordinals, `replay` the `ReplayStatus`'s
  ## ordinal and `unsafe` `witnessUnsafe` as `0`/`1`. RFC-0016 W1-d3: the
  ## sixth field is `witnessUndefined`, a canonical decimal integer of any
  ## length (no leading zeros): the bitmask over `ord(k) - ord(low(UbKind))`
  ## (five members need two digits, and a later one must not need a format
  ## change; the static pin in `smt/types.nim` bounds it below 30 bits).
  ## A non-empty `runDependence` follows as an optional seventh field, a
  ## bitmask over `RunDependence` ordinals (review R1-07); without it the
  ## record reads as `{}`. The seventh is told by FIELD COUNT (7 vs 6), never
  ## by guessing at a field's value. Anything else decodes as a miss, so a
  ## change to any of these enums' order, or to what a field means, bumps the
  ## version. A version 3 record has no undefined field and cannot say what
  ## it was proved under: a miss (a cold start), not an error. Review R2 (DD1):
  ## version 3 is the one where `witnessUnsafe` also marks an unconfirmed
  ## witness whose replay ended its child; a version 2 record cannot say so,
  ## and is a miss.

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

func taintBits(t: Taint): int =
  for c in t: result = result or (1 shl ord(c))

func runDependenceBits(d: set[RunDependence]): int =
  for c in d: result = result or (1 shl ord(c))

# Review R3 (E8). Encoding version 3 writes these enums' ordinals, so their
# order IS the format. Pinned here: reordering, inserting or appending a member
# fails to compile, and the fix is a new `soundnessMetaVersion` (and this pin).
# Every field is one decimal digit (`decodeSoundness` reads exactly one), so
# the largest value each can take must stay below 10.
const
  allBits = (1 shl (ord(high(SoundnessChannel)) + 1)) - 1
    ## The largest taint bitset a field holds (review R4, X4: defined once,
    ## used by the pins below and `decodeSoundness`).
  allRunBits = (1 shl (ord(high(RunDependence)) + 1)) - 1
static:
  doAssert ord(scSpurious) == 0 and ord(scIncomplete) == 1 and
           high(SoundnessChannel) == scIncomplete
  doAssert ord(rsUnsettled) == 0 and ord(rsNotNeeded) == 1 and
           ord(rsConfirmed) == 2 and ord(rsUnconfirmed) == 3 and
           ord(rsRefused) == 4 and high(ReplayStatus) == rsRefused
  doAssert ord(rdQueryTimeout) == 0 and ord(rdNativeStack) == 1 and
           ord(rdReplay) == 2 and high(RunDependence) == rdReplay
  doAssert allBits <= 9 and allRunBits <= 9 and ord(high(ReplayStatus)) <= 9
  doAssert ord(high(UbKind)) - ord(low(UbKind)) < 30   # also pinned in smt/types

func undefinedBits(u: set[UbOrdinal]): int =
  ## RFC-0016 W1-d3. The sixth field's value: bit `i` is `UbOrdinal` `i`.
  for o in u: result = result or (1 shl int(o))

func digit(n: int): char =
  ## One field of the encoding. Review R3 (E8): never two digits, which
  ## `decodeSoundness` would read as a miss. The static pins above bound
  ## every field (the largest is `allBits`, `allRunBits` or the last
  ## `ReplayStatus`), so no runtime check is needed.
  char(ord('0') + n)

proc encodeSoundness(s: Soundness): string =
  result = soundnessMetaVersion & ":" & digit(taintBits(s.pathTaint)) & ":" &
    digit(taintBits(s.runTaint)) & ":" & digit(ord(s.replay)) & ":" &
    digit(ord(s.witnessUnsafe)) & ":" & $undefinedBits(s.witnessUndefined)
  if s.runDependence != {}:
    result.add ":" & digit(runDependenceBits(s.runDependence))

proc decodeSoundness(v: string): Option[Soundness] =
  ## The inverse of `encodeSoundness`; `none` for anything it did not write.
  let parts = v.split(':')
  if parts.len notin {6, 7} or parts[0] != soundnessMetaVersion:
    return none(Soundness)
  var nums: array[6, int]    # [0..3] the fixed digits, [4] undefined, [5] run
  for i in 1 ..< parts.len:
    if i == 5:
      # RFC-0016 W1-d3: a canonical decimal of any length, at most 30 bits.
      # A `var` copy, not a `let`: the S8ab self-audit refuses a compile-time
      # `let` alias of a managed element (`decodeSoundness` is VM-reachable).
      var t = parts[i]
      if t.len == 0 or t.len > 10 or (t.len > 1 and t[0] == '0'):
        return none(Soundness)
      for ch in t:
        if ch notin {'0' .. '9'}: return none(Soundness)
      let v = parseBiggestInt(t)
      if v >= (1'i64 shl (ord(high(UbKind)) - ord(low(UbKind)) + 1)):
        return none(Soundness)
      nums[4] = int(v)
    else:
      if parts[i].len != 1 or parts[i][0] notin {'0' .. '9'}:
        return none(Soundness)
      nums[if i < 5: i - 1 else: 5] = ord(parts[i][0]) - ord('0')
  if nums[0] > allBits or nums[1] > allBits or
     nums[2] > ord(high(ReplayStatus)) or nums[3] > 1 or
     (parts.len == 7 and nums[5] notin 1 .. allRunBits):
    return none(Soundness)
  var s = Soundness(replay: ReplayStatus(nums[2]), witnessUnsafe: nums[3] == 1)
  for o in UbOrdinal.low .. UbOrdinal.high:
    if (nums[4] and (1 shl int(o))) != 0: s.witnessUndefined.incl o
  for c in SoundnessChannel:
    if (nums[0] and (1 shl ord(c))) != 0: s.pathTaint.incl c
    if (nums[1] and (1 shl ord(c))) != 0: s.runTaint.incl c
  for d in RunDependence:
    if (nums[5] and (1 shl ord(d))) != 0: s.runDependence.incl d
  some(s)

proc soundnessMeta(s: Soundness): Table[string, string] =
  result = initTable[string, string]()
  result[soundnessMetaKey] = encodeSoundness(s)

# ---- RFC-0005 S8av/S8az: every verdict/witness/raised cache value also -----
# ---- carries `gaps()` ------------------------------------------------------
#
# S11's remainder (§8.1's "Different mechanisms" list): a served cache hit
# returned `gaps: @[]` even when the run that produced it had a non-empty
# per-cause view, because only `Soundness` rode the entry metadata. S8av
# widened the `:unsat`/`:unk` verdict slot only (`CachedVerdict`); S8az
# widens the two remaining slots the SAME way: the `:sat` witness entry
# (`CachedWitness`, via `saveSymexWitnessImpl`/`loadSymexWitnessesImpl`) and
# each `:raised:<type>` sentinel (`CachedRaised`, via
# `saveSymexRaisedImpl`/`loadSymexRaisedImpl`). All three share this ONE
# encode/decode pair rather than each growing its own — `gapsMeta`/
# `storedGaps` take and return a plain `Table[string, string]`, so any
# metadata-carrying entry can fold them into its own `meta` table alongside
# `soundnessMeta`. `FindingGap` is already Z3-free (`class`, `kind`, `msg` —
# see `findingGaps`), so it is stored the same way: each gap gets its OWN
# set of metadata keys (`gapsc<i>`/`gapsk<i>`/`gapsm<i>`), sidestepping any
# need to escape `msg` (an arbitrary, user-influenced string) inside a
# single delimited value the way `encodeSoundness` can for its
# always-one-digit fields. A `gapsnMetaKey`/`gapsVersionMetaKey` pair marks
# how many entries to read back and which encoding wrote them, mirroring
# `soundnessMetaVersion`. Missing metadata degrades to `@[]`; RFC-0016 INT-32:
# malformed metadata is a miss of the whole record, never a prefix of it.

const gapsVersionMetaKey = "gapsv"
const gapsVersion = "1"
const gapsCountMetaKey = "gapsn"

func storedEnum[E: enum](name: string): Option[E] =
  ## RFC-0016 INT-34. A `FindingGap`/`FindingHint` enum as the cache stores it,
  ## by name (the form records before INT-34 used, so they still read). `none`
  ## for a name this build does not know. Never raises.
  for e in E:
    if $e == name: return some(e)
  none(E)

proc gapsMeta(gaps: seq[FindingGap]): Table[string, string] =
  result = initTable[string, string]()
  result[gapsVersionMetaKey] = gapsVersion
  result[gapsCountMetaKey] = $gaps.len
  for i, g in gaps:
    result["gapsc" & $i] = $ord(g.class)
    result["gapsk" & $i] = $g.kind
    result["gapsm" & $i] = g.msg

proc storedGaps(meta: Table[string, string]): Option[seq[FindingGap]] =
  ## The inverse of `gapsMeta`. `some(@[])` for a record with no gaps metadata
  ## at all (written before S8av/S8az, or by a writer that records none).
  ## RFC-0016 INT-32 (R1-33): `none` for gaps metadata that is present but not
  ## this encoding or not whole (another version, a count that is not a
  ## number, an entry missing or out of range), and every caller reads that as
  ## a miss of the WHOLE record. It served the gaps up to the break, so a hit
  ## could report fewer gaps than the cold run had. Never raises.
  if gapsVersionMetaKey notin meta: return some(newSeq[FindingGap]())
  if meta[gapsVersionMetaKey] != gapsVersion: return none(seq[FindingGap])
  var n: int
  try: n = parseInt(meta.getOrDefault(gapsCountMetaKey, ""))
  except ValueError: return none(seq[FindingGap])
  if n < 0: return none(seq[FindingGap])
  var gaps: seq[FindingGap]
  for i in 0 ..< n:
    let cKey = "gapsc" & $i
    let kKey = "gapsk" & $i
    let mKey = "gapsm" & $i
    if cKey notin meta or kKey notin meta or mKey notin meta:
      return none(seq[FindingGap])
    var classOrd: int
    try: classOrd = parseInt(meta[cKey])
    except ValueError: return none(seq[FindingGap])
    if classOrd < ord(low(DegradeClass)) or classOrd > ord(high(DegradeClass)):
      return none(seq[FindingGap])
    let kind = storedEnum[SymexErrorKind](meta[kKey])
    if kind.isNone: return none(seq[FindingGap])
    gaps.add FindingGap(class: DegradeClass(classOrd), kind: kind.get,
                        msg: meta[mKey])
  some(gaps)

proc storedSoundness(meta: Table[string, string]): Option[Soundness] =
  if soundnessMetaKey notin meta: return none(Soundness)
  decodeSoundness(meta[soundnessMetaKey])

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

proc findingGaps*(errors: seq[SymexErrorInfo]): seq[FindingGap] =
  ## RFC-0005 S11. `gapsOf` projected onto the Z3-free `FindingGap`.
  for g in gapsOf(errors):
    result.add FindingGap(class: g.class, kind: g.e.kind, msg: g.e.msg)

proc findingHints*(errors: seq[SymexErrorInfo]): seq[FindingHint] =
  ## RFC-0005 W1. The complement of `findingGaps`: every entry `taintsRun`
  ## does not admit (a hint, or a warning that decides nothing), in order.
  ## `gapsOf` leaves these out by design; without this projection a
  ## `SymexFinding` never showed them, the replay outcomes among them.
  for e in errors:
    if not taintsRun(e):
      result.add FindingHint(kind: e.kind, severity: e.severity, msg: e.msg)

proc findingDiagnostics*[T](ds: seq[DefectFinding[T]]): seq[FindingDiagnostic] =
  ## RFC-0005 W1. `SymexResult.diagnostics` projected onto the Z3-free
  ## `FindingDiagnostic`, the witness rendered as `witnessChoices` is.
  for d in ds:
    result.add FindingDiagnostic(raisedTypeId: d.raisedTypeId,
                                 isDefect: d.isDefect, raisedMsg: d.raisedMsg.get(""),
                                 witnessChoices: renderAsChoices(d.witness),
                                 witnessUnsafe: d.witnessUnsafe)

proc findingUndefined*[T](us: seq[UndefinedFinding[T]]): seq[FindingUndefined] =
  ## RFC-0016 K10a-target. `SymexResult.undefined` projected onto the Z3-free
  ## `FindingUndefined`, the witness rendered as `witnessChoices` is.
  for u in us:
    result.add FindingUndefined(kind: $u.kind, site: u.site,
                                witnessChoices: renderAsChoices(u.witness))
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
const notesVersionMetaKey = "notesv"
const notesVersion = "1"

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
  var meta = initTable[string, string]()
  meta[notesVersionMetaKey] = notesVersion
  meta["hintn"] = $hints.len
  for i, h in hints:
    meta["hintk" & $i] = $h.kind
    meta["hints" & $i] = $h.severity
    meta["hintm" & $i] = h.msg
  meta["diagn"] = $diagnostics.len
  meta["undefn"] = $undefined.len   # RFC-0016 K10a-target
  try:
    # RFC-0016 INT-38 (R6-07): a head the loader refuses first, so a re-save
    # that fails part-way never serves the earlier record's head over a mix
    # of its slots and this save's. A failure of this first write leaves the
    # earlier record whole.
    db.save(baseKey & cacheKeyNotes, @[],
            {notesVersionMetaKey: "-"}.toTable, verdictCacheMaxEntries)
    for i, u in undefined:
      var um = initTable[string, string]()
      um["kind"] = u.kind
      um["site"] = u.site
      db.save(notesKey(baseKey, i).replace(":diag:", ":undef:"),
              u.witnessChoices, um, verdictCacheMaxEntries)
    for i, d in diagnostics:
      var dm = initTable[string, string]()
      dm["tid"] = d.raisedTypeId
      dm["def"] = (if d.isDefect: "1" else: "0")
      dm["msg"] = d.raisedMsg
      dm["wx"] = (if d.witnessUnsafe: "1" else: "0")
      db.save(notesKey(baseKey, i), d.witnessChoices, dm,
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
    if meta.getOrDefault(notesVersionMetaKey, "") != notesVersion: return
    var nh, nd, nu: int
    try:
      nh = parseInt(meta.getOrDefault("hintn", ""))
      nd = parseInt(meta.getOrDefault("diagn", ""))
      nu = parseInt(meta.getOrDefault("undefn", "0"))
    except ValueError: return
    for i in 0 ..< nu:
      let e = db.loadPrimaryWithMeta(
        notesKey(baseKey, i).replace(":diag:", ":undef:"))
      if e.len != 1 or "kind" notin e[0].meta: break
      result.undefined.add FindingUndefined(
        kind: e[0].meta["kind"],
        site: e[0].meta.getOrDefault("site", ""),
        witnessChoices: e[0].choices)
    for i in 0 ..< nh:
      if ("hintk" & $i) notin meta: break
      # RFC-0016 INT-34: the record keeps each enum by name; a name this build
      # does not know ends the list, as a missing entry does.
      let kind = storedEnum[SymexErrorKind](meta["hintk" & $i])
      let severity = storedEnum[SymexErrorSeverity](
        meta.getOrDefault("hints" & $i, ""))
      if kind.isNone or severity.isNone: break
      result.hints.add FindingHint(kind: kind.get, severity: severity.get,
                                   msg: meta.getOrDefault("hintm" & $i, ""))
    for i in 0 ..< nd:
      let e = db.loadPrimaryWithMeta(notesKey(baseKey, i))
      if e.len != 1 or "tid" notin e[0].meta: break
      result.diagnostics.add FindingDiagnostic(
        raisedTypeId: e[0].meta["tid"],
        isDefect: e[0].meta.getOrDefault("def", "") == "1",
        raisedMsg: e[0].meta.getOrDefault("msg", ""),
        witnessChoices: e[0].choices,
        witnessUnsafe: e[0].meta.getOrDefault("wx", "") == "1")
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
  var meta = soundnessMeta(finding.soundness)
  for k, v in gapsMeta(finding.gaps): meta[k] = v   ## RFC-0005 S8az
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
  var meta = soundnessMeta(soundness)
  for k, v in gapsMeta(gaps): meta[k] = v
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

const raisedDefectMetaKey = "rdef"
  ## RFC-0005 W1. The `:raised:<type>` sentinel's `RawResult.isDefect`.

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
      var meta = soundnessMeta(sounds[i])
      for k, v in gapsMeta(gapsByType[i]): meta[k] = v
      meta[raisedDefectMetaKey] = (if defectByType[i]: "1" else: "0")
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
                                 isDefect: sentinel[0].meta.getOrDefault(
                                   raisedDefectMetaKey, "") == "1",
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
