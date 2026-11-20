## nelli/smt/symex_codec -- the symex cache's record encodings, with no I/O:
## the stored `Soundness`, the `gaps()` view, the `:notes` record's hints,
## diagnostics and undefined entries, and a raised sentinel's defect flag,
## each as an encode into entry metadata and its inverse; and the projections
## of a run's errors and findings onto the Z3-free `Finding*` types.
##
## RFC-0016 INT-34 C1: moved out of `symex_cache.nim` unchanged, so the
## encodings can be read and round-tripped without an `ExampleDatabase`.
## `symex_cache` keys the records and reads and writes them; every byte of the
## metadata a record carries is decided here.

import std/[tables, options, strutils]
import ../choice
import ./types
import ./witness_render
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

proc encodeSoundness*(s: Soundness): string =
  result = soundnessMetaVersion & ":" & digit(taintBits(s.pathTaint)) & ":" &
    digit(taintBits(s.runTaint)) & ":" & digit(ord(s.replay)) & ":" &
    digit(ord(s.witnessUnsafe)) & ":" & $undefinedBits(s.witnessUndefined)
  if s.runDependence != {}:
    result.add ":" & digit(runDependenceBits(s.runDependence))

proc decodeSoundness*(v: string): Option[Soundness] =
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

proc soundnessMeta*(s: Soundness): Table[string, string] =
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

proc gapsMeta*(gaps: seq[FindingGap]): Table[string, string] =
  result = initTable[string, string]()
  result[gapsVersionMetaKey] = gapsVersion
  result[gapsCountMetaKey] = $gaps.len
  for i, g in gaps:
    result["gapsc" & $i] = $ord(g.class)
    result["gapsk" & $i] = $g.kind
    result["gapsm" & $i] = g.msg

proc storedGaps*(meta: Table[string, string]): Option[seq[FindingGap]] =
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

proc storedSoundness*(meta: Table[string, string]): Option[Soundness] =
  if soundnessMetaKey notin meta: return none(Soundness)
  decodeSoundness(meta[soundnessMetaKey])

# ---- The projections onto the Z3-free `Finding*` types ----------------------

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

# ---- RFC-0005 W1: the `:notes` record's metadata ---------------------------
#
# The record's layout (its keys, which entry holds what) is `symex_cache`'s;
# the metadata of each entry is encoded here. The head carries the version,
# the hints (one key set per hint, as `gapsMeta` does, so no message needs
# escaping) and the diagnostic and undefined counts; each diagnostic and each
# undefined entry carries its own metadata beside its witness.

const notesVersionMetaKey* = "notesv"
const notesVersion = "1"

proc notesHeadMeta*(hints: seq[FindingHint]; diagnostics: int;
                    undefined: int): Table[string, string] =
  ## The `:notes` head entry's metadata: the hints and the counts of the
  ## diagnostic and undefined entries beside it.
  result = initTable[string, string]()
  result[notesVersionMetaKey] = notesVersion
  result["hintn"] = $hints.len
  for i, h in hints:
    result["hintk" & $i] = $h.kind
    result["hints" & $i] = $h.severity
    result["hintm" & $i] = h.msg
  result["diagn"] = $diagnostics
  result["undefn"] = $undefined   # RFC-0016 K10a-target

proc storedNotesCounts*(meta: Table[string, string]
                       ): Option[tuple[hints, diagnostics, undefined: int]] =
  ## The counts `notesHeadMeta` wrote; `none` for a head not in this encoding
  ## (another version, the invalidated head, a count that is not a number).
  ## A head without an undefined count (written before K10a-target) has none.
  if meta.getOrDefault(notesVersionMetaKey, "") != notesVersion:
    return none(tuple[hints, diagnostics, undefined: int])
  try:
    some((hints: parseInt(meta.getOrDefault("hintn", "")),
          diagnostics: parseInt(meta.getOrDefault("diagn", "")),
          undefined: parseInt(meta.getOrDefault("undefn", "0"))))
  except ValueError:
    none(tuple[hints, diagnostics, undefined: int])

proc storedHints*(meta: Table[string, string]; n: int): seq[FindingHint] =
  ## The hints `notesHeadMeta` wrote, up to the first of the `n` that is
  ## missing or unreadable.
  for i in 0 ..< n:
    if ("hintk" & $i) notin meta: break
    # RFC-0016 INT-34: the record keeps each enum by name; a name this build
    # does not know ends the list, as a missing entry does.
    let kind = storedEnum[SymexErrorKind](meta["hintk" & $i])
    let severity = storedEnum[SymexErrorSeverity](
      meta.getOrDefault("hints" & $i, ""))
    if kind.isNone or severity.isNone: break
    result.add FindingHint(kind: kind.get, severity: severity.get,
                           msg: meta.getOrDefault("hintm" & $i, ""))

proc diagnosticMeta*(d: FindingDiagnostic): Table[string, string] =
  ## A diagnostic entry's metadata; its witness is the entry's value.
  result = initTable[string, string]()
  result["tid"] = d.raisedTypeId
  result["def"] = (if d.isDefect: "1" else: "0")
  result["msg"] = d.raisedMsg
  result["wx"] = (if d.witnessUnsafe: "1" else: "0")

proc storedDiagnostic*(meta: Table[string, string];
                       choices: seq[ChoiceNode]): Option[FindingDiagnostic] =
  ## The inverse of `diagnosticMeta`, `choices` the entry's value; `none` for
  ## an entry with no type id.
  if "tid" notin meta: return none(FindingDiagnostic)
  some(FindingDiagnostic(
    raisedTypeId: meta["tid"],
    isDefect: meta.getOrDefault("def", "") == "1",
    raisedMsg: meta.getOrDefault("msg", ""),
    witnessChoices: choices,
    witnessUnsafe: meta.getOrDefault("wx", "") == "1"))

proc undefinedMeta*(u: FindingUndefined): Table[string, string] =
  ## RFC-0016 K10a-target. An undefined entry's metadata; its witness is the
  ## entry's value.
  result = initTable[string, string]()
  result["kind"] = u.kind
  result["site"] = u.site

proc storedUndefined*(meta: Table[string, string];
                      choices: seq[ChoiceNode]): Option[FindingUndefined] =
  ## The inverse of `undefinedMeta`, `choices` the entry's value; `none` for
  ## an entry with no kind.
  if "kind" notin meta: return none(FindingUndefined)
  some(FindingUndefined(kind: meta["kind"],
                        site: meta.getOrDefault("site", ""),
                        witnessChoices: choices))

# ---- A verdict's, a witness's and a raised sentinel's metadata -------------

proc verdictMeta*(s: Soundness; gaps: seq[FindingGap]): Table[string, string] =
  ## The metadata every verdict-carrying entry (a `:sat` witness, a `:unsat` /
  ## `:unk` sentinel, a `:raised:<type>` sentinel) carries: its soundness and
  ## (RFC-0005 S8av/S8az) its gaps.
  result = soundnessMeta(s)
  for k, v in gapsMeta(gaps): result[k] = v

const raisedDefectMetaKey = "rdef"
  ## RFC-0005 W1. The `:raised:<type>` sentinel's `RawResult.isDefect`.

proc raisedMeta*(s: Soundness; gaps: seq[FindingGap];
                 isDefect: bool): Table[string, string] =
  ## A `:raised:<type>` sentinel's metadata: `verdictMeta` and (RFC-0005 W1)
  ## the finding's defect-ness.
  result = verdictMeta(s, gaps)
  result[raisedDefectMetaKey] = (if isDefect: "1" else: "0")

proc storedRaisedDefect*(meta: Table[string, string]): bool =
  ## The defect-ness `raisedMeta` wrote; false when it is absent.
  meta.getOrDefault(raisedDefectMetaKey, "") == "1"
