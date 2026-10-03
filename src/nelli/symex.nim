## nelli/symex — public-API entry for the symbolic-execution capability.
##
## See:
##   * docs/SYMEX_PLAN.md     — build plan + scope
##   * docs/symex/ADR-0001-integer-semantics.md
##   * docs/symex/ADR-0002-dsl-factoring.md
##
## Phase 1 supports a small Nim fragment: int/bool params + locals,
## arithmetic + comparison + boolean, `if` / `elif` / `else`, the
## three body markers below. Each later phase widens the fragment.
##
## Body markers — `symexTarget`/`symexAssert`/`symexAssume` are
## `proc {.inline.}`, not templates, so the same SUT is simultaneously
## walkable by symex AND runnable under random PBT without source
## duplication. They are defined in `src/nelli/engine/markers.nim` and
## merely re-exported here by name (see :145-153) for `import nelli/symex`
## callers; they are also reachable from a bare `import nelli` via the
## `engine` export chain (RFC-z3-optional S1c), so a marker-annotated SUT
## survives the 0.7.0 break without importing this Z3-bound module.
## Outside symex:
##
##   * `symexTarget(name)`  — usually a no-op, but calls
##                            `symexCaptureRecord`, which feeds the
##                            `{.threadvar.}` capture context backing
##                            `assertCoveredBy`; a no-op only when no
##                            capture is active on this thread
##   * `symexAssert(cond)`  — `doAssert cond` (it's a stated invariant)
##   * `symexAssume(cond)`  — no-op; Phase 1 recognizes it in the parser
##                            but does not yet restrict the SUT's
##                            normal-run input domain

import std/[macros, sets, tables, algorithm, options, strutils, importutils]
import z3
export z3.z3FullVersion
import ./choice
export choice
import ./smt/dsl
export dsl
import ./smt/scan
from ./smt/scoped_names import isModuleGlobal   ## RFC-0005 S8bn
import ./engine/types as engineTypes
export engineTypes.SymexFinding, engineTypes.SymexFindingStatus,
       engineTypes.FindingGap, engineTypes.trusted   ## RFC-0005 S11

# ---- Witness → ChoiceNode bridge -------------------------------------------
#
# A symex witness is a Nim tuple (the proc's parameter list). Phase 7
# linearises it into a `seq[ChoiceNode]` so the same regression-seed
# substrate nelli already uses for random examples can carry
# symex-derived counterexamples. The encoding is deterministic and
# length-prefixed for variable-cardinality container shapes.

const sxIntMin = low(int64)
const sxIntMax = high(int64)
const sxLenMax = high(int64)

proc sortedKeysOf[K, V](t: Table[K, V]): seq[K] =
  ## Returns `t`'s keys in deterministic ascending order. Used by
  ## `renderAsChoices` to defeat Nim's undefined hash-iteration
  ## order so identical witnesses produce identical choice
  ## sequences. Local helper to dodge z3's shadowing of
  ## `tables.keys` at the `renderAsChoices` call-site scope.
  for k, _ in t: result.add k
  sort(result)

proc sortedElemsOf[E](s: HashSet[E]): seq[E] =
  ## HashSet counterpart of `sortedKeysOf`.
  for e in s: result.add e
  sort(result)

proc renderInto[T](w: T; res: var seq[ChoiceNode]; cells: var seq[pointer]) =
  ## The body of `renderAsChoices`. `cells` lists the ref / ptr cells
  ## rendered so far, in rendering order (RFC-0005 S8n): the one piece of
  ## state a witness graph needs, since a cell reached twice (an alias, a
  ## cycle) renders as a back-reference the second time.
  when T is bool:
    res.add booleanChoice(w, 0.5)
  elif T is SomeFloat:
    # Phase 15 F7: a symex float witness rides as a single `floatChoice`.
    # The constraint window is fully permissive — `[-Inf, +Inf]`, `allowNan
    # = true`, `smallestNonzeroMagnitude = 0.0` — so any IEEE-754 bit pattern
    # (NaN, ±Inf, subnormals, ±0) passes `permits` and round-trips through the
    # choice IR / `floats` replay strategy. `floatVal` is a float64, so a
    # float32 witness widens losslessly on the way in and narrows back on read.
    res.add floatChoice(float64(w), -Inf, Inf, allowNan = true,
                           smallestNonzeroMagnitude = 0.0)
  elif T is SomeSignedInt:
    res.add integerChoice(int64(w), sxIntMin, sxIntMax, 0'i64)
  elif T is SomeUnsignedInt:
    # Symex's uint widths fit in int64 modulo width; cast for the
    # constraint window. Witness values are non-negative.
    res.add integerChoice(int64(w), 0'i64, sxIntMax, 0'i64)
  elif T is string:
    # Full Unicode minus the UTF-16 surrogate block — `intervals`
    # rejects any range intersecting `[surrogateLo, surrogateHi]`.
    res.add stringChoice(w,
      intervals(@[(0'i32, surrogateLo - 1),
                   (surrogateHi + 1, maxCodepoint)]),
      0, w.len)
  elif T is array:
    for e in w:
      renderInto(e, res, cells)
  elif T is seq:
    # Continue-boolean protocol matching `lists`/`tables`/`sets`
    # strategies (strategy.nim:406-475): each element preceded by
    # `drawBoolean(0.9)` = true, list terminated by a final false.
    # The old length-prefix encoding was incompatible with replay
    # through these strategies; renderAsChoicesVersion bumps "1"
    # → "2" to invalidate stale collection witnesses in the DB.
    for e in w:
      res.add booleanChoice(true, 0.9)
      renderInto(e, res, cells)
    res.add booleanChoice(false, 0.9)
  elif T is HashSet:
    # Sort by element before iterating: Nim's HashSet iteration
    # order is undefined, and the cache key is content-addressed on
    # the choice sequence — same logical witness must round-trip to
    # identical choices across runs.
    for e in sortedElemsOf(w):
      res.add booleanChoice(true, 0.9)
      renderInto(e, res, cells)
    res.add booleanChoice(false, 0.9)
  elif T is Table:
    # Sort by key for the same determinism reason.
    for k in sortedKeysOf(w):
      res.add booleanChoice(true, 0.9)
      renderInto(k, res, cells)
      renderInto(w[k], res, cells)
    res.add booleanChoice(false, 0.9)
  elif T is ref or T is ptr:
    # RFC-0005 S8n: a ref / ptr witness is one integer tag, then its pointee:
    # 0 = nil; 1 = a cell not rendered before, followed by the pointee's
    # choices; k + 2 = the k-th cell already rendered (an alias or a cycle),
    # with nothing after it. The bounds are [0, 1 + cells rendered so far],
    # so a tree-shaped witness is all 0 / 1 tags. Before S8n a ref had no
    # arm: a SUT with a ref param could not reach `assertCoveredBy` or a
    # `symex` phase at all (the `{.error.}` below, at compile time). Keeping
    # identity makes the encoding total over cyclic witnesses and tells an
    # aliased pair from two equal cells.
    let hi = int64(cells.len + 1)
    if w == nil:
      res.add integerChoice(0'i64, 0'i64, hi, 0'i64)
    else:
      let cell = cast[pointer](w)
      let seen = cells.find(cell)
      if seen >= 0:
        res.add integerChoice(int64(seen + 2), 0'i64, hi, 0'i64)
      else:
        res.add integerChoice(1'i64, 0'i64, hi, 0'i64)
        cells.add cell
        renderInto(w[], res, cells)
  elif T is tuple:
    for f in fields(w):
      renderInto(f, res, cells)
  elif T is enum:
    # Phase 11 cycle 8 — enums (and variant discriminators) ride as
    # integer choices keyed on ordinal value. shrinkTowards points
    # at low(T) so the shrinker collapses to the first enum
    # constant by convention.
    res.add integerChoice(int64(ord(w)),
                              int64(ord(low(T))), int64(ord(high(T))),
                              int64(ord(low(T))))
  elif T is object:
    # For variant objects, Nim's `fields(w)` iterates the
    # discriminator plus only the *active arm's* fields — inactive
    # arms are skipped. Result: positional order is [discriminator,
    # active-arm field 1, active-arm field 2, …], which matches
    # Phase 11 cycle 8's contract.
    for f in fields(w):
      renderInto(f, res, cells)
  else:
    {.error: "renderAsChoices: unsupported witness shape".}

proc renderAsChoices*[T](w: T): seq[ChoiceNode] =
  var cells: seq[pointer]
  renderInto(w, result, cells)

# ---- assertCoveredBy capture context ----------------------------------------
#
# RFC-z3-optional S1c: `SymexCaptureCtx`, the `symexCapture` threadvar and
# `symexCaptureBegin`/`End`/`Record` now live in `engine/markers.nim`,
# alongside the `symexTarget`/`symexAssert`/`symexAssume` markers they
# serve. All of it is Z3-free, and putting it behind the walker's import
# meant a marker-annotated SUT could not compile under bare `import nelli`
# once the umbrella stopped re-exporting symex. Re-exported by name below,
# so `import nelli/symex` callers are unchanged.

import ./engine/markers as symexMarkers
export symexMarkers.SymexCaptureCtx,
       symexMarkers.symexCapture,
       symexMarkers.symexCaptureBegin,
       symexMarkers.symexCaptureEnd,
       symexMarkers.symexCaptureRecord,
       symexMarkers.symexTarget,
       symexMarkers.symexAssert,
       symexMarkers.symexAssume

# ---- SymexFinding sink (relocated to engine/types in Phase 12 cycle 1) ------
#
# The threadvar + recordSymexFinding + consumeSymexFindings live in
# `engine/types.nim` so phase modules can record findings without a
# circular import into the full symex+z3 stack. They're re-exported
# below for callers that imported them from `nelli/symex`.
export engineTypes.symexFindings,
       engineTypes.recordSymexFinding,
       engineTypes.consumeSymexFindings

proc describeTarget*(t: SymexTarget): string =
  case t.kind
  of stkLabel:              "label(\"" & t.label & "\")"
  of stkAssertionViolation: "assertion-violation"
  of stkIndexError:         "index-error"
  of stkFieldDefect:        "field-defect"
  of stkRaisedExn:                                       ## Phase 15 E2a
    if t.typeFilter.len == 0: "raised-exn(any)"
    else:                     "raised-exn(" & t.typeFilter & ")"
  of stkNilAccess:          "nil-access"                 ## Phase 15 R5

# ---- Content-addressed DB persistence ---------------------------------------
#
# Symex witnesses persist under a content-addressed key derived from
# (canonical SUT IR, target, witness-relevant settings, Z3 version,
# Nim version, walker version). Identical inputs → identical key;
# any change to *anything that affects the witness* rotates the key
# so stale entries become invisible. See docs/symex/determinism.md
# and nelli/smt/canonicalize.nim for the canonical-encoding
# contract and the proof obligations on each input.
import ./db
export db
import ./strategy
import ./engine
import ./engine/phases
import ./engine/pipeline
import ./optbox
import ./smt/canonicalize
export canonicalize.symexCacheKey, canonicalize.symexWalkerVersion,
       canonicalize.renderAsChoicesVersion, canonicalize.canonicalize,
       canonicalize.cacheKeySat, canonicalize.cacheKeyUnsat,
       canonicalize.cacheKeyUnknown, canonicalize.cacheKeyRaised,
       canonicalize.verdictCacheMaxEntries

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
const soundnessMetaVersion = "1"
  ## The encoding's own version: `"1:<pathTaint>:<runTaint>:<replay>"`, each
  ## taint a bitmask over `SoundnessChannel` ordinals and `replay` the
  ## `ReplayStatus` ordinal. Anything else decodes as a miss.

type
  CachedWitness* = tuple[choices: seq[ChoiceNode], soundness: Soundness]
    ## RFC-0005 S11. One `:sat` cache entry: the witness's choice sequence
    ## and the soundness of the verdict that produced it.
  CachedVerdict* = tuple[status: SymexFindingStatus, soundness: Soundness]
    ## RFC-0005 S11. A `:unsat` / `:unk` cache hit: the status and the
    ## soundness it was persisted with.

func taintBits(t: Taint): int =
  for c in t: result = result or (1 shl ord(c))

proc encodeSoundness(s: Soundness): string =
  soundnessMetaVersion & ":" & $taintBits(s.pathTaint) & ":" &
    $taintBits(s.runTaint) & ":" & $ord(s.replay)

proc decodeSoundness(v: string): Option[Soundness] =
  ## The inverse of `encodeSoundness`; `none` for anything it did not write.
  let parts = v.split(':')
  if parts.len != 4 or parts[0] != soundnessMetaVersion: return none(Soundness)
  var nums: array[3, int]
  for i in 1 .. 3:
    if parts[i].len != 1 or parts[i][0] notin {'0' .. '9'}:
      return none(Soundness)
    nums[i - 1] = ord(parts[i][0]) - ord('0')
  const allBits = (1 shl (ord(high(SoundnessChannel)) + 1)) - 1
  if nums[0] > allBits or nums[1] > allBits or
     nums[2] > ord(high(ReplayStatus)):
    return none(Soundness)
  var s = Soundness(replay: ReplayStatus(nums[2]))
  for c in SoundnessChannel:
    if (nums[0] and (1 shl ord(c))) != 0: s.pathTaint.incl c
    if (nums[1] and (1 shl ord(c))) != 0: s.runTaint.incl c
  some(s)

proc soundnessMeta(s: Soundness): Table[string, string] =
  result = initTable[string, string]()
  result[soundnessMetaKey] = encodeSoundness(s)

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

proc findingGaps(errors: seq[SymexErrorInfo]): seq[FindingGap] =
  ## RFC-0005 S11. `gapsOf` projected onto the Z3-free `FindingGap`.
  for g in gapsOf(errors):
    result.add FindingGap(class: g.class, kind: $g.e.kind, msg: g.e.msg)

proc saveSymexWitnessImpl*(db: ExampleDatabase, prog: SymexProgram,
                           target: SymexTarget, settings: SymexSettings,
                           finding: SymexFinding,
                           errors: var seq[string],
                           maxEntries = 64) =
  ## Runtime body of `saveSymexWitness`. Skips non-Sat findings (no
  ## witness to persist), otherwise saves the choice array under the
  ## content-addressed key with `:sat` suffix, with `finding.soundness` in
  ## the entry's metadata (RFC-0005 S11).
  ##
  ## DB save errors are appended to `errors` and the call returns
  ## normally — symmetric with `saveSymexVerdictImpl`. Closes a
  ## pre-existing inconsistency where `db.nim`'s module promise
  ## ("errors flow to Report.dbErrors") was violated here by
  ## propagating exceptions. Callers route `errors` into
  ## `Report.dbErrors`.
  if finding.status != sfSat: return
  if not metaReady(db, "saveSymexWitnessImpl", errors): return
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & cacheKeySat
  try:
    db.save(key, finding.witnessChoices, soundnessMeta(finding.soundness),
            maxEntries)
  except CatchableError as e:
    errors.add "saveSymexWitnessImpl: " & $e.name & ": " & e.msg

proc loadSymexWitnessesImpl*(db: ExampleDatabase, prog: SymexProgram,
                             target: SymexTarget,
                             settings: SymexSettings,
                             errors: var seq[string]
                            ): seq[CachedWitness] =
  ## Runtime body of `loadSymexWitnesses`. Returns the persisted
  ## witnesses for *exactly* this SUT/target/settings/Z3/Nim/walker
  ## combination, each with its stored `Soundness` (RFC-0005 S11).
  ## Mismatched key → empty seq. An entry without soundness metadata is
  ## skipped (a miss, with a note in `errors`).
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
      if s.isSome:
        result.add (choices: e.choices, soundness: s.get)
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
                            errors: var seq[string]) =
  ## Phase 13 cycle 3. Persist a non-SAT verdict (sfUnsat /
  ## sfUnknown) under the content-addressed key with the
  ## appropriate suffix. The stored value is the sentinel empty
  ## `seq[ChoiceNode]`; `verdictCacheMaxEntries = 1` keeps the
  ## slot to a single entry so the positional load invariant
  ## `result[0] == @[]` cannot break. RFC-0005 S11: the sentinel
  ## carries `soundness` in its metadata, and a load serves it back.
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
    of sfSat, sfNotApplicable, sfReplayMiss: return
      # `sfReplayMiss` (Phase 14 B5) is a per-replay diagnostic;
      # it's not a verdict and has no cache representation.
    of sfRaised: return
      # Phase 15 E2a. An `sfRaised` finding carries a per-type id and is
      # persisted by `saveSymexRaisedImpl` (multi-finding protocol), not by
      # this single-sentinel verdict path. No-op here.
  if not metaReady(db, "saveSymexVerdictImpl", errors): return
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & suffix
  try:
    db.save(key, @[], soundnessMeta(soundness), verdictCacheMaxEntries)
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
  ## `Soundness` on hit (RFC-0005 S11); `none` on full miss. A
  ## sentinel without soundness metadata is a miss. Never exposes the raw `seq[seq[ChoiceNode]]`
  ## to callers — the sentinel must not leak into any code path
  ## that might pass it to `db.removeMany`.
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
        if s.isSome:
          return some((status: verdict, soundness: s.get))
        errors.add "loadSymexVerdictImpl: a sentinel without soundness " &
          "metadata (pre-RFC-0005-S11 format) is treated as a miss"
    except CatchableError as e:
      errors.add "loadSymexVerdictImpl: " & $e.name & ": " & e.msg
  tryLoad(cacheKeyUnsat, sfUnsat)
  tryLoad(cacheKeyUnknown,   sfUnknown)
  none(CachedVerdict)

const cacheKeyRaisedIndex = ":raised"
  ## Phase 15 E2a. Index slot for the multi-`sxRaised` cache protocol. The
  ## per-type sentinels live under `cacheKeyRaised(typeId)` (e.g.
  ## `:raised:ValueError`); the index here enumerates which type ids were
  ## persisted (the general example-DB has no key-prefix scan, so the set of
  ## raised types must be recorded explicitly to be reloadable).

proc saveSymexRaisedImpl*(db: ExampleDatabase, prog: SymexProgram,
                          target: SymexTarget, settings: SymexSettings,
                          found: seq[RawResult],
                          errors: var seq[string]) =
  ## Phase 15 E2a. Persist every `sxRaised` finding in `found` under the
  ## content-addressed key. STRUCTURAL multi-finding protocol: each distinct
  ## raised type id is written
  ##   (a) as a per-type sentinel under `cacheKeyRaised(typeId)` (RFC: one DB
  ##       slot per `(exnType)` finding), and
  ##   (b) as an index entry under `cacheKeyRaisedIndex` so `loadSymexRaisedImpl`
  ##       can enumerate the persisted type ids without a DB key-prefix scan.
  ## A SUT with two distinct raise paths (e.g. ValueError, IOError) round-trips
  ## both findings through save/load. No witness is stored in E2a (the structural
  ## walker emits no witness); E2b populates witnesses.
  ##
  ## DB save errors are appended to `errors` and the call returns normally — the
  ## cache is best-effort (symmetric with `saveSymexVerdictImpl`).
  if not metaReady(db, "saveSymexRaisedImpl", errors): return
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  # Distinct type ids in first-seen order (duplicate raise paths of the same
  # type collapse to a single DB slot — the per-type key is the unit of record).
  var typeIds: seq[string] = @[]
  var sounds: seq[Soundness] = @[]   ## RFC-0005 S11: the first finding's, per type
  for raw in found:
    if raw.status != sxRaised: continue
    if raw.raisedTypeId notin typeIds:
      typeIds.add raw.raisedTypeId
      sounds.add raw.soundness
  if typeIds.len == 0: return
  try:
    for i, tid in typeIds:
      # (a) per-type sentinel slot, carrying the finding's soundness.
      db.save(baseKey & cacheKeyRaised(tid), @[], soundnessMeta(sounds[i]),
              verdictCacheMaxEntries)
      # (b) index entry: the type id encoded as its raw bytes.
      db.save(baseKey & cacheKeyRaisedIndex,
              @[bytesChoice(cast[seq[byte]](tid), 0, tid.len)],
              typeIds.len)
  except CatchableError as e:
    errors.add "saveSymexRaisedImpl: " & $e.name & ": " & e.msg

proc loadSymexRaisedImpl*(db: ExampleDatabase, prog: SymexProgram,
                          target: SymexTarget, settings: SymexSettings,
                          errors: var seq[string]): seq[RawResult] =
  ## Phase 15 E2a. Reconstruct the full `seq[RawResult]` of `sxRaised` findings
  ## from the DB without re-invoking Z3. Reads the index slot
  ## (`cacheKeyRaisedIndex`) to enumerate the persisted type ids and rebuilds one
  ## `RawResult{status: sxRaised, raisedTypeId, soundness}` per entry. The
  ## index is the enumeration source; RFC-0005 S11: the per-type sentinel
  ## (`cacheKeyRaised(typeId)`) carries the finding's `Soundness`, and a type
  ## whose sentinel is missing or has no soundness metadata is a miss.
  ## Returns `@[]` on a full miss.
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
    for entry in entries:
      if entry.len == 1 and entry[0].kind == ckBytes:
        let tid = cast[string](entry[0].bytesVal)
        let sentinel = db.loadPrimaryWithMeta(baseKey & cacheKeyRaised(tid))
        let s =
          if sentinel.len == 1 and sentinel[0].choices.len == 0:
            storedSoundness(sentinel[0].meta)
          else: none(Soundness)
        if s.isSome:
          result.add RawResult(status: sxRaised, raisedTypeId: tid,
                               soundness: s.get)
        else:
          errors.add "loadSymexRaisedImpl: raised(" & tid & ") has no " &
            "soundness-carrying sentinel (pre-RFC-0005-S11 format); a miss"
  except CatchableError as e:
    errors.add "loadSymexRaisedImpl: " & $e.name & ": " & e.msg
    result = @[]

proc toFindingStatus*(s: SymexStatusKind): SymexFindingStatus =
  case s
  of sxSat:     sfSat
  of sxUnsat:   sfUnsat
  of sxUnknown: sfUnknown
  of sxRaised:  sfRaised   ## Phase 15 E2a

# ---- Layer 2 — forAllWithSymexSeeds ----------------------------------------
#
# The engine entry that lifts symex witnesses into the random-PBT
# loop as forced seeds. `symexSeedPhase` is slotted between
# `explicit` (user-pinned regression seeds, no shrinking) and
# `random` (fresh exploration). Seeds that falsify carry their
# choice sequence forward to `shrinkPhase` for minimisation —
# Z3 returns *some* satisfying assignment, not a minimal one.

proc forAllWithSymexSeeds*[T](seeds: seq[seq[ChoiceNode]],
                              s: Strategy[T], prop: proc(x: T),
                              settings: Settings = Settings()
                             ): Report[T] =
  ## Run `prop` against `s` with `seeds` as forced replays before
  ## the random phase. Falsifications discovered from a seed flow
  ## through the same `shrinkPhase → finalizePhase` chain a random
  ## falsification would. Returns the terminal `Report[T]`.
  let phases = @[
    Phase[T](name: "dbReuse",   run: dbReusePhase[T]),
    Phase[T](name: "explicit",  run: explicitExamplesPhase[T]),
    symexSeedPhase[T](seeds),
    Phase[T](name: "random",    run: randomPhase[T]),
    Phase[T](name: "targeted",  run: targetedPhase[T]),
    Phase[T](name: "shrink",    run: shrinkPhase[T]),
    Phase[T](name: "explain",   run: explainPhase[T]),
    Phase[T](name: "finalize",  run: finalizePhase[T]),
  ]
  runForAllPipelineWithPhases(
    inMemoryDatabase(), dbEnabled = false,
    s, prop, settings, toExamples[T](@[]), phases)

# ---- Layer 3 — symexForAll sugar -------------------------------------------
#
# One-call entry: `symexForAll(strategy, fn, db)` discovers all
# auto-targets in `fn`, runs symex per target (Layer 1), seeds the
# random-PBT loop with the SAT witnesses (Layer 2), and threads
# the per-target findings into the resulting Report's
# `symexFindings` field for caller-side auditing.
#
# The SUT proc `fn` plays both roles: it is the property the
# engine runs against random + symex-seeded draws, AND the body
# the IR scan inspects for `symexTarget` / `symexAssert` / `arr[i]`
# / variant-field reads.

macro symexForAll*(s: typed, fn: typed,
                   db: ExampleDatabase,
                   symexSettings: static SymexSettings =
                     defaultSymexSettings(),
                   forAllSettings: Settings = Settings(),
                   excludeTargets: seq[SymexTarget] = @[]
                  ): untyped =
  ## Run symex against every auto-discovered target in `fn`, then
  ## drive the random PBT loop on `s` with the symex-derived
  ## witnesses as forced seeds. The terminal Report carries both
  ## the random-run verdict and the per-target symex findings.
  ##
  ## Returns `untyped` matching the `symexFind` macro shape; the
  ## emitted expression has type `Report[T]` where `T` is the
  ## strategy's element type.
  # Inspect `fn`'s formal-param count at macro time to decide
  # whether to pass `fn` directly as the property (single-arg) or
  # wrap it in a tuple-splatting lambda (multi-arg). The strategy
  # `s`'s element type comes from `getTypeInst(s)[1]` — for
  # `Strategy[T]` that's `T` (`int` for `integers()`,
  # `(int, bool)` for `map(integers(), booleans())`).
  # RFC-parser-normalization N1: routes through the shared nil-core's
  # hard-error wrapper. `symexForAll` DELIBERATELY never parses `impl` —
  # it defers entirely to `symexFindAllWitnesses`'s own parse/expansion
  # below. Do not "fix" this into a second `parseEntryImpl` call; that
  # would double-parse the same SUT.
  let impl = resolveEntryImpl(fn, "symexForAll")
  if impl[2].kind != nnkEmpty:
    error("symexForAll: generic procs are not supported as `fn` " &
          "(witness reconstruction has no type to bind generics to)",
          fn)
  let formalParams = impl[3]
  let nParams = formalParams.len - 1   # [0] is the return type
  let prop =
    if nParams <= 1:
      fn      # single-arg: `fn` IS the property
    else:
      # Multi-arg: emit `proc(t: T) = fn(t[0], t[1], …)`. Type
      # comes from `getTypeInst(s)[1]` — the strategy's element
      # type. Nim verifies field-types vs param-types when the
      # emitted call compiles, so a mismatch surfaces as a typed
      # error at the splat site rather than buried inside the
      # macro.
      let sTypeNode = newCall(bindSym"getTypeInst", s)
      # `sTypeNode` evaluates to a NimNode at *macro-time*; we
      # however need a `typedesc` *at call site* so the wrapper's
      # param type is a real type. Use a type alias via `type X =
      # typeof((default(...)))` — no, simpler — extract the
      # element-type expression directly from `s.getTypeInst` at
      # macro time and splice it as a type.
      let sTypeInst = s.getTypeInst
      if sTypeInst.kind != nnkBracketExpr or not sTypeInst[0].eqIdent("Strategy"):
        error("symexForAll: expected `s` to have type Strategy[T] " &
              "(got " & $sTypeInst.repr & ")", s)
      let elemTy = sTypeInst[1]
      # Reject named-field tuples — `map(s1, s2)` produces an
      # anonymous positional tuple (nnkTupleConstr). Named-field
      # tuple strategies are deferred to a future cycle.
      if elemTy.kind == nnkTupleTy:
        error("symexForAll: named-field tuple strategies are not " &
              "supported as `s` for multi-arg `fn`; use the " &
              "anonymous `map(s1, s2, …)` form", s)
      let tId = genSym(nskParam, "t")
      var splat = newCall(fn)
      for i in 0 ..< nParams:
        splat.add nnkBracketExpr.newTree(tId, newLit(i))
      let lam = newProc(
        params = @[ident"void",
                   newIdentDefs(tId, elemTy)],
        body = splat, procType = nnkLambda)
      lam

  result = quote do:
    block:
      let findings = symexFindAllWitnesses(`fn`, `db`, `symexSettings`,
                                            `excludeTargets`)
      var seeds: seq[seq[ChoiceNode]] = @[]
      for f in findings:
        # RFC-0005 S11 (§8.1 "the seed filter"): no `trusted()` test is
        # needed here. Since S10 an sfSat finding is trusted by construction
        # (a tainted candidate becomes sfSat only on `rsConfirmed`), and a
        # seed is only an input -- the property itself judges it.
        if f.status == sfSat:
          seeds.add f.witnessChoices
      var report = forAllWithSymexSeeds(seeds, `s`, `prop`,
                                         `forAllSettings`)
      # Drain the sink — picks up Layer 1's deposits PLUS any
      # sfNotApplicable findings symexSeedPhase deposited for
      # shape-mismatched seeds during Layer 2 — into the Report
      # so the audit trail flows back to the caller without a
      # separate `consumeSymexFindings()` call.
      for f in consumeSymexFindings():
        report.symexFindings.add f
      report


# ---- Macro helpers (at module scope so they can recurse cleanly) ----------

proc primTyAndReader(ty: IRType): (string, string) =
  case ty.kind
  of itBool: ("bool", "readBool")
  of itInt:
    if ty.signed:
      case ty.width
      of 8:  ("int8",  "readInt8")
      of 16: ("int16", "readInt16")
      of 32: ("int32", "readInt32")
      of 64: ("int",   "readInt")
      else: ("int", "readInt")
    elif ty.width == 8 and ty.isChar:
      # RFC-0005 S8am (S8z's remainder, item 3): render a Nim `char` as
      # `char`, not `uint8` -- `isChar` is the only thing that tells a
      # `char` witness apart from a `byte`/`uint8` one (see `IRType.isChar`'s
      # field doc: all three share one structural `itInt` shape).
      ("char", "readChar")
    else:
      case ty.width
      of 8:  ("uint8",  "readUInt8")
      of 16: ("uint16", "readUInt16")
      of 32: ("uint32", "readUInt32")
      of 64: ("uint",   "readUInt")
      else: ("uint", "readUInt")
  of itFloat32: ("float32", "readFloat32")   ## Phase 15 F1
  of itFloat64: ("float",   "readFloat")     ## Phase 15 F1
  else: ("", "")

proc rendersAsDefaultObject(ty: IRType): bool =
  ## The `itTuple` arm of `emitTyAndReader` below renders a nominal object
  ## that LOOKS like a variant (a leading `kind` field + more than two
  ## fields) as `default(Object)` instead of reading its fields -- the
  ## witness value is then NOT the solver's model. Factored out (RFC-0005
  ## S2) so `witnessFidelity` classifies exactly the shapes the reader stubs;
  ## two copies of the heuristic could drift and let a stubbed witness be
  ## replayed as if it were faithful.
  ty.kind == itTuple and ty.objectName.len > 0 and
    ty.fields.len > 2 and ty.fieldNames.len > 0 and ty.fieldNames[0] == "kind"

proc stdName(name: string): NimNode =
  ## RFC-0005 S8e. The symbol of a system/stdlib type, constructor or witness
  ## reader that `emitTyAndReader` writes into the CALLER's scope. An
  ## identifier there resolves in that scope: a caller that did not import
  ## `std/tables` has no `Table`, and a caller that declares its own `seq`
  ## or `readSeqInt` would have the witness built through it. Bound here,
  ## each name means what this module means by it, in any scope.
  case name
  of "bool": bindSym"bool"
  of "int": bindSym"int"
  of "int8": bindSym"int8"
  of "int16": bindSym"int16"
  of "int32": bindSym"int32"
  of "int64": bindSym"int64"
  of "uint": bindSym"uint"
  of "uint8": bindSym"uint8"
  of "char": bindSym"char"               # RFC-0005 S8am
  of "uint16": bindSym"uint16"
  of "uint32": bindSym"uint32"
  of "uint64": bindSym"uint64"
  of "float": bindSym"float"
  of "float32": bindSym"float32"
  of "string": bindSym"string"
  of "array": bindSym"array"
  of "seq": bindSym"seq"
  of "newSeq": bindSym"newSeq"
  of "Table": bindSym"Table"
  of "HashSet": bindSym"HashSet"
  of "readBool": bindSym"readBool"
  of "readInt": bindSym"readInt"
  of "readInt8": bindSym"readInt8"
  of "readInt16": bindSym"readInt16"
  of "readInt32": bindSym"readInt32"
  of "readUInt": bindSym"readUInt"
  of "readUInt8": bindSym"readUInt8"
  of "readChar": bindSym"readChar"       # RFC-0005 S8am
  of "readUInt16": bindSym"readUInt16"
  of "readUInt32": bindSym"readUInt32"
  of "readFloat": bindSym"readFloat"
  of "readFloat32": bindSym"readFloat32"
  of "readString": bindSym"readString"
  of "readSeqInt": bindSym"readSeqInt"
  of "readSeqInt8": bindSym"readSeqInt8"
  of "readSeqInt16": bindSym"readSeqInt16"
  of "readSeqInt32": bindSym"readSeqInt32"
  of "readSeqUInt8": bindSym"readSeqUInt8"
  of "readSeqUInt16": bindSym"readSeqUInt16"
  of "readSeqUInt32": bindSym"readSeqUInt32"
  of "readSeqUInt64": bindSym"readSeqUInt64"
  of "readSeqFloat64": bindSym"readSeqFloat64"
  of "readSeqFloat32": bindSym"readSeqFloat32"
  of "readTableStrInt": bindSym"readTableStrInt"
  of "readSetInt": bindSym"readSetInt"
  of "readTableStrIntAs": bindSym"readTableStrIntAs"   # RFC-0005 S8z
  of "readSetIntAs": bindSym"readSetIntAs"             # RFC-0005 S8z
  of "readSeqLen": bindSym"readSeqLen"
  of "newRefWitness": bindSym"newRefWitness"      # RFC-0005 S8h
  of "resolveRef": bindSym"resolveRef"            # RFC-0005 S8h
  of "refElemPos": bindSym"refElemPos"            # RFC-0005 S8h
  else:
    error("symex RFC-0005 S8e: stdName has no binding for `" & name & "`")
    nil

proc userTypeName(ty: IRType, spelling: string): NimNode =
  ## RFC-0005 S8e. A named user type in the witness: its own SYMBOL, as
  ## `dsl_typebridge.keyedBySym` recorded it at classification. The spelling
  ## stands in only where no symbol was recorded (a type that reached the IR
  ## from something other than a symbol), which is all the emitter wrote
  ## before.
  let sym = witnessTypeSym(ty)
  if sym == nil: ident(spelling)
  elif sym.kind == nnkSym: copyNimNode(sym)
  else: copyNimTree(sym)   ## RFC-0005 S8bn: a generic instance `G[int]`

proc defaultValueOf(tyNode: NimNode): NimNode =
  ## RFC-0005 S8e. The default value of the type `tyNode` names, as
  ## `block: (var w: T; w)`. `default(T)` needs `T` as a `typedesc`, and a
  ## type SYMBOL recorded from the typed AST (`userTypeName`) carries the
  ## type itself as its node type, which `default`'s overload rejects; a
  ## declaration's type position takes the symbol as it is.
  let w = genSym(nskVar, "dflt")
  quote do:
    block:
      var `w`: `tyNode`
      `w`

proc emitTyAndReader*(ty: IRType, path: string, witId: NimNode): (NimNode, NimNode)

proc emitTyAndReaderShared(ty: IRType, path: string,
                           witId: NimNode): (NimNode, NimNode)

var witnessRefCtx {.compileTime.}: NimNode
  ## RFC-0005 S8h. The `RefWitness` binding of the witness tuple being
  ## emitted (`emitWitnessTuple`): every `ref`/`ptr` position of one witness
  ## resolves through ONE context, so a cell shared by two positions is one
  ## Nim object bound to both.
var witnessRefCtxUsed {.compileTime.}: bool
  ## RFC-0005 S8h. Whether the tuple being emitted resolved any ref.

proc refWitnessCtx(witId: NimNode): NimNode =
  ## RFC-0005 S8h. The context a `ref` position resolves through: the
  ## enclosing `emitWitnessTuple`'s, or -- for a reader emitted outside one --
  ## a context of its own (identity is then shared within the position only).
  witnessRefCtxUsed = true
  if witnessRefCtx != nil: witnessRefCtx
  else: newCall(stdName("newRefWitness"), witId)

proc resolveRefCall(refTy: NimNode; pos, witId: NimNode): NimNode =
  ## RFC-0005 S8h. `resolveRef[refTy](ctx, pos)`.
  newCall(nnkBracketExpr.newTree(stdName("resolveRef"), refTy),
          refWitnessCtx(witId), pos)

proc emitRefElemsReader(elemTy: NimNode; path: string; witId, n,
                        init: NimNode): NimNode =
  ## RFC-0005 S8h. The reader of a `seq`/`array` of refs: `init` is the
  ## container, `n` its element count; element `i` is the position `path[i]`.
  let contId = genSym(nskVar, "cont")
  let iId = genSym(nskForVar, "i")
  let nId = genSym(nskLet, "n")
  let pos = newCall(stdName("refElemPos"), newLit(path), iId)
  let elem = resolveRefCall(elemTy, pos, witId)
  quote do:
    block:
      let `nId` = `n`
      var `contId` = `init`
      for `iId` in 0 ..< `nId`:
        `contId`[`iId`] = `elem`
      `contId`

proc refPointeeOf(ty: IRType): IRType =
  if ty.kind == itRef: ty.refPointeeTy else: ty.ptrPointeeTy

proc resolvesByRef(ty: IRType): bool =
  ## RFC-0005 S8h. Whether the `ref`/`ptr` position `ty` renders through
  ## `resolveRef`: always, for a `ref`, unless it is a recursive field whose
  ## type reached the IR without a symbol; for a `ptr`, when its pointee is
  ## an object or a scalar `alloc0` can hold.
  let pointee = refPointeeOf(ty)
  if isRecursionPlaceholder(pointee) and witnessTypeSym(pointee) == nil:
    return false
  # RFC-0005 S8bn: a `ptr string` too (S8bh retargets one like a scalar);
  # `alloc0` holds an empty string.
  ty.kind == itRef or
    pointee.kind in {itTuple, itVariant, itMultiVariant, itInt, itBool,
                     itFloat32, itFloat64, itString}

proc refWitnessTypeNode(ty: IRType; path: string; witId: NimNode): NimNode =
  ## RFC-0005 S8h. The Nim type of the `ref`/`ptr` position `ty`. A named ref
  ## alias (`type Node = ref object`) IS the ref type; a recursive field's IR
  ## pointee is an empty placeholder carrying only the symbol it was
  ## classified from -- the alias itself, or the object an inline `ref Obj`
  ## points to.
  let pointee = refPointeeOf(ty)
  proc wrapped(inner: NimNode): NimNode =
    if ty.kind == itRef: nnkRefTy.newTree(inner) else: nnkPtrTy.newTree(inner)
  if isRecursionPlaceholder(pointee):
    let sym = witnessTypeSym(pointee)
    if sym == nil: return wrapped(ident(pointee.objectName))
    if sym.kind == nnkBracketExpr:
      # RFC-0005 S8bn: a generic instance; its head's declaration tells.
      let gi = sym[0].getImpl
      if gi.kind == nnkTypeDef and gi.len >= 3 and
         gi[2].kind in {nnkRefTy, nnkPtrTy}:
        return copyNimTree(sym)
      return wrapped(copyNimTree(sym))
    let impl = sym.getImpl
    if impl.kind == nnkTypeDef and impl.len >= 3 and
       impl[2].kind in {nnkRefTy, nnkPtrTy}:
      return copyNimNode(sym)
    return wrapped(copyNimNode(sym))
  # RFC-0005 S8l: a variant pointee of a named `ref object` case type
  # (`type VB = ref object case ...`) is spelled by that ref type itself --
  # as `nameIsRefAlias` says for a plain one. Its symbol's own declaration
  # tells (a `ref VObj` alias's pointee symbol is the value object `VObj`).
  if pointee.kind in {itVariant, itMultiVariant}:
    let sym = witnessTypeSym(pointee)
    if sym != nil:
      let impl = sym.getImpl
      if impl.kind == nnkTypeDef and impl.len >= 3 and
         impl[2].kind in {nnkRefTy, nnkPtrTy}:
        return copyNimNode(sym)
  let (innerTy, _) = emitTyAndReader(pointee, path, witId)
  if pointee.kind == itTuple and pointee.nameIsRefAlias: innerTy
  else: wrapped(innerTy)

proc emitTyAndReaderShared(ty: IRType, path: string,
                           witId: NimNode): (NimNode, NimNode) =
  ## Recursive: returns (Nim type AST, witness-construction expression). The
  ## result may use one node at several places; `emitTyAndReader` unshares.
  case ty.kind
  of itUninterp:
    if ty.uninterpName == "__closure":
      # Phase 15 Cluster C (C2a, Invariant 3). A closure as a top-level SUT
      # param/result type is unsupported: a proc value cannot be reconstructed
      # as a concrete witness. Emit a `proc` placeholder + a compile-time
      # `{.warning.}` (classified, not a silent crash). Closures are constructed
      # IN-BODY (C2a) but never reach the witness reader as a top-level type.
      let placeholder = quote do:
        block:
          {.warning: "symex: a closure as a top-level SUT param/result type " &
                     "is unsupported; witness rendering yields a nil proc " &
                     "placeholder (Phase 15 Cluster C / Invariant 3).".}
          (proc (): void = discard)
      return (nnkProcTy.newTree(nnkFormalParams.newTree(newEmptyNode()),
                                newEmptyNode()), placeholder)
    if ty.uninterpName.startsWith("__unsupported:") or
       ty.uninterpName.startsWith("__unsupported_witness:"):
      # RFC-chapulin-hardening CR-2b/CR-2c (Cluster 2 — Crash-totality,
      # round-2 Option 2 / Option A). Two distinct catch-alls feed this ONE
      # placeholder arm:
      #   `__unsupported:` (CR-2b)         — classifyType's param-type text-
      #                                       match catch-all.
      #   `__unsupported_witness:` (CR-2c) — `parseProc*`'s SUT parameter-
      #                                       classification loop
      #                                       (`dsl_parser.nim`), via
      #                                       `demoteUnrenderableWitnessTy`,
      #                                       when a parameter's witness
      #                                       type-tree contains — at ANY
      #                                       depth (nested in a tuple /
      #                                       object / array / variant /
      #                                       distinct / ref pointee) — a
      #                                       seq/Table/HashSet shape outside
      #                                       emitTyAndReader's renderable
      #                                       fragment. The RECURSIVE
      #                                       `isRenderableWitnessTy`
      #                                       predicate (`smt/types.nim`,
      #                                       reusing the
      #                                       `isRenderableSeqElemTy`/
      #                                       `isRenderableTableTy`/
      #                                       `isRenderableSetElemTy` leaf
      #                                       checks) decides this —
      #                                       i.e. this is CR-2c's fix for
      #                                       the `itSeq`/`itTable`/`itSet`
      #                                       `error()` sites below: the
      #                                       unrenderable shapes never
      #                                       reach them because
      #                                       `parseProc*` already routed
      #                                       them here instead. (Applied at
      #                                       the top-level parameter, NOT
      #                                       inside `classifyType` itself —
      #                                       that classifier is also used
      #                                       for purely-internal,
      #                                       non-witness types.)
      # In both cases `allocateSym` raises the classified
      # `SymexClassifiedDegradeError` (with `feUnsupportedParamType` or
      # `feUnsupportedWitnessType` respectively) at PARAMETER-ALLOCATION
      # time, before the walker ever solves for a witness — so the
      # `sxSat`/`sxRaised` codegen arms that would read this witness
      # expression are UNREACHABLE for this param (the run always resolves
      # `sxUnknown`). This placeholder therefore only needs to TYPECHECK,
      # never to be evaluated. Emit an `int` placeholder + a compile-time
      # `{.warning.}`, mirroring the `__closure` precedent above.
      let placeholder = quote do:
        block:
          {.warning: "symex: an unsupported parameter/witness type degrades " &
                     "the whole run to sxUnknown (RFC-chapulin-hardening " &
                     "CR-2b/CR-2c / Invariant 3); witness rendering yields " &
                     "an unused int placeholder.".}
          0
      return (stdName("int"), placeholder)
    raise newException(ValueError,
      "emitTyAndReader(itUninterp): opaque-ref witness reader lands with cluster E")
  of itDistinct:
    # Phase 15 G4 (Breadth-CRIT-1). A `distinct T` param renders through the
    # eject-then-base-reader chain: extract the BASE value at the SAME path
    # (the runtime's `extractFromSymVal(svDistinct)` populated it from
    # `eject_T(distinctConst)`), then wrap it in the distinct type's
    # converter `DistinctName(baseValue)`. Without this the distinct param
    # would produce a silent empty reader.
    let (_, baseReader) = emitTyAndReader(ty.distinctBase, path, witId)
    (userTypeName(ty, ty.distinctName),
     newCall(userTypeName(ty, ty.distinctName), baseReader))
  of itBool, itInt, itFloat32, itFloat64:
    let (tyName, readerName) = primTyAndReader(ty)
    let rawReader = newCall(stdName(readerName), witId, newLit(path))
    if ty.kind == itInt and ty.enumName.len > 0:
      # Issue #163 (rev item 1). `ty` is the lifted `itInt` representation of
      # a Nim `enum` (see `IRType.enumName`'s field doc) — the RAW
      # `readUInt8`/`readUInt16`/... reader above produces a plain unsigned
      # value Nim will NOT implicitly convert back into an enum-typed slot,
      # so a bare `nnkObjConstr` field (or, via the `itArray`/itSeq` arms
      # below, an array/seq element) built from it fails to COMPILE. Wrap it
      # in the enum type's own converter call — `EnumName(rawReader)` — the
      # same `T(ordinalValue)` construction Nim itself accepts for any
      # ordinal-convertible value, sound regardless of signedness or a
      # negative/sparse ordinal domain (R2/R18's fixes already put the
      # correct width/signed/range on `ty` before this ever runs).
      (userTypeName(ty, ty.enumName),
       newCall(userTypeName(ty, ty.enumName), rawReader))
    else:
      (stdName(tyName), rawReader)
  of itTuple:
    if ty.objectName.len > 0:
      # Nominal object. For variant objects (heuristic: any of the
      # later fields would conflict with earlier branches), Nim's
      # constructor rejects per-field initialisation. Phase 5+ ships
      # a stub that returns `default(Object)` for variant cases —
      # downstream user code can examine `r.status` to verify
      # reachability. Variant-aware witness reconstruction is a
      # follow-up (#141 phase 2).
      let objTyId = userTypeName(ty, ty.objectName)
      # Check for variant: the discriminator name on the parsed
      # object is conventionally "kind" + fields after position 0
      # that would be ambiguous to construct all at once.
      # (RFC-0005 S2: the predicate is shared with `witnessFidelity`,
      # which must classify exactly the shapes this reader stubs.)
      if rendersAsDefaultObject(ty):
        (objTyId, defaultValueOf(objTyId))
      else:
        var objVal = newTree(nnkObjConstr, objTyId)
        for i, fty in ty.fields:
          let suffix = "." & ty.fieldNames[i]
          let (_, sv) = emitTyAndReader(fty, path & suffix, witId)
          objVal.add newTree(nnkExprColonExpr,
            ident(ty.fieldNames[i]), sv)
        (objTyId, objVal)
    else:
      # Anonymous: nnkTupleConstr (positional) or nnkTupleTy (named).
      let named = ty.fieldNames.len > 0 and ty.fieldNames[0].len > 0
      var subTy = if named: newTree(nnkTupleTy) else: newTree(nnkTupleConstr)
      var subVal = newTree(nnkTupleConstr)
      for i, fty in ty.fields:
        let suffix = if ty.fieldNames[i].len > 0: "." & ty.fieldNames[i]
                     else: "." & $i
        let (st, sv) = emitTyAndReader(fty, path & suffix, witId)
        if named:
          subTy.add newTree(nnkIdentDefs,
            ident(ty.fieldNames[i]), st, newEmptyNode())
          subVal.add newTree(nnkExprColonExpr,
            ident(ty.fieldNames[i]), sv)
        else:
          subTy.add st
          subVal.add sv
      (subTy, subVal)
  of itArray:
    let (elemTyNode, _) = emitTyAndReader(ty.elemTy, path & ".0", witId)
    # RFC-0005 S8am (S8z's remainder, item 5): a non-zero-based array
    # (`array[1..3, int]`, `ty.lo == 1`) renders its DECLARED index range
    # (`array[1..3, int]`), not Nim's `array[N, T]` sugar -- that sugar
    # always means `array[0..N-1, T]`, so a witness built from it alone was
    # typed `array[0..2, int]` for a `array[1..3, int]` parameter: same
    # length, same positional values (replay stays exact), but not the
    # parameter's own type (a caller could not assign it back to a slot
    # declared with the real type without a conversion). The element
    # LITERAL stays purely positional either way (`arrLit`, below) -- Nim's
    # `[v0, v1, v2]` bracket literal needs no index annotations regardless
    # of the target array's index origin.
    let arrIdxNode =
      if ty.lo == 0: newLit(ty.size)
      else: infix(newLit(ty.lo), "..", newLit(ty.lo + int64(ty.size) - 1))
    let arrTy = newTree(nnkBracketExpr,
      stdName("array"), arrIdxNode, elemTyNode)
    if ty.elemTy.kind in {itRef, itPtr} and resolvesByRef(ty.elemTy):
      # RFC-0005 S8f/S8h: element `i` is the position `path[i]`.
      return (arrTy, emitRefElemsReader(elemTyNode, path, witId,
                                        newLit(ty.size),
                                        defaultValueOf(arrTy)))
    var arrLit = newTree(nnkBracket)
    for i in 0 ..< ty.size:
      let (_, sv) = emitTyAndReader(ty.elemTy, path & "." & $i, witId)
      arrLit.add sv
    (arrTy, arrLit)
  of itString:
    (stdName("string"), newCall(stdName("readString"), witId, newLit(path)))
  of itSeq:
    if isUnsupportedFieldPlaceholder(ty):
      # Round-6 Bug #2 (scoped decline, ADR/RFC fork-resolution
      # 2026-08-15): a declared field whose element kind is unbacked (e.g.
      # `seq[(string,string)]`) — `runtime.nim`'s `allocateSym` never
      # populated real witness content for it (`seqLen` was forced `== 0`,
      # `seqDataRaw` is inert), so render a type-correct EMPTY `seq[T]`
      # literal instead of a real reader call — content is never modeled
      # or trusted for this field regardless (any SUT read was already
      # intercepted at parse time, forcing `sxUnknown` before this witness
      # would ever be examined). Recurses ONLY for the element TYPE (the
      # discarded `_` value half never gets emitted, so it is safe even
      # though it would reference witness data that was never written —
      # mirrors the `itArray`/`itRef` arms' existing "type-only" recursion
      # idiom above).
      let (elemTyNode, _) = emitTyAndReader(ty.seqElemTy, path & ".0", witId)
      let seqTy = newTree(nnkBracketExpr, stdName("seq"), elemTyNode)
      (seqTy, newCall(newTree(nnkBracketExpr, stdName("newSeq"), elemTyNode), newLit(0)))
    elif ty.seqElemTy.kind == itDistinct:
      # RFC-0005 S8bd. A `seq[D]`, `D` a chain of `distinct` over an int or
      # float (`isRenderableSeqElemTy`): the cells hold the base
      # (`seqCellTy`, S8ba), so they are read as the base seq, and each
      # element is converted back through the chain, innermost first
      # (`Km(Meters(int(x)))`). Every conversion keeps the value.
      let cell = seqCellTy(ty.seqElemTy)
      let (elemTyNode, _) = emitTyAndReader(ty.seqElemTy, path & ".0", witId)
      let (_, baseReader) = emitTyAndReader(tSeq(cell), path, witId)
      let (cellTyNode, _) = emitTyAndReader(cell, path & ".0", witId)
      let raw = genSym(nskLet, "rawSeq")
      let res = genSym(nskVar, "distinctSeq")
      let k = genSym(nskForVar, "k")
      proc conv(t: IRType; x: NimNode): NimNode =
        if t.kind == itDistinct:
          newCall(userTypeName(t, t.distinctName), conv(t.distinctBase, x))
        else:
          newCall(cellTyNode, x)
      let elemConv = conv(ty.seqElemTy, newTree(nnkBracketExpr, raw, k))
      # System's `len` and `..<`, bound here (RFC-0005 S8e: the caller's
      # scope may shadow either).
      let lenCall = newCall(bindSym"len", raw)
      let upTo = bindSym"..<"
      let newSeqCall = newCall(newTree(nnkBracketExpr, stdName("newSeq"),
                                       elemTyNode), copyNimTree(lenCall))
      let reader = quote do:
        block:
          let `raw` = `baseReader`
          var `res` = `newSeqCall`
          for `k` in `upTo`(0, `lenCall`):
            `res`[`k`] = `elemConv`
          `res`
      (newTree(nnkBracketExpr, stdName("seq"), elemTyNode), reader)
    # Phase 5 cycle 1: only seq[int] tested; specialised reader.
    elif ty.seqElemTy.kind == itInt and ty.seqElemTy.signed and
       ty.seqElemTy.width == 64:
      (newTree(nnkBracketExpr, stdName("seq"), stdName("int")),
       newCall(stdName("readSeqInt"), witId, newLit(path)))
    elif ty.seqElemTy.kind == itInt:
      # RFC-chapulin-hardening M1: fixed-width-int seq elements
      # (`byte`/`uint8..uint64`, `int8..int32` — `int64` is the arm above).
      # `extractSeqElements`/`allocateSeqDataRaw`/`seqElemAt` (runtime.nim)
      # already dispatch on `(signed, width)` for every one of these widths
      # (Phase 15 C4/seqElemAt plumbing); only the POST-SOLVE reader side was
      # missing a case, hard-`error()`ing at macro-expansion (CR-2c's
      # catch-all below). `isRenderableSeqElemTy` (`smt/types.nim`) is widened
      # in lockstep so CR-2c's `demoteUnrenderableWitnessTy` no longer demotes
      # these shapes to a placeholder before this arm is ever reached.
      let sTy = ty.seqElemTy
      let (elemTyName, readerName) =
        if sTy.signed:
          case sTy.width
          of 8:  ("int8",  "readSeqInt8")
          of 16: ("int16", "readSeqInt16")
          of 32: ("int32", "readSeqInt32")
          else:  ("int64", "readSeqInt")   ## unreachable: signed+64 handled above
        else:
          case sTy.width
          of 8:  ("uint8",  "readSeqUInt8")
          of 16: ("uint16", "readSeqUInt16")
          of 32: ("uint32", "readSeqUInt32")
          else:  ("uint64", "readSeqUInt64")
      (newTree(nnkBracketExpr, stdName("seq"), stdName(elemTyName)),
       newCall(stdName(readerName), witId, newLit(path)))
    elif ty.seqElemTy.kind == itFloat64:   ## Phase 15 F9b
      (newTree(nnkBracketExpr, stdName("seq"), stdName("float")),
       newCall(stdName("readSeqFloat64"), witId, newLit(path)))
    elif ty.seqElemTy.kind == itFloat32:   ## Phase 15 F9b
      (newTree(nnkBracketExpr, stdName("seq"), stdName("float32")),
       newCall(stdName("readSeqFloat32"), witId, newLit(path)))
    elif ty.seqElemTy.kind == itRef:   ## Phase 15 R3 (ADR-0010): seq[ref T]
      # RFC-0005 S8f/S8h: element `i` is the position `path[i]` -- nil, the
      # same object as any other position holding its address (an earlier
      # element, a param), or its own cell. (R3 rendered each element a
      # fresh default cell; S8f rebuilt each from its leaves, with identity
      # only among elements.)
      let (elemTy, _) = emitTyAndReader(ty.seqElemTy, path & "[0]", witId)
      let lenCall = newCall(stdName("readSeqLen"), witId, newLit(path))
      let reader = emitRefElemsReader(elemTy, path, witId, lenCall,
        newCall(nnkBracketExpr.newTree(stdName("newSeq"), elemTy), lenCall))
      (newTree(nnkBracketExpr, stdName("seq"), elemTy), reader)
    else:
      # RFC-chapulin-hardening CR-2c (Cluster 2 — Crash-totality). This
      # `else` used to `error()` at macro-expansion time, aborting
      # compilation of the whole test file — a THIRD macro-`error()` site
      # class, distinct from CR-2a/CR-2b. It is now unreachable for ANY SUT
      # PARAMETER witness type, top-level OR nested: `parseProc*`'s
      # parameter-classification loop (`dsl_parser.nim`), via
      # `demoteUnrenderableWitnessTy`, runs each parameter through the
      # RECURSIVE `isRenderableWitnessTy` predicate (`smt/types.nim`), which
      # mirrors EXACTLY this reader's type-tree walk (tuple/object fields,
      # array elems, variant arms, distinct bases, ref pointees) reusing the
      # `isRenderableSeqElemTy` leaf check. Any parameter whose witness tree
      # contains a non-renderable seq element — at any depth — is routed to
      # an `itUninterp("__unsupported_witness:" & s)` placeholder BEFORE this
      # `itSeq` is ever built, so the whole run degrades to a classified
      # `sxUnknown` at parameter-allocation time instead. Retained as a
      # defensive internal-invariant guard (should never fire) in case the
      # predicate and this reader ever drift apart.
      error("symex Phase 5: seq witness reader for " & $ty &
            " not yet implemented")
  of itTable:
    # Phase 5 cycle 5: Table[string, int]. RFC-0005 S8z: and every other
    # renderable value type, read through `readTableStrIntAs[T]`.
    if ty.tabKeyTy.kind == itString and
       ty.tabValTy.kind == itInt and ty.tabValTy.signed and
       ty.tabValTy.width == 64 and ty.tabValTy.enumName.len == 0:
      let tabTy = newTree(nnkBracketExpr,
        stdName("Table"), stdName("string"), stdName("int"))
      (tabTy, newCall(stdName("readTableStrInt"), witId, newLit(path)))
    elif isRenderableTableTy(ty.tabKeyTy, ty.tabValTy):
      let (valTyNode, _) = emitTyAndReader(ty.tabValTy, path, witId)
      let tabTy = newTree(nnkBracketExpr,
        stdName("Table"), stdName("string"), valTyNode)
      (tabTy, newCall(newTree(nnkBracketExpr, stdName("readTableStrIntAs"),
                              copyNimTree(valTyNode)),
                      witId, newLit(path)))
    else:
      # CR-2c: unreachable for any SUT parameter (top-level OR nested) — see
      # the `itSeq` else-arm comment above. `parseProc*`'s recursive
      # `isRenderableWitnessTy` predicate applies `isRenderableTableTy` at
      # every Table leaf and routes any non-`Table[string, int]` parameter
      # shape to the `__unsupported_witness:` placeholder before this
      # `itTable` is built.
      error("symex Phase 5: only Table[string, int] supported (got " &
            $ty & ")")
  of itSet:
    if ty.setElemTy.kind == itInt and ty.setElemTy.signed and
       ty.setElemTy.width == 64 and ty.setElemTy.enumName.len == 0:
      let setTy = newTree(nnkBracketExpr, stdName("HashSet"), stdName("int"))
      (setTy, newCall(stdName("readSetInt"), witId, newLit(path)))
    elif isRenderableSetElemTy(ty.setElemTy):   # RFC-0005 S8z
      let (elemTyNode, _) = emitTyAndReader(ty.setElemTy, path, witId)
      let setTy = newTree(nnkBracketExpr, stdName("HashSet"), elemTyNode)
      (setTy, newCall(newTree(nnkBracketExpr, stdName("readSetIntAs"),
                              copyNimTree(elemTyNode)),
                      witId, newLit(path)))
    else:
      # CR-2c: unreachable for any SUT parameter (top-level OR nested) — see
      # the `itSeq` else-arm comment above. `parseProc*`'s recursive
      # `isRenderableWitnessTy` predicate applies `isRenderableSetElemTy` at
      # every HashSet leaf and routes any non-`HashSet[int]` parameter shape
      # to the `__unsupported_witness:` placeholder before this `itSet` is
      # built.
      error("symex Phase 5: only HashSet[int] supported")
  of itVariant:
    # Phase 11 cycle 7 + plain-field sharing (post-cycle-12) —
    # construct the variant on the arm Z3 picked. Witness layout
    # written by `extractFromSymVal`:
    #   <path>.<discName>            discriminator value
    #   <path>.<plainFieldName>      plain (shared) field values
    #   <path>.@<tagOrdinal>.<field> arm-specific field values
    # Plain fields appear in every arm's constructor at their
    # shared witness path — so the same value is read from the
    # same path in every case branch, which Nim's runtime sees as
    # one shared symbolic value (matching Nim's variant memory
    # layout where plain fields are always-present and shared).
    let objTyId = userTypeName(ty, ty.vObjectName)
    let discPath = path & "." & ty.vDiscName
    let (discTyId, discReaderExpr) =
      emitTyAndReader(ty.vDiscTy, discPath, witId)
    var caseStmt = newTree(nnkCaseStmt, discReaderExpr)
    # Identify the else arm (if any). Phase 14 cycle A2 (ADR-0003 D2):
    # the else arm cannot be rendered as a static-disc nnkObjConstr
    # because its discriminator is dynamic. Render it via
    # `block: var w: V; w.kind = readDisc; w.<plain> = ...; w.<armF> = ...; w`
    # which Nim accepts since each assignment respects the at-that-
    # moment arm shape.
    var elseArm: VariantArm
    var hasElse = false
    for arm in ty.vArms:
      if arm.isElse: elseArm = arm; hasElse = true
    for arm in ty.vArms:
      if arm.isElse: continue
      let tagLit = newCall(discTyId, newLit(arm.tagOrdinal))
      var ctor = newTree(nnkObjConstr, objTyId)
      # Plain fields first (in source order).
      for i, fname in ty.vPlainFieldNames:
        let fty = ty.vPlainFieldTypes[i]
        let plainPath = path & "." & fname
        let (_, fReader) = emitTyAndReader(fty, plainPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      # Discriminator literal. Non-enum discs (Phase 14 A3) carry an
      # empty tagName — Nim accepts an int literal for `range`-typed
      # fields, so fall back to `newLit(tagOrdinal)`. RFC-0005 S8e: an
      # enum member is written `DiscTy(ordinal)` through the disc type's
      # symbol, never by its member name -- the caller's scope need not
      # hold the enum (it imported only the SUT), and may hold another
      # symbol of that spelling.
      let discValExpr =
        if arm.tagName.len > 0: newCall(discTyId, newLit(arm.tagOrdinal))
        else: newLit(arm.tagOrdinal)
      ctor.add nnkExprColonExpr.newTree(
        ident(ty.vDiscName), discValExpr)
      # Arm-specific fields.
      for j, fname in arm.fieldNames:
        let fty = arm.fieldTypes[j]
        let armPath = path & ".@" & $arm.tagOrdinal & "." & fname
        let (_, fReader) = emitTyAndReader(fty, armPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      caseStmt.add nnkOfBranch.newTree(tagLit, ctor)
    if hasElse:
      # For each disc-enum ordinal NOT covered by a non-else arm,
      # emit one `of <tagName>:` branch with a static discriminator
      # literal. Static-disc construction sidesteps the runtime
      # discriminant transition check that breaks the `var w` path.
      # `vDiscTags` carries the enum's full (name, ord) domain so we
      # have a concrete Nim identifier for each else-covered value.
      var nonElseOrds: seq[int]
      for arm in ty.vArms:
        if not arm.isElse: nonElseOrds.add arm.tagOrdinal
      for dt in ty.vDiscTags:
        if dt.ord in nonElseOrds: continue
        let tagLit = newCall(discTyId, newLit(dt.ord))
        var ctor = newTree(nnkObjConstr, objTyId)
        for i, fname in ty.vPlainFieldNames:
          let (_, fReader) = emitTyAndReader(
            ty.vPlainFieldTypes[i], path & "." & fname, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        ctor.add nnkExprColonExpr.newTree(
          ident(ty.vDiscName), newCall(discTyId, newLit(dt.ord)))  # RFC-0005 S8e
        for j, fname in elseArm.fieldNames:
          let armPath = path & ".@" & $elseArm.tagOrdinal & "." & fname
          let (_, fReader) = emitTyAndReader(
            elseArm.fieldTypes[j], armPath, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        caseStmt.add nnkOfBranch.newTree(tagLit, ctor)
      # RFC-0005 S8f. A NON-enum (`range[lo..hi]`) discriminator has no
      # `vDiscTags`, so the loop above rendered no branch for an
      # else-covered value: a `W(kind: 5, e: 42)` witness fell to the
      # `default` below and rendered `kind: 0, e: 0` -- a clean `sxSat`
      # whose witness never reached the target (#163 W6's own fixture).
      # Render ONE branch over the else arm's whole value set -- the
      # declared range minus the explicit tags, as ordinal intervals --
      # constructing with the discriminator bound to the case selector's
      # `let`: Nim accepts a runtime discriminator in an object constructor
      # when the enclosing `case` on that `let` proves its branch -- and
      # only for a discriminator type of at most 2^16 values, the limit
      # Nim puts on that proof (a wider range keeps the old fallback).
      if ty.vDiscTags.len == 0 and ty.vDiscTy.hasRange and
         ty.vDiscTy.rangeHi - ty.vDiscTy.rangeLo < 65536:
        var ranges: seq[NimNode]
        var lo = ty.vDiscTy.rangeLo
        let hi = ty.vDiscTy.rangeHi
        var explicit: seq[int64]
        for o in nonElseOrds: explicit.add int64(o)
        explicit.sort()
        proc addRun(ranges: var seq[NimNode]; a, b: int64) =
          if a > b: return
          let la = newCall(discTyId, newLit(a))
          if a == b: ranges.add la
          else: ranges.add infix(la, "..", newCall(discTyId, newLit(b)))
        for o in explicit:
          if o < lo or o > hi: continue
          addRun(ranges, lo, o - 1)
          lo = o + 1
        addRun(ranges, lo, hi)
        if ranges.len > 0:
          let selId = genSym(nskLet, "discSel")
          var ctor = newTree(nnkObjConstr, objTyId)
          for i, fname in ty.vPlainFieldNames:
            let (_, fReader) = emitTyAndReader(
              ty.vPlainFieldTypes[i], path & "." & fname, witId)
            ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
          ctor.add nnkExprColonExpr.newTree(ident(ty.vDiscName), selId)
          for j, fname in elseArm.fieldNames:
            let armPath = path & ".@" & $elseArm.tagOrdinal & "." & fname
            let (_, fReader) = emitTyAndReader(
              elseArm.fieldTypes[j], armPath, witId)
            ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
          var ofBr = newTree(nnkOfBranch)
          for r in ranges: ofBr.add r
          ofBr.add ctor
          caseStmt.add ofBr
          caseStmt[0] = selId
          caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
          # The selector must have the FIELD's own type (the reader's
          # `discTyId` is the range's base type).
          let fieldTy = newCall(ident"typeof", newDotExpr(
            defaultValueOf(objTyId), ident(ty.vDiscName)))
          let blk = newStmtList(
            newLetStmt(selId, newCall(fieldTy, discReaderExpr)), caseStmt)
          return (objTyId, newBlockStmt(blk))
    caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
    (objTyId, caseStmt)
  of itMultiVariant:
    # Phase 14 cycle A1d per ADR-0003 D1. Emit nested case
    # statements — one per axis, outer to inner — and at the
    # deepest level construct the object with plain fields + each
    # axis's chosen disc + that axis's active-arm fields. Witness
    # paths must match what `extractFromSymVal` writes for
    # svMultiVariant (runtime.nim ~1364-1374):
    #   <path>.<plainName>                         plain (shared)
    #   <path>.<discName>                          axis discriminator
    #   <path>.<discName>.@<tagOrdinal>.<fname>    arm-specific
    # `fields(w)` on the constructed object iterates active-arm
    # order: plain..., axis1, arm1-fields, axis2, arm2-fields...
    # which matches `renderAsChoices`'s iteration contract.
    let objTyId = userTypeName(ty, ty.mvObjectName)
    type AxisBind = tuple[
      discName: string,
      tagVal: NimNode,   ## RFC-0005 S8e: `DiscTy(ordinal)`, not the member name
      armFieldNames: seq[string],
      armFieldReaders: seq[NimNode]]
    proc emitMVBranch(axisIdx: int,
                      chosen: seq[AxisBind]): NimNode =
      if axisIdx == ty.mvAxes.len:
        var ctor = newTree(nnkObjConstr, objTyId)
        for i, fname in ty.mvPlainFieldNames:
          let (_, fReader) = emitTyAndReader(
            ty.mvPlainFieldTypes[i], path & "." & fname, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        for ab in chosen:
          ctor.add nnkExprColonExpr.newTree(
            ident(ab.discName), ab.tagVal)
          for j, fn in ab.armFieldNames:
            ctor.add nnkExprColonExpr.newTree(
              ident(fn), ab.armFieldReaders[j])
        return ctor
      let ax = ty.mvAxes[axisIdx]
      let discPath = path & "." & ax.discName
      let (discTyId, discReaderExpr) =
        emitTyAndReader(ax.discTy, discPath, witId)
      var caseStmt = newTree(nnkCaseStmt, discReaderExpr)
      # RFC-0005 S8s: an `else` arm renders one branch per enum ordinal it
      # covers (`discTags` minus the explicit arms), each with that static
      # discriminator, as the single-`case` emitter does. It used to render
      # its sentinel ordinal (`DiscTy(-1)`, a compile error).
      var nonElseOrds: seq[int]
      for arm in ax.arms:
        if not arm.isElse: nonElseOrds.add arm.tagOrdinal
      for arm in ax.arms:
        var tagOrds: seq[int]
        if arm.isElse:
          for dt in ax.discTags:
            if dt.ord notin nonElseOrds: tagOrds.add dt.ord
        else:
          tagOrds.add arm.tagOrdinal
        for tagOrd in tagOrds:
          let tagLit = newCall(discTyId, newLit(tagOrd))
          var armReaders: seq[NimNode]
          for j, fn in arm.fieldNames:
            let armPath = path & "." & ax.discName &
                          ".@" & $arm.tagOrdinal & "." & fn
            let (_, fr) = emitTyAndReader(arm.fieldTypes[j], armPath, witId)
            armReaders.add fr
          let body = emitMVBranch(axisIdx + 1, chosen & @[
            (discName: ax.discName, tagVal: newCall(discTyId, newLit(tagOrd)),
             armFieldNames: arm.fieldNames, armFieldReaders: armReaders)])
          caseStmt.add nnkOfBranch.newTree(tagLit, body)
      # RFC-0005 S8s: a NON-enum (`range[lo..hi]`) discriminator has no
      # `discTags`, so the loop above rendered no branch for an else-covered
      # value. Since S8s `allocateSym` admits those values (the axis's
      # declared range), so render them as the single-`case` emitter does
      # (RFC-0005 S8f): ONE branch over the range minus the explicit tags,
      # the discriminator bound to the case selector's `let`, only for a
      # discriminator type of at most 2^16 values (Nim's limit on proving a
      # runtime discriminator; a wider range keeps the fallback, whose
      # witness replay refutes).
      var elseArmIx = -1
      for i, arm in ax.arms:
        if arm.isElse: elseArmIx = i
      if elseArmIx >= 0 and ax.discTags.len == 0 and ax.discTy.hasRange and
         ax.discTy.rangeHi - ax.discTy.rangeLo < 65536:
        let elseArm = ax.arms[elseArmIx]
        var ranges: seq[NimNode]
        var lo = ax.discTy.rangeLo
        let hi = ax.discTy.rangeHi
        var explicit: seq[int64]
        for o in nonElseOrds: explicit.add int64(o)
        explicit.sort()
        proc addRun(ranges: var seq[NimNode]; a, b: int64) =
          if a > b: return
          let la = newCall(discTyId, newLit(a))
          if a == b: ranges.add la
          else: ranges.add infix(la, "..", newCall(discTyId, newLit(b)))
        for o in explicit:
          if o < lo or o > hi: continue
          addRun(ranges, lo, o - 1)
          lo = o + 1
        addRun(ranges, lo, hi)
        if ranges.len > 0:
          let selId = genSym(nskLet, "discSel")
          var armReaders: seq[NimNode]
          for j, fn in elseArm.fieldNames:
            let armPath = path & "." & ax.discName &
                          ".@" & $elseArm.tagOrdinal & "." & fn
            let (_, fr) = emitTyAndReader(elseArm.fieldTypes[j], armPath, witId)
            armReaders.add fr
          let body = emitMVBranch(axisIdx + 1, chosen & @[
            (discName: ax.discName, tagVal: selId,
             armFieldNames: elseArm.fieldNames, armFieldReaders: armReaders)])
          var ofBr = newTree(nnkOfBranch)
          for r in ranges: ofBr.add r
          ofBr.add body
          caseStmt.add ofBr
          caseStmt[0] = selId
          caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
          let fieldTy = newCall(ident"typeof", newDotExpr(
            defaultValueOf(objTyId), ident(ax.discName)))
          return newBlockStmt(newStmtList(
            newLetStmt(selId, newCall(fieldTy, discReaderExpr)), caseStmt))
      # Else covers any out-of-set disc value; same defensive
      # fallback as itVariant (line 599).
      caseStmt.add nnkElse.newTree(defaultValueOf(objTyId))
      caseStmt
    (objTyId, emitMVBranch(0, @[]))
  of itRef, itPtr:
    # RFC-0005 S8h. A `ref T`/`ptr T` position resolves through the witness's
    # `RefWitness` (`resolveRef`): nil, the object already built for another
    # position holding the same model address, or a cell built once and
    # filled from the model's INPUT heap. The fill is generic over the Nim
    # type, so a recursive field, a cycle and a case object reached through
    # a field render like a top-level param.
    #
    # Replaces Phase 15 R1/R9 and Cluster H Step C's readers, each of which
    # built a fresh object from leaves at `path`: a nil param rendered
    # non-nil, two params at one address rendered two objects, a recursive
    # field (an empty IR placeholder) rendered `nil` even when the path had
    # proved it live, and the fields rendered the heap the SUT had written by
    # the end of the path, not the one it was called with.
    let refTy = refWitnessTypeNode(ty, path, witId)
    if not resolvesByRef(ty):
      # A recursive field whose type reached the IR without a symbol, or a
      # `ptr` to a pointee `resolveRef` cannot allocate (an `UncheckedArray`,
      # a container): no Nim type to build the cell as. `witnessFidelity`
      # classifies it `wfUnexecutable`, so replay never trusts it.
      let placeholder = quote do:
        block:
          {.warning: "symex: this `ref`/`ptr` witness position renders as " &
                     "`nil`: no cell of its pointee type can be built " &
                     "(RFC-0005 S8h).".}
          nil
      return (refTy, placeholder)
    (refTy, resolveRefCall(refTy, newLit(path), witId))

proc emitTyAndReader*(ty: IRType, path: string, witId: NimNode): (NimNode, NimNode) =
  ## Returns (Nim type AST, witness-construction expression) for `ty` at
  ## witness path `path`. RFC-0005 S8e: every node of the result is its own
  ## copy. The builder above places one type node at several positions (a
  ## variant's type in each arm's constructor and in its `default`, a disc
  ## type in every tag conversion). With identifiers that was harmless; a
  ## SYMBOL node is annotated in place by semantic checking, so a shared one
  ## checked as a constructor head reaches the next position already typed as
  ## a value of the type, not the type itself.
  let (t, r) = emitTyAndReaderShared(ty, path, witId)
  (copyNimTree(t), copyNimTree(r))

proc irTypeHoldsPtr(t: IRType; depth = 0): bool =
  ## RFC-0005 S8bn (item 1). A value of type `t` holds a `ptr` somewhere
  ## (conservative past a depth bound).
  if t == nil: return false
  if depth > 8: return true
  case t.kind
  of itPtr: true
  of itRef: irTypeHoldsPtr(t.refPointeeTy, depth + 1)
  of itTuple:
    for f in t.fields:
      if irTypeHoldsPtr(f, depth + 1): return true
    false
  of itArray: irTypeHoldsPtr(t.elemTy, depth + 1)
  of itSeq: irTypeHoldsPtr(t.seqElemTy, depth + 1)
  of itDistinct: irTypeHoldsPtr(t.distinctBase, depth + 1)
  else: false

proc emitWitnessTuple(params: seq[IRParam]; witId: NimNode): (NimNode, NimNode) =
  ## The witness tuple of `params` over the `RawWitness` `witId`: (its type,
  ## its value). RFC-0005 S8h: every `ref`/`ptr` position in it resolves
  ## through ONE `RefWitness`, bound once around the tuple, so a cell held by
  ## two params (or a param and a field, or two elements) is one object.
  let ctxId = genSym(nskLet, "refWit")
  let (savedCtx, savedUsed) = (witnessRefCtx, witnessRefCtxUsed)
  witnessRefCtx = ctxId
  witnessRefCtxUsed = false
  var tupleTy = newTree(nnkTupleConstr)
  var tup = newTree(nnkTupleConstr)
  var vals: seq[NimNode]
  for p in params:
    let (pTy, pVal) = emitTyAndReader(p.ty, p.name, witId)
    tupleTy.add pTy
    tup.add pVal
    vals.add pVal
  let used = witnessRefCtxUsed
  (witnessRefCtx, witnessRefCtxUsed) = (savedCtx, savedUsed)
  if not used:
    return (tupleTy, tup)
  let ctxInit = newCall(stdName("newRefWitness"), witId)
  # RFC-0005 S8bn (item 1). Every position is built before any `ptr` that
  # may address it: a parameter holding no pointer first, then one holding
  # a pointer inside it, then a `ptr` parameter, each group in parameter
  # order. A pointer aimed at a field (`"&<cell>.<field>"`) then finds its
  # object built whichever parameter comes first; in parameter order,
  # `(pi: ptr int; q: Q)` built `pi` first and left it its own cell, so the
  # replay refuted a sound `sxSat`. The tuple keeps parameter order.
  var stmts = newStmtList(newLetStmt(ctxId, ctxInit))
  var ids = newSeq[NimNode](params.len)
  for rank in 0 .. 2:
    for i, p in params:
      let r = if p.ty != nil and p.ty.kind == itPtr: 2
              elif irTypeHoldsPtr(p.ty): 1
              else: 0
      if r != rank: continue
      ids[i] = genSym(nskLet, "witPos")
      stmts.add newTree(nnkLetSection,
        newIdentDefs(ids[i], copyNimTree(tupleTy[i]), vals[i]))
  var ordered = newTree(nnkTupleConstr)
  for id in ids: ordered.add id
  stmts.add ordered
  (tupleTy, nnkBlockExpr.newTree(newEmptyNode(), stmts))

# ---- Body markers -----------------------------------------------------------

## Body markers are procs (not templates) so semcheck doesn't elide
## the call site before the symex parser sees it. The parser
## recognizes the call by callee name; outside symex these run as
## ordinary procs whose body provides the dual-mode semantics.

# ---- Extension pragma -------------------------------------------------------

## Phase 9 user-extension hook. Attach to a proc the walker should
## not enter: `proc readSensor(): int {.symexOpaque.} = ...`.
## Inside symex, a call to the proc returns a fresh symbolic value and
## records `feOpaqueCallUnmodelled` (class `dcSubstituted`: the analysis
## put a free value where the real one goes). That gap is `scSpurious` on
## the paths through the call and `scIncomplete` on the run (RFC-0005), so:
##
## - a witness found past the call is reported `sxSat` only after replay
##   has run the real proc on it and reproduced the target
##   (`soundness.replay == rsConfirmed`) -- otherwise `sxUnknown`;
## - an `sxUnsat` is not `trusted()` while the gap is on the run.
##
## `gaps()` on the result names the call and its class, which is the lever
## (model the callee, or prove it irrelevant with `{.symexTransparent.}`).
## Outside symex the pragma is a no-op and the proc executes normally.
template symexOpaque*() {.pragma.}

## Issue #163 user-extension hook, and the one to reach for first for a
## logging/metrics/tracing call: attach to a VOID proc that cannot change
## anything the code under test observes — no result, nothing written through
## an argument, no state the SUT reads back — and symex DELETES the call
## instead of modelling it:
##
## ```nim
## proc trace(msg: string) {.symexTransparent.} = stderr.writeLine msg
## ```
##
## `{.symexOpaque.}` would also keep the walker out of `trace`'s body, but it
## additionally records a `dcSubstituted` gap on every path through the call,
## so a target behind it is `sxSat` only if replay confirms the witness and is
## never a trusted `sxUnsat`. That is the right price for `readSensor()`, whose
## result the SUT branches on, and the wrong price for a trace line. Use `symexOpaque`
## when the call's result or effects matter and cannot be modelled; use
## `symexTransparent` when the honest answer is that they do not matter.
##
## The promise is honoured only in statement position, and even there only
## when every argument is provably inert (a plain value — never a `var`
## formal, `ref`, `ptr`, or an object that might carry one). Two ways to
## over-claim it, and both fail the same safe way:
##
## - the result IS used (expression position) — `avResultUsed`;
## - a statement-position argument is NOT provably inert (e.g. `var x: int`
##   passed to a callee that writes through it) — `avArgNotInert`.
##
## Either way the call falls back to `symexOpaque` handling (its gap, with the
## consequences above), and the broken promise is reported on its own
## channel: an `AnnotationViolation` on `SymexResult.annotationViolations` and
## `SymexFinding.annotationViolations`, naming the pragma, the callee and the
## site. The channel is verdict-neutral -- it never changes a status -- and
## every report format renders it (GitHub output as an `::error`), because it
## is a defect in the annotated code, not in the analysis. An over-claimed
## pragma therefore costs precision, never soundness (never a false witness).
## Outside symex it is a no-op.
##
## One asymmetry worth knowing: the pragma is matched purely BY NAME (any
## module may declare its own private `{.pragma.}` template spelled the same
## — deliberate, and how `nelli/coverage` stays Z3-free), so an accidental
## name collision is possible. The risk is not symmetric between the two
## pragmas: colliding on `symexOpaque` fails SAFE (at worst one more
## `dcSubstituted` gap), but colliding on `symexTransparent` would fail UNSAFE — the
## call vanishes outright — so name this pragma with care in any module that
## does not import it from here.
template symexTransparent*() {.pragma.}

# RFC-z3-optional S1c: `symexTarget`/`symexAssert`/`symexAssume` moved to
# `engine/markers.nim` and are re-exported by name near the top of this
# file. They are Z3-free annotations that belong in production code, so
# they must not sit behind the walker's import.

# ---- Witness replay (RFC-0005 S2, §4.2) --------------------------------------
#
# The execution contract behind RFC-0005's SAT relaxation: a `sxSat`/`sxRaised`
# the engine would newly permit on a `scSpurious`-tainted path must first have
# its witness RUN against the real `fn`. S2 lands the substrate only -- the
# outcome type, the target-shaped `replayWitness` macro, the eligibility gate
# and (in `engine/markers.nim`) the stackable capture context. S10 wires it
# into the verdict of BOTH `runSymex` consumers (`symexFind` and the
# `symexFindAllWitnesses` codegen).
#
# WHY A MACRO. Invoking the SUT means splatting a typed witness tuple into its
# parameter list with `var`-param wrapping -- the same codegen
# `assertCoveredBy` does -- and `runSymex` is runtime code with no `fn`. So
# replay runs in macro-generated code AFTER `runSymex` returns (§4.2
# "Plumbing"). `emitReplayWitness` is the macro-time half S10 splices into
# the entry macros, which already hold the parsed `params`.
#
# CONTRACT CHANGE (§4.2, for §8.1 / S11's migration note): now that it is wired,
# `symexFind` EXECUTES `fn` on solver-chosen inputs, where it never ran `fn`
# before. Replay performs the SUT's side effects FOR REAL, at verdict time, in
# the caller's process -- and a `scSpurious` path is tainted precisely because
# it ran through an unmodelled (often effectful: `echo`/`writeFile`, #137) call.
#
# NON-TERMINATION (§4.2). There is deliberately no watchdog: an in-process one
# is not safely buildable under §1.5's no-nested-try constraint, and Invariant
# 3 is instead preserved by the ELIGIBILITY GATE -- a `dcFabricated`
# (k-unroll survivor) witness is by §0.3 an input on which the real program
# may still be looping, and the gate declines it without running it. What
# remains is the ordinary risk any PBT library takes calling a user proc,
# which nelli already takes in `forAll`/`fuzz`.

type ReplayOutcome* = enum
  ## RFC-0005 §4.2. The result of executing a witness against the real `fn`.
  ## Three-valued because a `bool` would conflate "refuted" with "could not
  ## run" -- different facts with different downstream reporting.
  ##
  ## DISTINCT from `SymexFindingStatus.sfReplayMiss` (Phase 14 B5,
  ## `engine/types.nim`): that status diagnoses a persisted REGRESSION SEED
  ## whose choice sequence no longer drives the test runtime onto its marker
  ## (strategy/generator skew, found by `assertCoveredBy` in the seed phase).
  ## `ReplayOutcome` is a VERDICT-TIME fact about a fresh solver witness from
  ## this run. A seed miss says the harness drifted; `roRefuted` says the
  ## model did.
  roConfirmed     ## the real fn reached the target on this witness -- the
                  ## target is reachable in reality, whatever the model's taint
  roRefuted       ## the real fn ran to completion (returned, or raised
                  ## something other than the target) on a FAITHFULLY rendered
                  ## witness and did not reach the target: this witness is
                  ## proven spurious (a confirmed model gap). It says nothing
                  ## about OTHER inputs -- the model's havoc symbols (an opaque
                  ## call's return, …) are not part of the witness, so the
                  ## verdict for a refuted candidate is sxUnknown, never sxUnsat
                  ## (§2.3 rule 4)
  roInconclusive  ## replay declined or not faithfully executable: an
                  ## ineligible taint, a witness outside the renderable
                  ## fragment, a target kind outside replay scope, or a lossy
                  ## witness that did not reach the target. The candidate
                  ## stays sxUnknown

func replayEligible*(pathTaint: Taint): bool =
  ## RFC-0005 §4.2 eligibility gate: replay is attempted only for a candidate
  ## whose path taint derives ENTIRELY from `dcFreshSymbol` sites. Read off
  ## `RawResult.pathTaint` (RFC-0005 S1) via the class algebra rather than a
  ## site list: `pathTaint(dcFreshSymbol) == {scSpurious}` and `dcOmitted`
  ## contributes `{}`, while `dcSubstituted`/`dcFabricated`/`dcNoAnswer` all
  ## put `scIncomplete` on the PATH -- so "entirely fresh-symbol" is exactly
  ## "within `pathTaint(dcFreshSymbol)`". A clean path (`{}`) is trivially
  ## eligible. A `dcFabricated` candidate is thereby `roInconclusive` by
  ## construction, at no cost (§0.3: the k-unroll SAT payoff is empty), and
  ## that is the bound on the non-termination hazard.
  pathTaint <= pathTaint(dcFreshSymbol)

func replayInScope*(target: SymexTarget): bool =
  ## RFC-0005 §4.2 "Defect-flavoured targets": the target kinds replay may
  ## execute. Outside scope the answer is `roInconclusive`, without running.
  ##   * `stkNilAccess` -- never: a raw-`ptr` nil deref is a SIGSEGV, not a
  ##     catchable Defect, and a `ref` nil deref is catchable only under
  ##     nil-checking builds. Executing could kill the caller's process.
  ##   * EVERY target under `--panics:on` (`nimPanics`), where a Defect is
  ##     not catchable and aborts the process. S2 declined only the Defect
  ##     TARGETS there; RFC-0005 S10 widens it to all targets, because S10
  ##     runs replay implicitly inside `symexFind`/`symexFindAllWitnesses`
  ##     on a CANDIDATE -- a witness from a path whose model diverges from
  ##     reality by construction (`scSpurious`), so the real `fn` may hit a
  ##     Defect the model never forked (an `IndexDefect` before a label, a
  ##     user `Defect` subtype the `endsWith("Defect")` convention misses)
  ##     even when the target itself is a label.
  ##   * `stkRaisedExn` for `NilAccessDefect` -- never, for `stkNilAccess`'s
  ##     reason (RFC-0005 S8k). S10 replays an `sxRaised` candidate against
  ##     `tRaisedExn(<its type>)`, and the walker's only producer of that
  ##     type is its nil-dereference fork, whose real run is a SIGSEGV in
  ##     the default build of the pinned toolchain (probed: a `ref` read or
  ##     write through nil, `--nilchecks:on` or not, never reaches an
  ##     `except NilAccessDefect` arm), not a Defect.
  ##   * otherwise every kind (`stkLabel`, the Defect targets, any other
  ##     `stkRaisedExn`): an escaping exception, Defects included, is caught
  ##     by the replay frame and classified.
  const panics = defined(nimPanics)
  if panics: return false
  case target.kind
  of stkLabel, stkAssertionViolation, stkIndexError, stkFieldDefect: true
  of stkRaisedExn: target.typeFilter != "NilAccessDefect"
  of stkNilAccess: false

func replayReached*(target: SymexTarget; hits: HashSet[string];
                    escaped: ref Exception): bool =
  ## RFC-0005 §4.2: did one real execution reach `target`? `hits` is the
  ## execution's own capture frame; `escaped` is the exception that escaped
  ## `fn` (nil when it returned normally). A label counts if it was hit at
  ## all, even if `fn` raised afterwards. The raise kinds mirror what the
  ## walker reports as the finding: an exception ESCAPING the SUT frame
  ## (`routeRaise`'s step 3 -- a handler-caught raise is never a finding),
  ## matched by exact type name for `stkRaisedExn` (the walker's
  ## `typeFilter == typeId` test) and by subtype for the builtin Defects
  ## (`assertCoveredBy`'s precedent).
  case target.kind
  of stkLabel:              target.label in hits
  of stkAssertionViolation: not escaped.isNil and escaped of AssertionDefect
  of stkIndexError:         not escaped.isNil and escaped of IndexDefect
  of stkFieldDefect:        not escaped.isNil and escaped of FieldDefect
  of stkRaisedExn:
    not escaped.isNil and
      (target.typeFilter.len == 0 or $escaped.name == target.typeFilter)
  of stkNilAccess:          false   ## out of scope; never executed

type WitnessFidelity = enum
  ## RFC-0005 §4.2 "Un-replayable witnesses". How faithfully `emitTyAndReader`
  ## renders a witness shape -- decided at macro time, per parameter, from
  ## the SAME `IRType` the reader walks. Ordered: the worst component wins.
  wfFaithful      ## the rendered value IS the solver's model value
  wfLossy         ## safe to execute, but the render is not the model (a
                  ## `ref` cell with a field kind the logical heap does not
                  ## model, or whose fields are unknown at macro time -- RFC-
                  ## 0005 S8h; `default(Object)` variant stubs; the
                  ## unsupported-field empty seq).
                  ## A HIT still confirms -- any concrete input that reaches the
                  ## target proves reachability -- but a MISS proves nothing
                  ## about the model's witness, so it is inconclusive
  wfUnexecutable  ## a placeholder that must never be run: the nil-proc
                  ## closure stub, the nil `ptr` to a pointee no cell can be
                  ## built for, the `__unsupported:` dummy `int`, a recursive
                  ## ref field with no type symbol (deref would crash or
                  ## misattribute a raise)

proc collectNominals(ty: IRType; acc: var Table[string, IRType];
                     seen: var HashSet[string]) =
  ## RFC-0005 S8h. Every fielded named object in the type tree `ty`, by
  ## `nominalId`: the only place a recursive field's placeholder pointee can
  ## learn its fields at macro time.
  if ty == nil: return
  case ty.kind
  of itTuple:
    if ty.nominalId.len > 0:
      if ty.isPlaceholder or seen.containsOrIncl(ty.nominalId): return
      acc[ty.nominalId] = ty
    for f in ty.fields: collectNominals(f, acc, seen)
  of itRef: collectNominals(ty.refPointeeTy, acc, seen)
  of itPtr: collectNominals(ty.ptrPointeeTy, acc, seen)
  of itArray: collectNominals(ty.elemTy, acc, seen)
  of itSeq: collectNominals(ty.seqElemTy, acc, seen)
  of itDistinct: collectNominals(ty.distinctBase, acc, seen)
  of itVariant:
    for f in ty.vPlainFieldTypes: collectNominals(f, acc, seen)
    for arm in ty.vArms:
      for f in arm.fieldTypes: collectNominals(f, acc, seen)
  of itMultiVariant:
    for f in ty.mvPlainFieldTypes: collectNominals(f, acc, seen)
    for ax in ty.mvAxes:
      for arm in ax.arms:
        for f in arm.fieldTypes: collectNominals(f, acc, seen)
  else: discard

proc refCellFidelity(ty: IRType; noms: Table[string, IRType];
                     inProgress: var HashSet[string]): WitnessFidelity =
  ## RFC-0005 S8h. The fidelity of a `ref`/`ptr` position: `resolveRef`
  ## renders the model's input heap exactly for the field kinds the logical
  ## heap models (`liftHeapValue`: int -- incl. enums --, bool, float, ref,
  ## ptr), so a cell of only those is faithful, recursively; a field of any
  ## other kind keeps its zero value (lossy), and a cell whose fields cannot
  ## be known at macro time is lossy too.
  if not resolvesByRef(ty): return wfUnexecutable
  var pointee = refPointeeOf(ty)
  if pointee.kind == itTuple and pointee.isPlaceholder:
    if pointee.nominalId.len == 0 or not noms.hasKey(pointee.nominalId):
      return wfLossy
    pointee = noms[pointee.nominalId]
  proc fieldFidelity(f: IRType; inProgress: var HashSet[string]): WitnessFidelity =
    case f.kind
    of itBool, itInt, itFloat32, itFloat64: wfFaithful
    of itRef, itPtr: refCellFidelity(f, noms, inProgress)
    # RFC-0005 S8ap: a string field, and a leaf-split seq / Table / HashSet
    # field whose content `renderHeapCompound` writes and `readCellField`
    # reads (`readCellSeq`/`readCellTable`/`readCellSet`): a seq of int,
    # bool, float or ref/ptr, a `Table[string, int|bool]`, a backed
    # `HashSet`. Any other compound field keeps its zero value (lossy).
    of itString: wfFaithful
    of itSeq:
      if isUnsupportedFieldPlaceholder(f): wfLossy
      else:
        case f.seqElemTy.kind
        of itBool, itInt, itFloat32, itFloat64: wfFaithful
        of itRef, itPtr: refCellFidelity(f.seqElemTy, noms, inProgress)
        else: wfLossy
    of itTable:
      if f.tabKeyTy.kind == itString and f.tabValTy.kind in {itInt, itBool} and
         isBackedTableTy(f.tabKeyTy, f.tabValTy): wfFaithful
      else: wfLossy
    of itSet:
      if isBackedSetElemTy(f.setElemTy): wfFaithful else: wfLossy
    else: wfLossy
  case pointee.kind
  of itBool, itInt, itFloat32, itFloat64: wfFaithful
  of itString, itSeq, itTable, itSet:   # RFC-0005 S8ap: `ref seq[int]` etc.
    fieldFidelity(pointee, inProgress)
  of itTuple:
    if pointee.objectName.len == 0: return wfLossy   ## `fieldPairs` names differ
    if pointee.nominalId.len > 0:
      # A cycle through this type is faithful if the rest of it is.
      if inProgress.containsOrIncl(pointee.nominalId): return wfFaithful
    var r = wfFaithful
    for f in pointee.fields: r = max(r, fieldFidelity(f, inProgress))
    if pointee.nominalId.len > 0: inProgress.excl pointee.nominalId
    r
  of itVariant:
    var r = fieldFidelity(pointee.vDiscTy, inProgress)
    for f in pointee.vPlainFieldTypes: r = max(r, fieldFidelity(f, inProgress))
    for arm in pointee.vArms:
      for f in arm.fieldTypes: r = max(r, fieldFidelity(f, inProgress))
    r
  else: wfLossy

proc witnessFidelity(ty: IRType; noms: Table[string, IRType]): WitnessFidelity =
  ## Mirrors `emitTyAndReader`'s arms one-for-one; keep them in lockstep.
  ## `noms`: `collectNominals` over every parameter (RFC-0005 S8h).
  template worst(a, b: WitnessFidelity): WitnessFidelity = max(a, b)
  template wf(t: IRType): WitnessFidelity = witnessFidelity(t, noms)
  case ty.kind
  of itBool, itInt, itFloat32, itFloat64, itString: wfFaithful
  of itDistinct: wf(ty.distinctBase)
  of itUninterp: wfUnexecutable
  of itRef, itPtr:
    var inProgress: HashSet[string]
    refCellFidelity(ty, noms, inProgress)
  of itTuple:
    if rendersAsDefaultObject(ty): wfLossy
    else:
      var r = wfFaithful
      for f in ty.fields: r = worst(r, wf(f))
      r
  of itArray: wf(ty.elemTy)
  of itSeq:
    if isUnsupportedFieldPlaceholder(ty): wfLossy
    else:
      case ty.seqElemTy.kind
      of itInt, itFloat32, itFloat64: wfFaithful
      of itRef: wf(ty.seqElemTy)   ## RFC-0005 S8h
      of itDistinct:   ## RFC-0005 S8bd: the base seq, converted back
        if isRenderableSeqElemTy(ty.seqElemTy): wfFaithful
        else: wfUnexecutable
      else: wfUnexecutable   ## the reader's defensive `error()` arm
  of itTable:   # RFC-0005 S8z: every renderable shape
    if isRenderableTableTy(ty.tabKeyTy, ty.tabValTy): wfFaithful
    else: wfUnexecutable
  of itSet:
    if isRenderableSetElemTy(ty.setElemTy): wfFaithful
    else: wfUnexecutable
  of itVariant:
    var r = wf(ty.vDiscTy)
    for f in ty.vPlainFieldTypes: r = worst(r, wf(f))
    for arm in ty.vArms:
      for f in arm.fieldTypes: r = worst(r, wf(f))
    r
  of itMultiVariant:
    var r = wfFaithful
    for f in ty.mvPlainFieldTypes: r = worst(r, wf(f))
    for ax in ty.mvAxes:
      r = worst(r, wf(ax.discTy))
      for arm in ax.arms:
        for f in arm.fieldTypes: r = worst(r, wf(f))
    r

proc emitWitnessSplat(callee: NimNode; nParams: int; witId: NimNode;
                      paramTys: seq[NimNode] = @[];
                      afterBind: NimNode = nil;
                      params: seq[IRParam] = @[];
                      globals: seq[NimNode] = @[]): NimNode =
  ## `callee(wit[0], wit[1], …)` with each argument first bound to a fresh
  ## `var` local, so `var T` parameters receive an addressable lvalue (Phase
  ## 14 A7b). Zero-cost for non-var params. Shared by `assertCoveredBy` and
  ## `emitReplayWitness` -- one splat shape for every place the library runs
  ## a SUT on a witness.
  ##
  ## RFC-0005 S10 (replay only; `assertCoveredBy` passes neither): with
  ## `paramTys` (`fn`'s DECLARED parameter types, `var` stripped) each local
  ## is bound as `wit[i]` when the rendered witness type already is the
  ## parameter type and as the conversion `T(wit[i])` otherwise -- the
  ## witness reader renders some parameter types as their carrier (a `Rune`
  ## as `int`, a `distinct` as its base) -- and a non-void `callee` has its
  ## result discarded. `afterBind` is spliced between the bindings and the
  ## call, so a caller can tell a conversion that raised from a `fn` that did.
  ##
  ## RFC-0005 S8bn (item 2): with `params` (`fn`'s IR parameters) and
  ## `globals` (the module-level `var`s `fn` can reach), a `ptr` parameter
  ## the witness aimed at a variable (`ptrAimsAt`) is handed that variable's
  ## address once the arguments are bound: a `var` parameter's own local
  ## (the one `fn` receives), or the global itself. No witness cell can be
  ## either location.
  var preamble = newStmtList()
  var call = newCall(callee)
  var pvars: seq[NimNode]
  for i in 0 ..< nParams:
    let pvar = genSym(nskVar, "pvar" & $i)
    pvars.add pvar
    let elem = nnkBracketExpr.newTree(witId, newLit(i))
    let init =
      if paramTys.len == 0: elem
      else:
        let ty = paramTys[i]
        quote do:
          (when `elem` is `ty`: `elem` else: `ty`(`elem`))
    preamble.add newTree(nnkVarSection,
      newIdentDefs(pvar, newEmptyNode(), init))
    call.add pvar
  for j in 0 ..< min(nParams, params.len):
    if params[j].ty == nil or params[j].ty.kind != itPtr: continue
    let pj = pvars[j]
    for i in 0 ..< min(nParams, params.len):
      if i == j or not params[i].isVar: continue
      let pi = pvars[i]
      let nm = newLit(params[i].name)
      preamble.add quote do:
        when typeof(addr `pi`) is typeof(`pj`):
          if ptrAimsAt(cast[pointer](`pj`), `nm`): `pj` = addr `pi`
        # RFC-0005 S8bn (item 4): or a part of it (`ptrAimPath`).
        when typeof(`pj`) is ptr:
          block:
            let pa = ptrAimPath(cast[pointer](`pj`), `nm`)
            if pa.hit:
              `pj` = ptrAimInto[typeof(`pi`), typeof(`pj`[])](`pi`, pa.path, 0)
    for g in globals:
      let nm = newLit(globalEnvPrefix & macros.strVal(owner(g)) & "." &
                      macros.strVal(g))
      preamble.add quote do:
        when typeof(addr `g`) is typeof(`pj`):
          if ptrAimsAt(cast[pointer](`pj`), `nm`): `pj` = addr `g`
        when typeof(`pj`) is ptr:
          block:
            let pa = ptrAimPath(cast[pointer](`pj`), `nm`)
            if pa.hit:
              `pj` = ptrAimInto[typeof(`g`), typeof(`pj`[])](`g`, pa.path, 0)
  if afterBind != nil: preamble.add afterBind
  if paramTys.len == 0:
    return newStmtList(preamble, call)
  let callStmt = quote do:
    when typeof(`call`) is void: `call`
    else: discard `call`
  newStmtList(preamble, callStmt)

proc formalParamTypes(fn: NimNode): seq[NimNode] =
  ## RFC-0005 S10. The declared parameter types of the typed proc `fn`, one
  ## per parameter, `var` stripped -- what replay's splat converts the
  ## rendered witness to. Empty when `fn`'s type is not a plain proc type
  ## (the caller then declines to replay).
  let ty = getTypeImpl(fn)
  if ty.kind != nnkProcTy or ty.len == 0 or ty[0].kind != nnkFormalParams:
    return @[]
  for i in 1 ..< ty[0].len:
    let d = ty[0][i]
    var t = d[^2]
    if t.kind == nnkVarTy: t = t[0]
    for _ in 0 ..< d.len - 2: result.add t

proc emitReplayWitness*(fn: NimNode; params: seq[IRParam];
                        witness, target, pathTaint: NimNode;
                        extraLossy: NimNode = newLit(false);
                        nilDeref: NimNode = newLit(false)): NimNode =
  ## RFC-0005 S2: the macro-time half of `replayWitness`, spliced by S10 into
  ## the entry macros' shared replay emitter (`emitRunSymexReplayed`). Emits
  ## an expression of type `ReplayOutcome`. `witness` is the typed witness
  ## tuple (the output of `emitTyAndReader`), `target` a `SymexTarget`
  ## expression, `pathTaint` a `Taint` expression (the candidate's).
  ## `extraLossy` (RFC-0005 S10) is a runtime `bool`: true when the model
  ## behind this witness is known NOT to be the rendered value even though
  ## its shape renders faithfully -- a candidate whose extraction recorded
  ## `feExtractionFailed` (a float leaf substituted by `0.0`). It demotes a
  ## miss from `roRefuted` to `roInconclusive`; a hit still confirms.
  ## `nilDeref` (RFC-0005 S8k) is a runtime `bool`: true when the witness's
  ## path went through the walker's nil-dereference edge
  ## (`SatCandidate.nilDerefOnPath`), whose real run is a SIGSEGV that would
  ## kill the process -- declined, never executed. Order of refusal, each
  ## one WITHOUT executing `fn`: ineligible taint, unexecutable witness
  ## shape, out-of-scope target kind, a nil-dereference path.
  var noms: Table[string, IRType]
  var seenNoms: HashSet[string]
  for p in params: collectNominals(p.ty, noms, seenNoms)
  var fidelity = wfFaithful
  for p in params: fidelity = max(fidelity, witnessFidelity(p.ty, noms))
  if fidelity == wfUnexecutable:
    # Decided at macro time: the splat is not even emitted, so a placeholder
    # (a nil proc, a nil ptr) can never be called.
    return bindSym"roInconclusive"
  let paramTys = formalParamTypes(fn)
  if paramTys.len != params.len:
    return bindSym"roInconclusive"   # not a plain proc type: never run it
  let witId = genSym(nskLet, "replayWit")
  let tgtId = genSym(nskLet, "replayTarget")
  let escId = genSym(nskVar, "replayEscaped")
  let boundId = genSym(nskVar, "replayArgsBound")
  # RFC-0005 S8bn (item 2): the module-level `var`s `fn` can reach, which a
  # `ptr` parameter's witness may be aimed at.
  var globals: seq[NimNode]
  for g in calleeOuterSyms(fn):
    if isModuleGlobal(g) and g.symKind == nskVar: globals.add g
  let splat = emitWitnessSplat(fn, params.len, witId, paramTys,
                               newAssignment(boundId, newLit(true)),
                               params, globals)
  let lossy = newLit(fidelity == wfLossy)
  # RFC-0005 S10. The rendered witness type is not always the parameter
  # type (a `Rune` renders as `int`, a `distinct` as its base, a table as
  # the reader's own instantiation). `convertible` is a COMPILE-TIME check
  # that every argument converts; a witness that does not is never run
  # (`roInconclusive`, permanently -- the same as a placeholder shape).
  # `converted` marks a run whose arguments went through a conversion: its
  # hit still confirms (it is a real execution of `fn` on a concrete input),
  # but a miss only demotes to `roInconclusive`, because a conversion may
  # round (`float32`) and so the input run need not be the model.
  var convertible = newLit(true)
  var converted = newLit(false)
  for i in 0 ..< params.len:
    let elem = nnkBracketExpr.newTree(witId, newLit(i))
    let ty = paramTys[i]
    convertible = infix(convertible, "and",
                        newCall(bindSym"compiles", newCall(ty, elem)))
    converted = infix(converted, "or", infix(elem, "isnot", ty))
  result = quote do:
    block:
      let `tgtId`: SymexTarget = `target`
      if not replayEligible(`pathTaint`) or not replayInScope(`tgtId`) or
         `nilDeref`:
        roInconclusive
      else:
        let `witId` {.used.} = `witness`
        when not (`convertible`):
          roInconclusive
        else:
          var `escId`: ref Exception = nil
          var `boundId` = false
          # §4.2 "Capture reentrancy": a nested frame, so an enclosing user
          # capture (`assertCoveredBy`) keeps its hits and does not see ours.
          symexCaptureBegin()
          try:
            `splat`
          except Exception as e:
            `escId` = e
          let hits = symexCaptureEnd()
          if not `boundId`: roInconclusive   # a conversion raised: fn never ran
          elif replayReached(`tgtId`, hits, `escId`): roConfirmed
          elif `lossy` or `extraLossy` or `converted`: roInconclusive
          else: roRefuted

macro replayWitness*(fn: typed; witness: typed; target: SymexTarget;
                     pathTaint: Taint): untyped =
  ## RFC-0005 §4.2: execute `witness` (a `SymexResult.witness`, or
  ## `.raisedWitness`, of a `symexFind(fn, …)` run) against the REAL `fn`
  ## and report whether it reaches `target`. Target-shaped, so the
  ## raise-flavoured targets §2.3 puts in scope are expressible: a `sxRaised`
  ## candidate is replayed with `tRaisedExn(r.raisedTypeId)` -- the claim
  ## that exact type ESCAPES `fn`, whatever the search target was (under E6 a
  ## non-excluded Defect surfaces as `sxRaised` under ANY target).
  ## `pathTaint` is the candidate's `RawResult.pathTaint`, the input to the
  ## eligibility gate (`replayEligible`).
  ##
  ## Returns `roInconclusive` WITHOUT running `fn` for an ineligible taint, a
  ## witness shape outside the faithfully-renderable fragment (`emitTyAndReader`
  ## placeholders -- permanently), or a target kind outside
  ## `replayInScope`. Otherwise runs `fn` once, inside its own nested capture
  ## frame, catching whatever escapes.
  let parsed = parseEntryImpl(fn, "replayWitness",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  emitReplayWitness(fn, parsed.params, witness, target, pathTaint)

# ---- Replay wired into the verdict (RFC-0005 S10, §2.3 rule 3) ---------------
#
# `runSymex` ends at `decideVerdict`, which cannot apply rule 3 (replay needs
# `fn`, and `runSymex` is runtime code with none -- §4.2 "Plumbing"). So a run
# whose only SAT lies on an `scSpurious`-tainted path returns `sxUnknown` with
# its SOLVED models in `RawResult.candidates` (`SatCandidate`), and the entry
# macro settles them here, after `runSymex` returns and BEFORE any
# `SymexResult`/`SymexFinding` is built or anything is persisted.
#
# CANDIDACY IS UNSPELLABLE AS SAT. A `SatCandidate` is not a `RawResult` and
# has no witness branch; its model is the private `input` field. This module
# alone reads it (`privateAccess`), through the two procs below, both
# private and reached from generated code only via `bindSym` inside
# `emitRunSymexReplayed`:
#   * `candidateInput` -- the model, for rendering the witness to REPLAY;
#   * `settleCandidate` -- the ONLY constructor of a `sxSat`/`sxRaised`
#     `RawResult` from a candidate, and only on `roConfirmed`.
# And `emitRunSymexReplayed` is the only place in this module that emits a
# `runSymex` call (pinned by `tsymex_rfc0005_s10_replay_verdict`), so an entry
# macro cannot obtain a `RawResult` that skipped the settle: forgetting replay
# is not expressible, and even a hand-rolled caller of `runSymex` elsewhere
# can only ever see a candidate's metadata, never a witness to report.
#
# REPLAY HAZARDS (§4.2), as contained here:
#   * Contract change -- `symexFind`/`symexFindAllWitnesses`/`symexForAll` now
#     EXECUTE `fn` at verdict time, on solver-chosen inputs, whenever a run's
#     only SAT is a replay-eligible candidate. Its side effects happen for
#     real, in the caller's process (a `scSpurious` path is tainted precisely
#     because it ran through something unmodelled, often an effect). Nothing
#     runs for a clean verdict, an `sxUnsat`, or an ineligible candidate.
#   * Link/load -- because the settle references `fn`, `fn` and its callees
#     are code-generated, linked and loaded into the caller's binary even
#     when no candidate is ever replayed (an undefined `importc`, a missing
#     `dynlib` such as `std/re`'s PCRE, now fails the build or start-up).
#     Not containable at runtime; `SymexSettings.replay = false` (static)
#     emits no reference to `fn` at all -- the pre-S10 verdict.
#   * Non-termination -- no watchdog (§1.5: not safely buildable in-process);
#     bounded by the eligibility gate, which never runs a `dcFabricated`
#     (k-unroll survivor) witness. What remains is the risk `forAll`/`fuzz`
#     already take calling a user proc.
#   * Defects -- caught by the replay frame and classified; under
#     `--panics:on` nothing is replayed (`replayInScope`); a raw-`ptr`
#     witness is never executed (`witnessFidelity`); a candidate whose path
#     went through the walker's nil-dereference edge, escaping or caught,
#     is never executed (RFC-0005 S8k: `nilDerefOnPath`, and a
#     `NilAccessDefect` raise target is out of `replayInScope`) -- the
#     walker models that edge as a raise, the default build SIGSEGVs.
#     Any other crash `fn` would also commit under `forAll` (SIGSEGV, stack
#     overflow, `quit`) off the modelled path is not containable in-process
#     and is not contained.
#   * Capture reentrancy -- each replay runs in its own nested capture frame
#     (`engine/markers.nim`), so a user's enclosing `assertCoveredBy`
#     capture neither loses hits nor sees replay's.
#   * Bounded replays -- candidates are replayed in discovery order, `sxSat`
#     claims before `sxRaised` claims (ADR-0012 D2's precedence, as rules
#     1-2), and the settle STOPS at the first `roConfirmed`: at most one
#     confirming execution, plus one per earlier refuted/declined candidate.
#
# THE TWO BLANKET VETOES (§2.5) are not consulted: they distrust the MODEL
# (a cap or closure decline anywhere), and a confirmed replay is a fact about
# the REAL `fn` -- it reached the target on a concrete input -- that no model
# defect can make false. Rules 1-2 still precede rule 3 (a clean winner means
# the raw status is already `sxSat`/`sxRaised`, and the settle is skipped).

privateAccess(SatCandidate)

proc candidateInput(c: SatCandidate): auto =
  ## RFC-0005 S10. The candidate's model, for the replay codegen to render
  ## into `fn`'s parameter tuple. Private: see the section comment.
  c.input

func candidateLossy*(c: SatCandidate): bool =
  ## RFC-0005 S10. True when the candidate's own extraction substituted a
  ## value (`feExtractionFailed`: a float leaf that did not resolve to a
  ## numeral was rendered `0.0`), so the rendered witness is not the model
  ## even where its shape is faithful -- replay's `extraLossy`.
  for e in c.errors:
    if e.kind == feExtractionFailed: return true
  false

proc settleCandidate(raw: RawResult; c: SatCandidate;
                     outcome: ReplayOutcome): RawResult =
  ## RFC-0005 S10 (§2.3 rule 3). Applies ONE candidate's replay outcome to
  ## the `sxUnknown` result `raw`:
  ##   * `roConfirmed` -- the verdict becomes the candidate's claim
  ##     (`sxSat`/`sxRaised`) carrying its model as the witness, its
  ##     `pathTaint` (still `scSpurious`, with RFC-0005 S11's `replay =
  ##     rsConfirmed` beside it -- the one writer of `rsConfirmed`) and its
  ##     own extraction errors after the run's. No `diagnostics`: every other finding is either a
  ##     candidate nobody confirmed or a clean one an unplaced decline
  ##     suppressed (`decideVerdict`'s `reachUnknown`, RFC-0005 S9).
  ##   * `roRefuted` -- stays `sxUnknown` (rule 4: the enlarged program
  ##     reaches the target; never `sxUnsat`), plus a `feReplayRefuted`
  ##     `sevHint` naming the witness's confirmed model gap (§4.2).
  ##   * `roInconclusive` -- unchanged.
  ## Private (the only candidate -> verdict constructor); see the section
  ## comment.
  result = raw
  case outcome
  of roInconclusive: discard
  of roRefuted:
    result.errors.add SymexErrorInfo(kind: feReplayRefuted, severity: sevHint,
      msg: "replay refuted a " & $c.status & " candidate (" &
           (if c.status == sxRaised: "raise " & c.raisedTypeId
            else: "target hit") &
           "): the real fn ran on the solver's witness without reaching " &
           "the target -- a confirmed model gap on a scSpurious path " &
           "(feReplayRefuted)")
  of roConfirmed:
    case c.status
    of sxSat:
      result = RawResult(status: sxSat, witness: c.input)
    of sxRaised:
      result = RawResult(status: sxRaised, raisedTypeId: c.raisedTypeId,
                         isDefect: c.isDefect, raisedMsg: c.raisedMsg,
                         raisedWitness: c.input)
    of sxUnsat, sxUnknown:
      return raw    ## not a claim; `toCandidate` never builds one
    result.abstractions = raw.abstractions
    result.obligations  = raw.obligations
    result.callStats    = raw.callStats
    result.errors       = raw.errors & c.errors
    # RFC-0005 S11: the claim's soundness -- its own path, the run's
    # coordinate (re-derived: the candidate's extraction errors are now part
    # of this result's error list), and the replay that confirmed it.
    result.soundness    = Soundness(pathTaint: c.pathTaint,
                                    runTaint: runTaintOf(result.errors),
                                    replay: rsConfirmed)
    result.bounds       = raw.bounds
    result.candidates   = raw.candidates
    result.annotationViolations = raw.annotationViolations   # RFC-0005 S8

proc emitRunSymexReplayed(fn: NimNode; params: seq[IRParam];
                          prog, target, settings: NimNode;
                          replayOn: bool): NimNode =
  ## RFC-0005 S10. THE `runSymex` call of every entry macro (`symexFind`,
  ## and `symexFindAllWitnesses` -- hence `symexForAll`): emits a block
  ## expression of type `RawResult` that runs the walker and then settles
  ## its candidates by replay (rule 3), so neither consumer can see a raw
  ## result that skipped the settle. `prog`/`target`/`settings` are the
  ## `SymexProgram`, `SymexTarget` and `SymexSettings` expressions the
  ## caller would have passed to `runSymex`.
  ##
  ## `replayOn` is the caller's STATIC `SymexSettings.replay`. Off, the
  ## emitted expression is the bare `runSymex` call: no reference to `fn` is
  ## generated at all, so `fn` and its callees need not link or load (the
  ## opt-out for a SUT that is analysable but not executable in the test
  ## binary), and every candidate stays `sxUnknown` -- the pre-S10 verdict.
  ##
  ## Settles only an `sxUnknown` (rules 1-2 already produced any clean
  ## verdict; `sxUnsat` has no candidates). For each candidate, in
  ## discovery order, `sxSat` claims first: renders its model through the
  ## same `emitTyAndReader` readers the verdict uses, replays it
  ## (`emitReplayWitness`) against the search target (an `sxSat` claim) or
  ## `tRaisedExn(<its raised type>)` (an `sxRaised` claim -- the claim that
  ## exact type escapes `fn`), and folds the outcome in with
  ## `settleCandidate`; stops at the first confirmation.
  let rawId     = genSym(nskLet, "rawPreReplay")
  let runCall = quote do:
    runSymex(`prog`, `target`, `settings`)
  if not replayOn:
    return runCall
  let witId  = genSym(nskLet, "candRawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(params, witId)
  let settledId = genSym(nskVar, "settled")
  let tgtId     = genSym(nskLet, "searchTarget")
  let candId    = genSym(nskForVar, "cand")
  let claimId   = genSym(nskForVar, "claim")
  let typedId   = genSym(nskLet, "candWitness")
  let outcomeId = genSym(nskLet, "replayOutcome")
  let replayTgt = genSym(nskLet, "replayTarget")
  let inputSym  = bindSym"candidateInput"
  let settleSym = bindSym"settleCandidate"
  # A zero-param `fn` has the empty tuple `()` as its witness, which is a
  # value but not a type annotation -- so annotate only a non-empty one.
  let typedDecl =
    if params.len == 0:
      quote do:
        let `typedId` {.used.} = `witnessTup`
    else:
      quote do:
        let `typedId` {.used.}: `tupleTy` = `witnessTup`
  let replay = emitReplayWitness(fn, params, typedId, replayTgt,
    newDotExpr(candId, ident"pathTaint"),
    newCall(bindSym"candidateLossy", candId),
    newDotExpr(candId, ident"nilDerefOnPath"))
  result = quote do:
    block:
      let `rawId` = `runCall`
      var `settledId` = `rawId`
      if `rawId`.status == sxUnknown and `rawId`.candidates.len > 0:
        let `tgtId`: SymexTarget = `target`
        block replayPass:
          for `claimId` in [sxSat, sxRaised]:
            for `candId` in `rawId`.candidates:
              if `candId`.status != `claimId`: continue
              let `replayTgt`: SymexTarget =
                if `claimId` == sxSat: `tgtId`
                else: tRaisedExn(`candId`.raisedTypeId)
              let `witId` {.used.} = `inputSym`(`candId`)
              `typedDecl`
              let `outcomeId` = `replay`
              `settledId` = `settleSym`(`settledId`, `candId`, `outcomeId`)
              if `outcomeId` == roConfirmed: break replayPass
      `settledId`

# ---- The driver macro -------------------------------------------------------

proc warnIncoherentSettings(settings: SymexSettings, entry: string) =
  ## RFC-0010 C3a. `validateSymexSettings` is exported and unit-tested and was
  ## called by nothing in `src/` -- a validator that never runs on a real
  ## configuration, which is this RFC's own pattern sitting inside the RFC that
  ## exists to end it. §5 required a decision: wire it in or delete it.
  ##
  ## Wire it in. Its warning (b) is "arithChecks is empty: no arithmetic defect
  ## forks will be emitted" -- precisely the defect round B found in the ten
  ## const literals, which had been running release-like for as long as they
  ## had existed. The one mechanism that could have caught it was already
  ## written; it was simply never called.
  ##
  ## RFC-0010 review round 2: this proc is no longer called directly from
  ## any entry macro. Every macro that reaches the walker under a
  ## caller-chosen `settings` calls `parseEntryImplWarned` below instead
  ## of `dsl_parser.parseEntryImpl` directly, and that wrapper is the one
  ## call site left that invokes this. That makes coverage true BY
  ## CONSTRUCTION rather than by each macro author remembering to add the
  ## call: a future entry macro gets the check for free by reusing the
  ## helper it already needs for parsing, not by a separate step that can
  ## be forgotten the way the original four call sites were.
  ##
  ## Known duplicate (RFC-0010 review round 2, finding R2-06): an
  ## incoherent `settings` passed to `assertCoveredBy` reaches THIS `for`
  ## loop twice for one user call -- once with `entry == "assertCoveredBy"`
  ## from its own `parseEntryImplWarned` call, once with
  ## `entry == "symexFind"` from the `symexFind` macro that
  ## `assertCoveredBy`'s expansion calls internally. See the long comment
  ## on `assertCoveredBy` (below) for why this is intentional and why a
  ## `{.compileTime.}` dedup here was tried and rejected as unsafe.
  for w in validateSymexSettings(settings):
    warning(entry & ": " & w)

proc parseEntryImplWarned(fn: NimNode, apiName: string,
                          settings: SymexSettings): ParseResult =
  ## The chokepoint referenced above. Parses `fn` exactly like
  ## `dsl_parser.parseEntryImpl` (it delegates to that proc for the parse
  ## itself) and, before doing so, unconditionally emits a `warning()` via
  ## `warnIncoherentSettings` when `settings` looks incoherent. That is ALL
  ## it does: nothing here rejects, fixes up, or substitutes a corrected
  ## `settings` -- a caller who ignores the compiler warning gets back
  ## exactly the same `ParseResult` as one who heeds it. Despite the RFC's
  ## review-round comments (kept verbatim below) using the word "validates",
  ## this is not validation in the gating sense; it is parse-plus-warn. The
  ## name was corrected from `parseEntryImplValidated` to
  ## `parseEntryImplWarned` in a later review round (finding R2-08) for
  ## exactly this reason.
  ##
  ## `dsl_parser.parseEntryImpl` (owned by RFC-parser-normalization N1,
  ## outside this file) takes only the derived `maxInst: int`, not
  ## `settings` itself -- its signature has no `static` settings value to
  ## inspect, so the warning cannot live inside it without changing that
  ## signature. This wrapper is the closest genuine chokepoint reachable
  ## from `symex.nim` alone: every macro that runs the WALKER under a
  ## caller-chosen `settings` (`symexFind`, `concolicCollect`,
  ## `concolicFlip`, `assertCoveredBy`, `symexFindAllWitnesses` — and,
  ## transitively, `symexForAll`, which itself emits a call to
  ## `symexFindAllWitnesses`) calls THIS instead of `parseEntryImpl`
  ## directly, so parsing and warning can never drift apart again for
  ## that set. The five cache/DB helper macros
  ## (`symexCacheKeyForFn`/`saveSymexWitness`/`loadSymexWitnesses`/
  ## `saveSymexVerdict`/`loadSymexVerdict`) still call `parseEntryImpl`
  ## directly and deliberately stay out of this: they don't run the walker
  ## themselves, they key or persist results computed elsewhere, so an
  ## arithChecks-empty warning at a cache lookup would be noise pointing at
  ## the wrong call site.
  ##
  ## `settings` is `static SymexSettings` at every call site (an entry
  ## macro's own `static` parameter), so this whole call resolves at macro
  ## time: zero runtime cost, and `warnIncoherentSettings`'s `warning()`
  ## lands on the user's call site, not inside the library.
  warnIncoherentSettings(settings, apiName)
  parseEntryImpl(fn, apiName, settings.budget.maxInstantiationsPerProc)

proc methodPrelude(fn: NimNode): NimNode =
  ## RFC-0005 S8bn (item 6). nil when every method `fn` calls (transitively)
  ## is registered (`dsl_parser.methodRegistry`); otherwise the statements
  ## that register them, emitted into the CALLER's scope, where each name
  ## resolves to every overload visible there. The entry macro then expands
  ## again after them, and its parse dispatches each method call over the
  ## overrides (`methodDispatchStmt`). A name not visible at the caller is
  ## recorded as such, and its calls stay declined.
  let names = unregisteredMethodNames(fn)
  if names.len == 0: return nil
  result = newStmtList()
  for nm in names:
    let id = ident(nm)
    let reg = newCall(bindSym"symexRegisterMethods", newLit(nm), id)
    let none = newCall(bindSym"symexRegisterNoMethods", newLit(nm))
    result.add quote do:
      when declared(`id`): `reg`
      else: `none`

proc targetLit(t: SymexTarget): NimNode =
  ## RFC-0005 S8bn. A static `SymexTarget` as an expression, for an entry
  ## macro's re-expansion (`methodPrelude`).
  case t.kind
  of stkLabel: newCall(bindSym"tLabel", newLit(t.label))
  of stkRaisedExn: newCall(bindSym"tRaisedExn", newLit(t.typeFilter))
  else: nnkObjConstr.newTree(bindSym"SymexTarget",
                             newColonExpr(ident"kind", newLit(t.kind)))

macro symexFind*(fn: typed,
                 target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): untyped =
  ## Symbolically execute `fn` searching for an input that reaches `target`.
  ## Returns `SymexResult[ParamTuple]` where `ParamTuple` is the proc's
  ## parameter list as a Nim tuple.
  # RFC-parser-normalization N1: routes through `parseEntryImpl` like
  # `symexFindAllWitnesses` — `parsed` is consumed at macro time here
  # (`.params` below) via the same helper, not a different shape.
  # RFC-0010 review round 2: goes through `parseEntryImplWarned`
  # (below `warnIncoherentSettings`), which warns on an incoherent
  # `settings` and THEN calls `parseEntryImpl` — a single call site both
  # entries share.
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  let pre = methodPrelude(fn)
  if pre != nil:
    return newTree(nnkStmtListExpr, pre, newCall(bindSym"symexFind", fn,
      targetLit(target), newLit(settings)))
  let parsed = parseEntryImplWarned(fn, "symexFind", settings)

  # Build the tuple type and witness-construction tuple. We genSym a
  # local name for the RawWitness so the witness-constructor calls
  # share an identity-equal NimNode with the `let` that binds it.
  let witId = genSym(nskLet, "rawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(parsed.params, witId)

  # ADR-0012 D2: a SEPARATE gensym for the per-diagnostic RawWitness
  # binding inside the diagnostics loop. Using a distinct name avoids any
  # shadowing concern with the outer `witId` binding.
  let diagWitId = genSym(nskLet, "diagRawWit")
  let (_, diagWitnessTup) = emitWitnessTuple(parsed.params, diagWitId)

  # `(int,)` is a syntactic 1-tuple; nnkTupleConstr with one child
  # renders correctly for both the type and the value.

  let bodyExpr   = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let uxhExpr    = parsed.userExnHierarchyNimNode  ## Phase 15 E4a
  let peExpr     = parsed.parseErrorsNimNode       ## Phase 15 G1c
  let avExpr     = parsed.annotationViolationsNimNode  ## RFC-0005 S8

  # RFC-0005 S10: the walker run AND the rule-3 replay settle of its
  # candidates, in one emitted expression (`emitRunSymexReplayed`) -- the
  # `case raw.status` below only ever sees a settled result.
  let progId = genSym(nskLet, "prog")
  let runReplayed = emitRunSymexReplayed(fn, parsed.params, progId,
                                         newLit(target), newLit(settings),
                                         settings.replay)

  result = quote do:
    block:
      let `progId` = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`,
                              userExnHierarchy: `uxhExpr`,
                              parseErrors: `peExpr`,
                              annotationViolations: `avExpr`)
      let raw = `runReplayed`
      ## ADR-0012 D2: type each RawDiagnostic into DefectFinding[T] by
      ## rebinding diagWitId per entry and running the same witnessTup reader.
      let diagResult = block:
        var diagSeq: seq[DefectFinding[`tupleTy`]]
        for diagEntry in raw.diagnostics:
          let `diagWitId` = diagEntry.raisedWitness
          diagSeq.add DefectFinding[`tupleTy`](
            raisedTypeId: diagEntry.raisedTypeId,
            defectKind:   typeIdToDefectKind(diagEntry.raisedTypeId),
            isDefect:     diagEntry.isDefect,
            raisedMsg:    diagEntry.raisedMsg,
            witness:      `diagWitnessTup`,
            heapSnapshot: readHeapSnapshot(`diagWitId`))
        diagSeq
      case raw.status
      of sxSat:
        let `witId` = raw.witness
        SymexResult[`tupleTy`](status: sxSat, witness: `witnessTup`,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               heapSnapshot: readHeapSnapshot(`witId`),
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               fromCache: false,
                               diagnostics: diagResult)
      of sxUnsat:
        SymexResult[`tupleTy`](status: sxUnsat,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               fromCache: false,
                               diagnostics: diagResult)
      of sxUnknown:
        SymexResult[`tupleTy`](status: sxUnknown,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               fromCache: false,
                               diagnostics: diagResult)
      of sxRaised:
        # Phase 15 E2b. The walker reached a reachable `raise`; surface the
        # raised type id PLUS the reconstructed witness that reaches it (solved
        # from the raise-path condition). `witId` binds `raw.raisedWitness` so
        # the shared `witnessTup` reader reconstructs the SUT input tuple exactly
        # as on the `sxSat` path.
        let `witId` = raw.raisedWitness
        SymexResult[`tupleTy`](status: sxRaised,
                               raisedTypeId: raw.raisedTypeId,
                               raisedWitness: `witnessTup`,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               heapSnapshot: readHeapSnapshot(`witId`),
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               fromCache: false,
                               diagnostics: diagResult)

# ---- concolicCollect (RFC-fuzzer-nextgen G1b) -------------------------------

macro concolicCollect*(fn: typed, trace, bindings: typed,
                       settings: static SymexSettings = defaultSymexSettings(),
                       maxDraws: static int = defaultMaxConcolicDraws
                      ): ConcolicCollectResult =
  ## The G1b concolic entry: draw-symbolication + concrete-trace constraint
  ## collection (RFC §G-concolic steps 2-3 — no branch-flipping, that's G2).
  ##
  ## `fn` is the property proc (named or an inline `proc(x: T) = …` literal,
  ## same capture contract as `symexFind` — routes through the SAME
  ## `parseEntryImplWarned` helper, so `fn` becomes a walkable
  ## `SymexProgram` exactly as it does there, AND an incoherent `settings`
  ## warns exactly as it does there. `trace` is the recorded concrete draw
  ## sequence (`seq[ChoiceNode]`) the corpus entry replays; `bindings` says,
  ## per `fn` parameter, whether it's a direct (symbolic) draw or a
  ## concretized (opaque-combinator) value — see `ConcolicParamBinding`.
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  let pre = methodPrelude(fn)
  if pre != nil:
    return newTree(nnkStmtListExpr, pre, newCall(bindSym"concolicCollect",
      fn, trace, bindings, newLit(settings), newLit(maxDraws)))
  let parsed = parseEntryImplWarned(fn, "concolicCollect", settings)
  let bodyExpr   = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let uxhExpr    = parsed.userExnHierarchyNimNode
  let peExpr     = parsed.parseErrorsNimNode
  let avExpr     = parsed.annotationViolationsNimNode  ## RFC-0005 S8
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`, body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`, userExnHierarchy: `uxhExpr`,
                              parseErrors: `peExpr`,
                              annotationViolations: `avExpr`)
      runConcolicCollectImpl(prog, `trace`, `bindings`, `settings`, `maxDraws`)

# ---- concolicFlip (RFC-fuzzer-nextgen G2) -----------------------------------

macro concolicFlip*(fn: typed, trace, bindings: typed,
                    targetBranchIndex: typed,
                    settings: static SymexSettings = defaultSymexSettings(),
                    maxDraws: static int = defaultMaxConcolicDraws,
                    maxRelaxationAttempts: static int = defaultMaxRelaxationAttempts,
                    z3TimeoutMs: static uint = defaultZ3TimeoutMs
                   ): ConcolicFlipResult =
  ## The G2 entry: branch-flip solve + choice-sequence materialization (RFC
  ## §G-concolic steps 4-5), with the bounded optimistic fallback. Same
  ## macro-capture contract as `concolicCollect` (routes through
  ## `parseEntryImplWarned`) — `fn`/`trace`/`bindings` are exactly G1b's. G2 adds
  ## `targetBranchIndex`: which recorded `if`-decision (occurrence order
  ## along the concrete replay, i.e. an index into the collected
  ## `branchTrace`) to flip — a caller-supplied designator at G2; G3 wires
  ## frontier-stall selection on top of this later.
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  let pre = methodPrelude(fn)
  if pre != nil:
    return newTree(nnkStmtListExpr, pre, newCall(bindSym"concolicFlip",
      fn, trace, bindings, targetBranchIndex, newLit(settings),
      newLit(maxDraws), newLit(maxRelaxationAttempts), newLit(z3TimeoutMs)))
  let parsed = parseEntryImplWarned(fn, "concolicFlip", settings)
  let bodyExpr   = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let uxhExpr    = parsed.userExnHierarchyNimNode
  let peExpr     = parsed.parseErrorsNimNode
  let avExpr     = parsed.annotationViolationsNimNode  ## RFC-0005 S8
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`, body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`, userExnHierarchy: `uxhExpr`,
                              parseErrors: `peExpr`,
                              annotationViolations: `avExpr`)
      runConcolicFlipImpl(prog, `trace`, `bindings`, `targetBranchIndex`,
                         `settings`, `maxDraws`, `maxRelaxationAttempts`,
                         `z3TimeoutMs`)

# ---- allRaiseFindings -------------------------------------------------------

proc allRaiseFindings*[T](r: SymexResult[T]): seq[DefectFinding[T]] =
  ## ADR-0012 D2. Returns the complete set of raise findings for a result:
  ## when `r.status == sxRaised`, prepends a `DefectFinding[T]` built from
  ## the winning branch fields to `r.diagnostics`; otherwise returns
  ## `r.diagnostics` unchanged (which may be non-empty for sxSat results
  ## where incidental raises were discovered before the label was hit).
  ## `isDefect` is derived from the type id suffix; `raisedMsg` is not
  ## available at the public-type level and is always `none`.
  if r.status == sxRaised:
    let winning = DefectFinding[T](
      raisedTypeId: r.raisedTypeId,
      defectKind:   typeIdToDefectKind(r.raisedTypeId),
      isDefect:     r.raisedTypeId.endsWith("Defect"),
      raisedMsg:    none(string),
      witness:      r.raisedWitness,
      heapSnapshot: r.heapSnapshot)
    @[winning] & r.diagnostics
  else:
    r.diagnostics

# ---- assertCoveredBy --------------------------------------------------------

macro assertCoveredBy*(fn: typed,
                       target: static SymexTarget,
                       testFn: typed = nil,
                       settings: static SymexSettings = defaultSymexSettings()
                      ): untyped =
  ## Prove that `testFn`, invoked on the symex witness for `target`
  ## inside `fn`, actually exercises that target. Raises
  ## `AssertionDefect` when symex found a witness (`sxSat`) but the
  ## testFn run did not observe the target. UNSAT vacuously passes;
  ## UNKNOWN raises (cycle 4 will gate this on a setting).
  ##
  ## `testFn` defaults to `fn` itself — the common shape where the
  ## same code under symex is the same code under random PBT.
  ##
  ## Known cosmetic duplicate (RFC-0010 review round 2, finding R2-06): an
  ## incoherent `settings` here prints the `warnIncoherentSettings` warning
  ## TWICE — once as `assertCoveredBy: ...` (this macro's own
  ## `parseEntryImplWarned` call below) and once as `symexFind: ...`,
  ## because the block this macro expands to calls the public `symexFind`
  ## macro internally (see `symexFind(\`fn\`, ...)` a little further down),
  ## which independently re-validates the SAME `settings` through its own
  ## `parseEntryImplWarned` call. Both warnings resolve to the same
  ## compile-time `warning()` statement (`warnIncoherentSettings`, above
  ## `parseEntryImplWarned`); the compiler's instantiation trace for both
  ## points back to this exact call site, so nothing here is misattributed
  ## -- it is genuinely one incoherent `settings` value producing two
  ## printed lines for one user call. This is INTENTIONAL, not a bug to
  ## silence: routing this macro's internal `symexFind` call through raw
  ## `parseEntryImpl` to skip the re-validation was evaluated and rejected
  ## -- it would reopen the exact bypass this RFC closed, for the sole
  ## benefit of quieter output. A `{.compileTime.}`-set dedup keyed on the
  ## call-site `NimNode`'s `lineInfoObj` was also evaluated (round 2
  ## follow-up) and rejected: measured experimentally, the `fn` NimNode
  ## seen INSIDE the nested `symexFind` expansion does not carry this
  ## call site's line info -- it carries the fixed source position of the
  ## `quote do:` block below that constructs the nested call, which is
  ## IDENTICAL for every `assertCoveredBy` call anywhere in the program.
  ## Deduping on it would not merely fail to suppress this pair; it would
  ## silently cross-suppress the SECOND warning from every OTHER, unrelated
  ## incoherent `assertCoveredBy` call in the whole compilation after the
  ## first one -- a correctness regression far worse than double-printed
  ## noise. Two harmless corollaries worth knowing: (1) the multi-target
  ## `assertCoveredBy` overload below dispatches each target to THIS macro,
  ## so an N-target call with incoherent `settings` prints this pair N
  ## times, once per target; (2) a caller invoking `symexFind` directly
  ## never sees the duplicate -- it is specific to routing through
  ## `assertCoveredBy`.
  # RFC-parser-normalization N1: routes through `parseEntryImpl`, same as
  # `symexFind` above — `parsed` is consumed at macro time via the same
  # helper `symexFindAllWitnesses` uses.
  # RFC-0010 review round 2: via `parseEntryImplWarned`, so an
  # incoherent `settings` warns here too.
  let parsed = parseEntryImplWarned(fn, "assertCoveredBy", settings)

  let actualTestFn =
    if testFn.kind == nnkNilLit: fn else: testFn

  # Splat the witness tuple into testFn's positional params.
  # Phase 14 A7b: wrap each param in a fresh `var` local before the
  # call so `var T` parameters receive an addressable lvalue.
  # Pre-A7b this emitted `testFn(wit[0], wit[1], ...)` which fails
  # to compile for SUTs that take any `var T`. The wrapping is
  # zero-cost for non-var params and idiomatic for var params.
  # (RFC-0005 S2: the splat is `emitWitnessSplat`, shared with replay.)
  let witId = genSym(nskLet, "wit")
  let splatBlock = emitWitnessSplat(actualTestFn, parsed.params.len, witId)

  # gensym shared identifiers used across the cover-check sub-quote
  # and the main quote — quote-do hygiene would otherwise mint
  # fresh symbols per block.
  let hitsId           = genSym(nskLet, "hits")
  let assertionRaisedId = genSym(nskVar, "assertionRaised")
  let indexRaisedId     = genSym(nskVar, "indexRaised")
  let fieldRaisedId     = genSym(nskVar, "fieldRaised")
  let anyRaisedId       = genSym(nskVar, "anyRaised")        ## Phase 15 E2a

  # We dispatch on `target.kind` at macro time so that only the
  # branch-appropriate field is referenced in the emitted code.
  # Splicing a `static SymexTarget` of a non-stkLabel kind via
  # quote-do would otherwise force Nim to materialise an
  # nnkObjConstr that names every field — but a variant-object's
  # `label` field is invalid under `stkAssertionViolation`.
  let coveredExpr =
    case target.kind
    of stkLabel:
      let labelLit = newLit(target.label)
      quote do: (`labelLit` in `hitsId`)
    of stkAssertionViolation:
      quote do: `assertionRaisedId`
    of stkIndexError:
      quote do: `indexRaisedId`
    of stkFieldDefect:
      quote do: `fieldRaisedId`
    of stkRaisedExn:
      quote do: `anyRaisedId`   ## Phase 15 E2a: covered iff the SUT raised
    of stkNilAccess:
      quote do: `anyRaisedId`   ## Phase 15 R5: covered iff the SUT nil-derefed
  let failMsg =
    case target.kind
    of stkLabel:
      newLit("assertCoveredBy: testFn did not reach symexTarget(\"" &
             target.label & "\") on the symex witness")
    of stkAssertionViolation:
      newLit("assertCoveredBy: testFn did not raise AssertionDefect " &
             "on the symex witness (target was tAssertionViolation)")
    of stkIndexError:
      newLit("assertCoveredBy: testFn did not raise IndexDefect " &
             "on the symex witness (target was tIndexError)")
    of stkFieldDefect:
      newLit("assertCoveredBy: testFn did not raise FieldDefect " &
             "on the symex witness (target was tFieldDefect)")
    of stkRaisedExn:
      newLit("assertCoveredBy: testFn did not raise an exception " &
             "on the symex witness (target was tRaisedExn)")
    of stkNilAccess:
      newLit("assertCoveredBy: testFn did not raise NilAccessDefect " &
             "on the symex witness (target was tNilAccess)")
  let targetDescLit = newLit(describeTarget(target))

  # Rebuild the target node from its kind so the spliced AST is
  # always well-formed for the variant.
  let targetExpr =
    case target.kind
    of stkLabel:           newCall(bindSym"tLabel", newLit(target.label))
    of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
    of stkIndexError:      newCall(bindSym"tIndexError")
    of stkFieldDefect:     newCall(bindSym"tFieldDefect")
    of stkRaisedExn:       newCall(bindSym"tRaisedExn", newLit(target.typeFilter))
    of stkNilAccess:       newCall(bindSym"tNilAccess")

  let gapsSym = bindSym"findingGaps"   ## RFC-0005 S11 (private helper)
  result = quote do:
    block:
      let r = symexFind(`fn`, `targetExpr`, `settings`)
      case r.status
      of sxSat:
        let `witId` = r.witness
        symexCaptureBegin()
        var `assertionRaisedId` = false
        var `indexRaisedId` = false
        var `fieldRaisedId` = false
        var `anyRaisedId` = false   ## Phase 15 E2a: any exception raised
        try:
          `splatBlock`
        except AssertionDefect:
          `assertionRaisedId` = true
          `anyRaisedId` = true
        except IndexDefect:
          `indexRaisedId` = true
          `anyRaisedId` = true
        except FieldDefect:
          `fieldRaisedId` = true
          `anyRaisedId` = true
        except NilAccessDefect:                       ## Phase 15 R5
          `anyRaisedId` = true
        except CatchableError:
          `anyRaisedId` = true
        let `hitsId` = symexCaptureEnd()
        let covered = `coveredExpr`
        recordSymexFinding(SymexFinding(
          targetDesc:     `targetDescLit`,
          status:         sfSat,
          covered:        covered,
          witnessChoices: renderAsChoices(`witId`),
          z3Version:      z3FullVersion(),
          soundness:      r.soundness,              ## RFC-0005 S11
          gaps:           `gapsSym`(r.errors),
          annotationViolations: r.annotationViolations))
        if not covered:
          raise newException(AssertionDefect, `failMsg`)
      of sxUnsat:
        recordSymexFinding(SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnsat, covered: true,
          z3Version:  z3FullVersion(),
          soundness:  r.soundness,                  ## RFC-0005 S11
          gaps:       `gapsSym`(r.errors),
          annotationViolations: r.annotationViolations))
        discard  # vacuous pass
      of sxUnknown:
        recordSymexFinding(SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnknown, covered: false,
          z3Version:  z3FullVersion(),
          soundness:  r.soundness,                  ## RFC-0005 S11
          gaps:       `gapsSym`(r.errors),
          annotationViolations: r.annotationViolations))
        let s: SymexSettings = `settings`
        if not s.acceptUnknownAsCovered:
          raise newException(AssertionDefect,
            "assertCoveredBy: symex returned UNKNOWN; cannot prove " &
            "coverage (set acceptUnknownAsCovered = true to downgrade)")
      of sxRaised:
        # Phase 16 D1a: defect targets (tAssertionViolation, tIndexError,
        # tFieldDefect, tNilAccess) now return sxRaised with a populated
        # `raisedWitness` (the path-constrained witness that triggers the
        # raise). Replay it through testFn — the same witness-replay logic
        # as sxSat — to validate that testFn actually exercises the defect.
        # Before D1a (E2a STRUCTURAL) no witness was available; the old
        # comment "no witness-replay coverage check" no longer applies.
        let `witId` = r.raisedWitness
        symexCaptureBegin()
        var `assertionRaisedId` = false
        var `indexRaisedId` = false
        var `fieldRaisedId` = false
        var `anyRaisedId` = false
        try:
          `splatBlock`
        except AssertionDefect:
          `assertionRaisedId` = true
          `anyRaisedId` = true
        except IndexDefect:
          `indexRaisedId` = true
          `anyRaisedId` = true
        except FieldDefect:
          `fieldRaisedId` = true
          `anyRaisedId` = true
        except NilAccessDefect:
          `anyRaisedId` = true
        except CatchableError:
          `anyRaisedId` = true
        let `hitsId` = symexCaptureEnd()
        let covered = `coveredExpr`
        recordSymexFinding(SymexFinding(
          targetDesc:     `targetDescLit`,
          status:         sfRaised,
          covered:        covered,
          witnessChoices: renderAsChoices(`witId`),
          z3Version:      z3FullVersion(),
          soundness:      r.soundness,              ## RFC-0005 S11
          gaps:           `gapsSym`(r.errors),
          annotationViolations: r.annotationViolations))
        if not covered:
          raise newException(AssertionDefect, `failMsg`)

macro assertCoveredBy*(fn: typed,
                       targets: static openArray[SymexTarget],
                       testFn: typed = nil,
                       settings: static SymexSettings = defaultSymexSettings()
                      ): untyped =
  ## Multi-target form: prove `testFn` covers every target. Each
  ## target is dispatched through the single-target `assertCoveredBy`;
  ## failures are accumulated and reported as one aggregate message.
  let failuresId = genSym(nskVar, "failures")
  result = newStmtList()
  result.add quote do:
    var `failuresId`: seq[string] = @[]
  for t in targets:
    let tNode =
      case t.kind
      of stkLabel:              newCall(bindSym"tLabel", newLit(t.label))
      of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
      of stkIndexError:         newCall(bindSym"tIndexError")
      of stkFieldDefect:        newCall(bindSym"tFieldDefect")
      of stkRaisedExn:          newCall(bindSym"tRaisedExn", newLit(t.typeFilter))
      of stkNilAccess:          newCall(bindSym"tNilAccess")   ## Phase 15 R5
    let settingsNode = newLit(settings)
    let inner = newCall(ident"assertCoveredBy", fn, tNode, testFn, settingsNode)
    result.add quote do:
      try:
        `inner`
      except AssertionDefect as e:
        `failuresId`.add e.msg
  let totalLit = newLit(targets.len)
  result.add quote do:
    if `failuresId`.len > 0:
      var msg = "assertCoveredBy (multi): " & $`failuresId`.len &
                " of " & $`totalLit` & " targets uncovered:"
      for f in `failuresId`:
        msg.add "\n  - " & f
      raise newException(AssertionDefect, msg)
  result = nnkBlockStmt.newTree(newEmptyNode(), result)

# ---- Macro forms for the content-addressed DB API ---------------------------
#
# These macros parse the typed SUT to a SymexProgram (so the IR hash
# in the cache key reflects the same IR the walker will see), then
# delegate to the runtime impl. The pure (testable) part of the key
# derivation lives in nelli/smt/canonicalize.

proc rebuildTargetNode(target: SymexTarget): NimNode =
  ## Macro-time fresh constructor call for `target`. Splicing a
  ## `static SymexTarget` of a non-stkLabel kind directly via
  ## `quote do` triggers Nim to materialise an nnkObjConstr that
  ## names every field — invalid for variants. Rebuilding via the
  ## `t*` constructors is always well-formed.
  case target.kind
  of stkLabel:              newCall(bindSym"tLabel", newLit(target.label))
  of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
  of stkIndexError:         newCall(bindSym"tIndexError")
  of stkFieldDefect:        newCall(bindSym"tFieldDefect")
  of stkRaisedExn:          newCall(bindSym"tRaisedExn", newLit(target.typeFilter))
  of stkNilAccess:          newCall(bindSym"tNilAccess")   ## Phase 15 R5

macro symexCacheKeyForFn*(fn: typed,
                           target: static SymexTarget,
                           settings: static SymexSettings =
                             defaultSymexSettings()
                          ): string =
  ## Phase 13 cycle 2 — test helper. Emits a runtime expression
  ## that evaluates to the bare content-addressed key (no
  ## `:sat`/`:unsat`/`:unk` suffix) for `fn` + `target` + `settings`
  ## under the current Z3 / Nim / walker / rendering versions.
  ##
  ## Tests use this to probe `db.loadPrimary` directly without
  ## reconstructing `SymexProgram` by hand, while still pinning the
  ## suffix participation contract. NOT intended for production
  ## consumers — they should use `saveSymexWitness` /
  ## `loadSymexWitnesses` which encapsulate the suffix.
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  let parsed = parseEntryImpl(fn, "symexCacheKeyForFn",
                               settings.budget.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`)
      symexCacheKey(prog, `targetExpr`, `settings`,
                    z3Version        = z3FullVersion(),
                    nimVersion       = NimVersion,
                    walkerVersion    = symexWalkerVersion,
                    renderingVersion = renderAsChoicesVersion)

macro saveSymexWitness*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings,
                        finding: SymexFinding,
                        maxEntries: int = 64): untyped =
  ## Persist `finding`'s witness under the content-addressed cache
  ## key derived from `fn`'s IR, the target, the witness-relevant
  ## subset of `settings`, and the current Z3/Nim/walker versions.
  ## Non-Sat findings are skipped.
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  let parsed = parseEntryImpl(fn, "saveSymexWitness",
                               settings.budget.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      saveSymexWitnessImpl(`db`, prog, `targetExpr`, `settings`,
                            `finding`, dbErrors, `maxEntries`)
      # `dbErrors` is captured in this scope so the macro emission
      # type-checks; Phase 13 cycle 7 wires the engine flow that
      # threads these errors into Report.dbErrors. Until then the
      # public macro form discards them — matching the pre-RFC
      # behavior of silently swallowing rare DB failures.

macro loadSymexWitnesses*(db: ExampleDatabase, fn: typed,
                          target: static SymexTarget,
                          settings: static SymexSettings
                         ): untyped =
  ## Load previously-persisted witnesses for *exactly* this
  ## SUT/target/settings/Z3/Nim/walker combination, each with its
  ## stored `Soundness` (`seq[CachedWitness]`, RFC-0005 S11).
  ## Mismatched key → empty seq.
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  let parsed = parseEntryImpl(fn, "loadSymexWitnesses",
                               settings.budget.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      loadSymexWitnessesImpl(`db`, prog, `targetExpr`, `settings`, dbErrors)

# ---- Verdict macro forms (Phase 13 cycle 10) -------------------------------
#
# Mirror `saveSymexWitness` / `loadSymexWitnesses` for non-SAT
# verdicts. `status: SymexFindingStatus` is a runtime value, not
# static — the suffix (`:unsat` vs `:unk`) is dispatched at
# runtime inside `saveSymexVerdictImpl`. Error accumulation is
# internal and discarded (the user-facing macro doesn't carry a
# Report); callers wanting error reporting use the `*Impl` procs
# directly with their own `errors` seq.

macro saveSymexVerdict*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings,
                        status: SymexFindingStatus,
                        soundness: Soundness): untyped =
  ## Persist a non-SAT verdict (sfUnsat / sfUnknown) for `fn`'s
  ## content-addressed key, with the `soundness` it was decided under
  ## (RFC-0005 S11). No-op for sfSat (use `saveSymexWitness`) and
  ## sfNotApplicable.
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  let parsed = parseEntryImpl(fn, "saveSymexVerdict",
                               settings.budget.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      saveSymexVerdictImpl(`db`, prog, `targetExpr`, `settings`,
                            `status`, `soundness`, dbErrors)

macro loadSymexVerdict*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings
                       ): untyped =
  ## Load a previously-persisted non-SAT verdict for `fn`'s
  ## content-addressed key. Checks `:unsat` then `:unk`
  ## (UNSAT-first load-order tie-break). Returns
  ## `Option[CachedVerdict]`: the status and its stored `Soundness`
  ## (RFC-0005 S11).
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  let parsed = parseEntryImpl(fn, "loadSymexVerdict",
                               settings.budget.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      loadSymexVerdictImpl(`db`, prog, `targetExpr`, `settings`, dbErrors)

# ---- Layer 1 — symexFindAllWitnesses ---------------------------------------
#
# Phase 12 cycle 7. The Layer-1 primitive: given a SUT and an
# `ExampleDatabase`, run symex against every auto-discovered target
# in the SUT's IR and return one `SymexFinding` per. Each finding
# is also deposited via `recordSymexFinding` so the engine's
# `finalizePhase` later drains them into `Report.symexFindings`.
#
# Cycle 7 covers `tLabel` only — `symexTarget("name")` markers
# extracted via `irCollectLabels` (cycle 4) walking transitively
# through `parseProc`'s callee table. Cycles 8-10 add the three
# auto-included defect targets. Cycle 11 adds `excludeTargets`.
# Cycle 12 wires the DB cache.

macro symexFindAllWitnesses*(fn: typed,
                              db: ExampleDatabase,
                              symexSettings: static SymexSettings =
                                defaultSymexSettings(),
                              # Constructor-form list of targets to suppress
                              # from auto-discovery. Comparison is by
                              # `SymexTargetKind` (label-by-name suppression
                              # is out of scope). Not `static` because Nim 2.2
                              # rejects every viable default expression for a
                              # `static seq[T]` parameter; instead the macro
                              # inspects the call-site AST directly via the
                              # NimNode it receives.
                              excludeTargets: seq[SymexTarget] = @[]
                             ): seq[SymexFinding] =
  ## Run symex against every auto-discovered target in `fn`. Returns
  ## one `SymexFinding` per target, in IR-traversal order; each
  ## finding is also recorded into the per-thread sink so it flows
  ## into `Report.symexFindings` at end-of-run.
  # Phase 14 A7b: the Phase-12 `var T` guard is lifted. Witness
  # semantics: the walker reports the INITIAL value of each `var`
  # param (via `initialEnv`), which the test runtime invokes the
  # SUT with. Mutations are walker-internal symbolic operations
  # with no caller-side identity tracking.
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  # RFC-0010 review round 2: via `parseEntryImplWarned`, so an
  # incoherent `symexSettings` warns here — and, transitively, for
  # `symexForAll`, which emits a call to this macro rather than routing
  # through `symexFind`/`assertCoveredBy` (its own settings never touched
  # `warnIncoherentSettings` before this).
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  let pre = methodPrelude(fn)
  if pre != nil:
    return newTree(nnkStmtListExpr, pre, newCall(bindSym"symexFindAllWitnesses",
      fn, db, newLit(symexSettings), excludeTargets))
  let parsed = parseEntryImplWarned(fn, "symexFindAllWitnesses", symexSettings)

  let labels = irCollectLabels(parsed.body, parsed.procs)

  # Macro-time filter set: any target kind appearing in
  # `excludeTargets` is dropped, regardless of `label` (per plan:
  # comparison is by kind). Label-by-name suppression is
  # out-of-scope for v1 — the deferrals table tracks it.
  # `excludeTargets` is a NimNode at macro time (the call-site
  # expression). The user writes one of:
  #   * `@[tIndexError(), tLabel("x")]`   — nnkPrefix("@", nnkBracket(...))
  #   * the default `@[]`                  — empty bracket
  # We inspect the AST and translate each constructor call to the
  # corresponding `SymexTargetKind`. Comparison is by kind per the
  # plan: any call to `tIndexError` excludes ALL tIndexError
  # auto-discoveries; any call to `tLabel(...)` excludes ALL labels
  # regardless of name. Label-by-name suppression is a documented
  # deferral.
  # Phase 14 B67: `tLabel("name")` excludes ONLY the named label
  # (previously excluded ALL labels regardless of name).
  # `tAssertionViolation/tIndexError/tFieldDefect` continue to
  # exclude by kind. This is a documented breaking change for
  # users who relied on `tLabel(...)` to mean "all labels."
  var excludedKinds: set[SymexTargetKind]
  var excludedLabels: seq[string]
  proc collectKinds(n: NimNode) =
    case n.kind
    of nnkPrefix:
      if n.len == 2: collectKinds(n[1])
    of nnkBracket:
      for child in n: collectKinds(child)
    of nnkCall, nnkCommand:
      if n.len >= 1 and n[0].kind in {nnkIdent, nnkSym}:
        case n[0].strVal
        of "tLabel":
          if n.len >= 2 and n[1].kind in {nnkStrLit..nnkTripleStrLit}:
            excludedLabels.add n[1].strVal
        of "tAssertionViolation": excludedKinds.incl stkAssertionViolation
        of "tIndexError":         excludedKinds.incl stkIndexError
        of "tFieldDefect":        excludedKinds.incl stkFieldDefect
        of "tRaisedExn":          excludedKinds.incl stkRaisedExn
        else: discard
    else: discard
  collectKinds(excludeTargets)

  # Build the witness-renderer for this proc's parameter tuple
  # exactly as `symexFind` does — the witness reconstruction must
  # produce a typed Nim value so `renderAsChoices` can serialise it
  # into the choice IR for the example DB and report.
  let witId = genSym(nskLet, "rawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(parsed.params, witId)

  let bodyExpr   = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode
  let procsExpr  = parsed.procsNimNode
  let rtExpr     = parsed.retTyNimNode   ## RFC-0005 S8p
  let peExpr     = parsed.parseErrorsNimNode   ## Phase 15 G1c
  let avExpr     = parsed.annotationViolationsNimNode  ## RFC-0005 S8

  # Compile-time list of target constructors. We materialise them
  # at runtime as a `seq[SymexTarget]` so the runtime loop is a
  # single straight-line walk regardless of label count.
  # Build the runtime target list as a typed `newSeq[SymexTarget]()`
  # plus per-target `.add` calls. Avoids the "cannot infer element
  # type" trap when the SUT exposes zero targets — that case
  # (which cycle 18 promotes to `sfNotApplicable`) still needs to
  # compile cleanly.
  let tsId = genSym(nskVar, "targets")
  var targetsBuild = newStmtList()
  targetsBuild.add quote do:
    var `tsId` = newSeq[SymexTarget]()
  var nTargets = 0
  # Phase 14 B67: per-label exclusion.
  for lbl in labels:
    if lbl in excludedLabels: continue
    let call = newCall(bindSym"tLabel", newLit(lbl))
    targetsBuild.add newCall(bindSym"add", tsId, call)
    inc nTargets
  if stkAssertionViolation notin excludedKinds and
     irHasAssert(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tAssertionViolation"))
    inc nTargets
  if stkIndexError notin excludedKinds and
     irHasIndex(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tIndexError"))
    inc nTargets
  if stkFieldDefect notin excludedKinds and
     irHasVariantField(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tFieldDefect"))
    inc nTargets
  # Phase 15 E6. A raw `assert cond, msg` lowers to an implicit
  # `AssertionDefect` raise; auto-discover it as a `tRaisedExn("AssertionDefect")`
  # target so the reachable defect surfaces in `Report.symexFindings`.
  if stkRaisedExn notin excludedKinds and
     irHasAssertDefect(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tRaisedExn", newLit("AssertionDefect")))
    inc nTargets

  # Zero-targets fallback: the SUT has no symex-relevant constructs
  # (no markers, no asserts, no indexing, no variant arm-field
  # reads) — or `excludeTargets` ruled them all out. Skip Z3
  # entirely; deposit one `sfNotApplicable` audit entry so the
  # eventual Report still carries an honest "we looked, there was
  # nothing to look at" record. The runtime loop falls through
  # cleanly because `tsId` is empty.
  # Zero-targets fallback assembled at macro time: when nothing
  # was discovered (after `excludeTargets` filtering), the macro
  # emits a single `sfNotApplicable` deposit and skips the entire
  # `runSymex` loop — Z3 isn't called, the per-target cache isn't
  # touched. Otherwise the emitted body iterates `tsId` and runs
  # cache-then-symex per target.
  # gensym shared between the outer prog-binding quote and the
  # inner runtime body so they refer to the same NimNode (each
  # `quote do:` mints its own hygienic identifiers otherwise).
  let progId     = genSym(nskLet, "prog")
  let findingsId = genSym(nskVar, "findings")
  let dbErrorsId = genSym(nskVar, "dbErrors")
  let loopTarget = genSym(nskForVar, "t")  ## the runtime loop variable below
  let runReplayed = emitRunSymexReplayed(fn, parsed.params, progId,
                                         loopTarget, newLit(symexSettings),
                                         symexSettings.replay)
  let gapsSym = bindSym"findingGaps"   ## RFC-0005 S11 (private helper)
  let runtimeBody =
    if nTargets == 0:
      quote do:
        let noTargetsFinding = SymexFinding(
          targetDesc: "no-targets-discovered",
          status:     sfNotApplicable,
          covered:    false,
          z3Version:  z3FullVersion())
        recordSymexFinding(noTargetsFinding)
        `findingsId`.add noTargetsFinding
    else:
      quote do:
        for `loopTarget` in `tsId`:
          var f = SymexFinding(
            targetDesc: describeTarget(`loopTarget`),
            covered:    false,
            z3Version:  z3FullVersion(),
            fromCache:  false,
            # RFC-0005 S11: parse-time facts, so a cache hit has them too.
            annotationViolations: `progId`.annotationViolations)
          # Phase 13 cycle 7. Three-level cascade:
          #   1. SAT cache hit → load witness, fromCache=true.
          #   2. Verdict cache hit → load sfUnsat/sfUnknown,
          #      fromCache=true.
          #   3. Cold path → runSymex; save witness or verdict.
          # `recordSymexFinding(f)` stays outside the if-else tree
          # so EVERY path deposits — invariant pinned by cycle 7's
          # `consumeSymexFindings()` assertion.
          let cached = loadSymexWitnessesImpl(`db`, `progId`, `loopTarget`,
                                              `symexSettings`, `dbErrorsId`)
          if cached.len > 0:
            f.status = sfSat
            f.witnessChoices = cached[0].choices
            f.soundness = cached[0].soundness   ## RFC-0005 S11: served unchanged
            f.fromCache = true
          else:
            let cachedVerdict = loadSymexVerdictImpl(`db`, `progId`, `loopTarget`,
                                                     `symexSettings`,
                                                     `dbErrorsId`)
            let cachedRaised = loadSymexRaisedImpl(`db`, `progId`, `loopTarget`,
                                                   `symexSettings`,
                                                   `dbErrorsId`)
            if cachedVerdict.isSome:
              f.status = cachedVerdict.get.status
              f.soundness = cachedVerdict.get.soundness   ## RFC-0005 S11
              f.fromCache = true
            elif cachedRaised.len > 0:
              # Phase 15 E2a (STRUCTURAL). A reachable raise was persisted for
              # this target; serve it from cache without Z3. (E2b carries the
              # witness; E2a has none, so only the status is reloaded here.)
              f.status = sfRaised
              f.soundness = cachedRaised[0].soundness   ## RFC-0005 S11
              f.fromCache = true
            else:
              # RFC-0005 S10: run + rule-3 replay settle; persisted below
              # only AFTER the settle (replay precedes persist, §7).
              let raw = `runReplayed`
              f.status = toFindingStatus(raw.status)
              # RFC-0005 S11: the settled soundness (persisted below with the
              # verdict) and the per-cause view of this run.
              f.soundness = raw.soundness
              f.gaps = `gapsSym`(raw.errors)
              case raw.status
              of sxSat:
                let `witId` {.used.} = raw.witness
                let typedWit: `tupleTy` = `witnessTup`
                f.witnessChoices = renderAsChoices(typedWit)
                saveSymexWitnessImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                      f, `dbErrorsId`)
              of sxUnsat, sxUnknown:
                saveSymexVerdictImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                      f.status, f.soundness, `dbErrorsId`)
              of sxRaised:
                # Phase 16 D1a. The defect fork is now unconditional;
                # `routeRaise` populates `raisedWitness`. Carry it as
                # `witnessChoices` so callers can replay the input.
                # Use a DISTINCT `targetDesc` ("raised(<TypeId>)") so
                # sfSat filter loops in tests don't double-match on the
                # same base descriptor.
                let `witId` {.used.} = raw.raisedWitness
                let typedRaisedWit: `tupleTy` = `witnessTup`
                f.witnessChoices = renderAsChoices(typedRaisedWit)
                f.targetDesc = "raised(" & raw.raisedTypeId & ")"
                # Phase 15 E6. Carry the defect type id onto the finding for
                # display when the raised type is a `Defect` subtype.
                if raw.isDefect:
                  f.defectTypeId = raw.raisedTypeId
                saveSymexRaisedImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                    @[raw], `dbErrorsId`)
          recordSymexFinding(f)
          `findingsId`.add f

  result = quote do:
    block:
      let `progId` {.used.} = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`, retTy: `rtExpr`,
                              parseErrors: `peExpr`,
                              annotationViolations: `avExpr`)
      `targetsBuild`
      var `findingsId`: seq[SymexFinding] = @[]
      var `dbErrorsId` {.used.}: seq[string] = @[]
        # Phase 13 cycle 3 — accumulator for DB save/load failures.
        # Phase 14 cycle C2: drained into `engineSymexDbErrors`
        # thread-local sink so `finalizePhase` can append into
        # `Report.dbErrors` at end-of-run.
      `runtimeBody`
      # Phase 14 C2: deposit accumulated DB errors into the
      # engine-side thread-local sink. `recordSymexDbError` is a
      # tiny append; safe to call from any phase.
      for dbErr in `dbErrorsId`:
        recordSymexDbError(dbErr)
      `findingsId`

# =============================================================================
# RFC-0005 S8ah -- build-time wiring of the compile-time VM let-aliasing
# guard (`smt/vm_alias_guard.nim`) onto the REAL symex compile path, opt-in
# behind `-d:nelliVmAliasAudit` so an ordinary `import nelli/symex` compile
# (every user who is not running this repo's own CI) pays nothing: the
# `when defined` condition is false, so this whole block -- including the
# `import` itself -- is never semantically checked, only parsed as a
# skipped statement. Measured (S8ah's own note in the RFC): with the define
# OFF, compiling `tests/tsymex_phase15_F8_smoke.nim` (a small, representative
# symex test) shows no measurable difference against the pre-S8ah baseline;
# with it ON, the guard's own reflection walk adds a few seconds (the same
# order of cost `tsymex_rfc0005_s8ab_letaudit.nim` itself already pays every
# `nimble test`/`dt-bounded.sh` run) -- acceptable for CI, not for every
# user's build, hence opt-in rather than unconditional.
#
# `vm_alias_guard.nim` audits the OTHER 15 files in scope (14 directly via
# `{.all.}}` imports, plus itself covers none of symex.nim -- see its own
# header for why `concolic.nim` is ALSO excluded there, to avoid an import
# cycle). This block covers the 16th: symex.nim's OWN top-level routines,
# self-audited (no `{.all.}}` import needed to reflect on your own module).
when defined(nelliVmAliasAudit):
  import ./smt/vm_alias_guard

  const symexSelfNames = extractTopLevelNames(currentSourcePath())
  vmGuardAuditNames(symexSelfNames, "symex.nim")

  const symexSelfLetHits = block:
    var dedup: seq[string]
    for h in vmGuardLetHits:
      if h.startsWith("symex.nim:") and h notin dedup: dedup.add h
    dedup

  const symexSelfParamHits = block:
    var dedup: seq[string]
    for h in vmGuardParamHits:
      if h.startsWith("symex.nim:") and h notin dedup: dedup.add h
    dedup

  const symexSelfReachHits = block:
    var dedup: seq[string]
    for h in vmGuardReachHits:
      if h.startsWith("symex.nim:") and h notin dedup: dedup.add h
    dedup

  # The one historical hazard S8x/S8ab/S8af already reviewed and allowlisted
  # in symex.nim's own scope: `emitTyAndReaderShared`'s nested
  # `emitMVBranch`, reading a `VariantAxis`/`VariantArm` element with
  # nothing written while the binding is live (the `types.nim:==` twin of
  # this same finding is allowlisted in `vm_alias_guard.nim`'s own block).
  const symexSelfLetAllowlist = [
    "symex.nim:emitTyAndReaderShared: let ax : VariantAxis (ntyObject) <- ty.mvAxes[axisIdx]",
    "symex.nim:emitTyAndReaderShared: let elseArm : VariantArm (ntyObject) <- ax.arms[elseArmIx]",
  ]

  # RFC-0005 S8ah: symex.nim's own macros (`symexFindAllWitnesses`) call
  # `traceOneCallBoundary[seq[NimNode]]` directly (unquoted) -- but forcing
  # that instantiation for audit needs `{.all.}}` visibility into
  # `dsl_parser.nim`'s private symbol, which symex.nim does not have (and
  # should not need just to self-audit). `vm_alias_guard.nim`'s own
  # 14-file self-audit already forces and audits that exact instantiation
  # as a side effect of the `import` above (module-level code runs once,
  # at import time) and records it in the GLOBAL `vmGuardForcedGenerics`
  # list -- the completeness check below reads THAT, not a local
  # symex.nim-only copy, so it sees the forcing regardless of which module
  # performed it.
  static:
    doAssert vmGuardWalkErrs.len == 0,
      "symex.nim self-audit: getImpl/audit-machinery error:\n" & vmGuardWalkErrs.join("\n")
    var unexpectedLets: seq[string]
    for h in symexSelfLetHits:
      if h notin symexSelfLetAllowlist: unexpectedLets.add h
    doAssert unexpectedLets.len == 0,
      "symex.nim self-audit: unallowlisted compile-time VM let-aliasing " &
      "hazard (RFC-0005 S8ab/S8x) -- fix it or add a reviewed allowlist " &
      "entry with a justification:\n" & unexpectedLets.join("\n")
    doAssert symexSelfParamHits.len == 0,
      "symex.nim self-audit: unallowlisted compile-time VM param-aliasing " &
      "hazard:\n" & symexSelfParamHits.join("\n")
    var reachableGenerics: seq[string]
    for h in symexSelfReachHits:
      let genericKey = h.split(" -> ")[^1]
      if genericKey notin reachableGenerics: reachableGenerics.add genericKey
    var unforced: seq[string]
    for g in reachableGenerics:
      if g notin vmGuardForcedGenerics: unforced.add g
    doAssert unforced.len == 0,
      "symex.nim self-audit: a macro directly (unquoted) calls a generic " &
      "with no forced-instantiation audit (RFC-0005 S8ah item 1/3):\n" &
      unforced.join("\n")

