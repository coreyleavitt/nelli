## RFC-fuzzer-nextgen S6: learned-state checkpoint/resume.
##
## `fuzz`'s contract is open-ended and wall-clock-scheduled, so routine
## interruption (Ctrl-C, OOM-kill, a CI timeout, E-cleanup's own crash-
## recovery) and restart is the normal case, not an edge case. The
## *corpus* survives a restart via `ExampleDatabase`'s `corpus` section
## (F1/E3b), but the SCHEDULING state built on top of it —
## S1 rarity/energy (`FrontierStats`, `nelli/coverage`), S2 bandit weights
## (`OperatorBandit`, `nelli/bandit`), and G5's harvested `Dictionary`
## (`nelli/fuzzir`) — is in-memory `fuzz[T]`-loop state that silently
## cold-starts every restart, discarding hours of schedule learning on
## exactly the long-running workload the `fuzz` contract exists for.
##
## `LearnedState` is that small, cheaply-serialized snapshot. `fuzz.nim`'s
## loop persists one periodically (`FuzzSettings.checkpointCadence`) and
## reloads a compatible one at campaign start — see that module for the
## wiring; this module is pure encode/decode, no I/O.
##
## **Scoped OUT (stated limitation, not silent): S4's favored-set is not
## persisted.** It is a pure function of `FrontierStats` + the live corpus
## (`favoredIndices`, fuzz.nim) — both of which already survive a restart
## through this module and the DB's `corpus` section respectively — so a
## resumed campaign simply RE-DERIVES it at its own next cull tick rather
## than needing it as a persisted artifact. Persisting a snapshot of WHICH
## corpus INDICES were favored would be meaningless anyway: a resumed
## campaign reloads the corpus in `loadCorpus`'s order/composition, not the
## prior run's live in-memory `corpus` seq, so index-based favored-set
## state from a previous run wouldn't even apply to the reloaded one.
##
## **Versioned header, ignore-on-mismatch** (mirrors E0/E3b's corpus-format
## discipline, `nelli/db`): magic + u16 `learnedStateVersion`. A version
## mismatch (a rebuilt binary with a changed `LearnedState` layout) or any
## corrupt/truncated bytes makes `decodeLearnedState` report `ok: false` —
## the caller cold-starts, exactly as if no checkpoint existed. This NEVER
## raises and NEVER misreads: unlike the corpus (authoritative data, with
## its own stricter refuse-on-newer versioning), a checkpoint is a pure
## performance cache the fuzz loop is always correct to discard.
##
## **How corruption realistically arises.** `db.nim`'s `saveSchedImpl` writes
## via a tmp-file-then-rename, which gives atomic VISIBILITY: a reader never
## observes a partially-written file, so an ordinary Ctrl-C, OOM-kill, or CI
## timeout during a checkpoint write can NOT produce a corrupt/truncated
## blob — the rename either lands the old file or the new one, never a
## half-written mix. The realistic sources of a corrupt blob are storage-
## layer bit rot, a crash before the renamed file's data blocks are
## actually flushed to disk (there is no fsync here), a version skew
## between two `nelli` builds sharing a checkpoint directory, or direct
## file tampering. `decodeLearnedState` defends against all of these
## uniformly, including the case where two independently length-prefixed,
## PAIRED arrays (frontier hit-counts/last-improved-seq, bandit pulls/
## reward-sums) each individually pass their own bounds check but disagree
## with each other — every consumer of this state (`nelli/coverage`,
## `nelli/bandit`) assumes its paired seqs are the same length and indexes
## accordingly, so that disagreement must be caught here, at the one place
## that can still refuse the whole blob instead of raising past a caller
## that has no such recourse.

import ./coverage, ./bandit, ./fuzzir, ./binaryio

type
  LearnedState* = object
    ## The persisted snapshot. Every field is `FrontierStats`/
    ## `OperatorBandit`/`Dictionary`'s own persisted state, flattened —
    ## see each field's owning module for what it means.
    frontierHitCounts*: seq[int]
    frontierLastImprovedSeq*: seq[int]
    frontierTotalAdmitted*: int
    frontierLastGlobalImprovedSeq*: int
      ## G3's staleness counter — lives on the SAME `FrontierStats` object
      ## S1 owns (coverage.nim's extensibility contract), so it is
      ## persisted alongside S1's own fields rather than split out: a
      ## resumed campaign that restores rarity/energy but not staleness
      ## would otherwise read as permanently "just improved" on resume,
      ## which could wrongly suppress G3's stall-triggered concolic bridge
      ## for a campaign that was in fact long stalled pre-restart.
    banditPulls*: seq[float]
    banditRewardSum*: seq[float]
    banditTotalPulls*: float
    dictionary*: Dictionary

const
  learnedStateMagic = "NLS0"
  learnedStateVersion* = 1'u16
    ## Bump on ANY layout change to this type's encoding. A checkpoint
    ## written by a different version is never partially trusted — see the
    ## module doc's ignore-on-mismatch rule.

proc newLearnedState*(stats: FrontierStats; bandit: OperatorBandit;
                      dict: Dictionary): LearnedState =
  ## Snapshot the three learned-state sources into one persistable value.
  let fs = frontierStatsSnapshot(stats)
  let bs = banditSnapshot(bandit)
  LearnedState(frontierHitCounts: fs.hitCounts,
              frontierLastImprovedSeq: fs.lastImprovedSeq,
              frontierTotalAdmitted: fs.totalAdmitted,
              frontierLastGlobalImprovedSeq: fs.lastGlobalImprovedSeq,
              banditPulls: bs.pulls, banditRewardSum: bs.rewardSum,
              banditTotalPulls: bs.totalPulls, dictionary: dict)

proc encodeLearnedState*(s: LearnedState): seq[byte] =
  ## Fixed little-endian encoding via `binaryio`'s primitives (the same
  ## codec layer `nelli/serialize` and `nelli/db` use) — magic + version
  ## header, then each field length-prefixed.
  for c in learnedStateMagic: result.add byte(c)
  result.putU16(learnedStateVersion)
  result.putU64(uint64(s.frontierHitCounts.len))
  for h in s.frontierHitCounts: result.putI64(int64(h))
  result.putU64(uint64(s.frontierLastImprovedSeq.len))
  for x in s.frontierLastImprovedSeq: result.putI64(int64(x))
  result.putI64(int64(s.frontierTotalAdmitted))
  result.putI64(int64(s.frontierLastGlobalImprovedSeq))
  result.putU64(uint64(s.banditPulls.len))
  for p in s.banditPulls: result.putF64(p)
  result.putU64(uint64(s.banditRewardSum.len))
  for r in s.banditRewardSum: result.putF64(r)
  result.putF64(s.banditTotalPulls)
  let dictEntries = dictionarySnapshot(s.dictionary)
  result.putU64(uint64(dictEntries.len))
  for e in dictEntries:
    result.putU8(uint8(ord(e.kind)))
    case e.kind
    of dvInt:    result.putInt128(e.intVal)
    of dvBytes:  result.putRawBytes(e.bytesVal)
    of dvString: result.putRawStr(e.strVal)

proc readBoundedCount(data: openArray[byte], pos: var int, elemSize: int): int =
  ## Shared length-prefix guard (mirrors `db.nim`'s `getIntervals`/
  ## `parseContents` pattern): a corrupt/hostile count can never drive an
  ## allocation or loop bound larger than what `data` could possibly hold.
  let raw = getU64(data, pos)
  let bytesLeft = uint64(data.len - pos)
  if elemSize > 0 and raw > bytesLeft div uint64(elemSize):
    raise newException(DbCorrupt, "learned-state count " & $raw & " exceeds buffer capacity")
  if raw > uint64(high(int)):
    raise newException(DbCorrupt, "learned-state count exceeds int range")
  int(raw)

proc decodeLearnedState*(data: seq[byte]): tuple[ok: bool, state: LearnedState] =
  ## Inverse of `encodeLearnedState`. NEVER raises: bad magic, an
  ## unsupported version, any truncated/corrupt field, OR a pair of
  ## sibling arrays that individually pass their own bounds check but
  ## disagree in length with each other, decodes to `(ok: false, state:
  ## <zero value>)` — the "ignore the checkpoint and cold-start" rule the
  ## module doc names. `data` shorter than the fixed 6-byte header is the
  ## same as a bad magic (also `ok: false`).
  ##
  ## **Pairing invariants enforced** (every set of fields `encodeLearnedState`
  ## always writes from a common-length source seq, so a mismatch can only
  ## mean a corrupt/tampered/skewed blob, never a legitimately-produced
  ## one): `frontierHitCounts.len == frontierLastImprovedSeq.len` (both
  ## indexed by coverage slot in `coverage.admit`) and `banditPulls.len ==
  ## banditRewardSum.len` (both indexed by arm in `bandit.chooseOperator`/
  ## `credit`). `dictionary.entries` carries no sibling array to disagree
  ## with — each entry is self-describing (kind byte + its own payload) —
  ## so it has no pairing invariant to check here.
  if data.len < 6: return (false, LearnedState())
  for i, c in learnedStateMagic:
    if data[i] != byte(c): return (false, LearnedState())
  var pos = 4
  let ver = getU16(data, pos)
  if ver != learnedStateVersion: return (false, LearnedState())
  try:
    var s: LearnedState
    let nHit = readBoundedCount(data, pos, 8)
    for _ in 0 ..< nHit: s.frontierHitCounts.add int(getI64(data, pos))
    let nLast = readBoundedCount(data, pos, 8)
    if nLast != nHit:
      raise newException(DbCorrupt,
        "learned-state: frontierHitCounts/frontierLastImprovedSeq length mismatch (" &
        $nHit & " vs " & $nLast & ")")
    for _ in 0 ..< nLast: s.frontierLastImprovedSeq.add int(getI64(data, pos))
    s.frontierTotalAdmitted = int(getI64(data, pos))
    s.frontierLastGlobalImprovedSeq = int(getI64(data, pos))
    let nPulls = readBoundedCount(data, pos, 8)
    for _ in 0 ..< nPulls: s.banditPulls.add getF64(data, pos)
    let nRewards = readBoundedCount(data, pos, 8)
    if nRewards != nPulls:
      raise newException(DbCorrupt,
        "learned-state: banditPulls/banditRewardSum length mismatch (" &
        $nPulls & " vs " & $nRewards & ")")
    for _ in 0 ..< nRewards: s.banditRewardSum.add getF64(data, pos)
    s.banditTotalPulls = getF64(data, pos)
    let nDict = readBoundedCount(data, pos, 1)   # min entry size is 1 (kind byte)
    var dictEntries: seq[DictEntry]
    for _ in 0 ..< nDict:
      let kindByte = getU8(data, pos)
      if kindByte > uint8(ord(high(DictValueKind))):
        raise newException(DbCorrupt, "learned-state: invalid dict entry kind " & $kindByte)
      case DictValueKind(kindByte)
      of dvInt:    dictEntries.add DictEntry(kind: dvInt, intVal: getInt128(data, pos))
      of dvBytes:  dictEntries.add DictEntry(kind: dvBytes, bytesVal: getRawBytes(data, pos))
      of dvString: dictEntries.add DictEntry(kind: dvString, strVal: getRawStr(data, pos))
    s.dictionary = restoreDictionary(dictEntries)
    (true, s)
  except DbCorrupt, IndexDefect, RangeDefect, ValueError:
    (false, LearnedState())
