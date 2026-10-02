## RFC-0005 (soundness channels) slice S8av -- S8am's and S11's remainder
## (§8.1's and S8am's own "Different mechanisms, reported and not fixed
## here" lists). Four independent items:
##
##   (1) The public cache macros (`saveSymexWitness`, `loadSymexWitnesses`,
##       `saveSymexVerdict`, `loadSymexVerdict`) collected `dbErrors` into a
##       block-local `{.used.}` variable and discarded it. Now routed into
##       `recordSymexDbError`/`consumeSymexDbErrors` -- the same thread-local
##       sink `symexFindAllWitnesses` already drains into `Report.dbErrors`.
##   (2) `db.nim`'s F6 (`save(..., meta)`/`loadPrimaryWithMeta`), targeted-PBT
##       secondary, F1 corpus and scheduler-checkpoint wrappers called their
##       OPTIONAL closure unconditionally -- a hand-built `ExampleDatabase`
##       (the partial-object-literal idiom already used elsewhere in this
##       repo, e.g. `tests/tsymex_phase13_verdict_primitives.nim` and
##       `tests/tfuzzcorpus_nilguard.nim`) leaving one of those closures nil
##       SIGSEGV'd the instant the wrapper was called, rather than raising
##       the module's own documented `DbError`.
##   (3) A served `sfUnknown`/`sfUnsat` verdict cache hit always reported
##       `gaps: @[]`, even when the cold run that produced it had a
##       non-empty per-cause view -- only `Soundness` rode the cache entry's
##       metadata. `CachedVerdict` now also carries `gaps`
##       (`gapsMeta`/`storedGaps`, `symexWalkerVersion` 190 -> 195); an entry
##       saved before S8av (soundness present, no gaps metadata) degrades to
##       `gaps: @[]` rather than becoming a miss.
##   (4) S8am's "raise-irrelevant-parameter witness sentinel" note
##       misdiagnosed a Phase 15 E6 characteristic as a witness-extraction
##       defect: `seqAsgnOrder.symexFind(tRaisedExn("ValueError"))`'s
##       reported witness is actually **IndexDefect's own** -- a reachable
##       `Defect` subtype always surfaces (`routeRaise`'s `wantsRaise`:
##       `raisedIsDefect` bypasses the caller's `stkRaisedExn` type filter),
##       and `shouldStop` halts the walk on ANY `sxRaised` before
##       `orderRaiser` (ValueError's own raise site) is ever reached. The
##       witness is fully relevant to IndexDefect and concretely replayable
##       -- there is no sentinel to fix. Proved here and in the corrected
##       comments of `tests/tsymex_rfc0005_s8am_remainder.nim`.
import std/[unittest, options, strutils, tables]
import nelli
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, runtime, canonicalize]
import nelli/engine/types

# =============================================================================
# (1) public cache macros route dbErrors to the caller, not discard them
# =============================================================================

proc s8avMacroFn(x: int) =
  if x == 42: symexTarget("s8av_macro")

proc brokenMetaDb(): ExampleDatabase =
  ## The base primary closures only -- NEITHER metadata-carrying closure is
  ## set, so `metaReady` (symex.nim) fails for every one of the four public
  ## cache macros, each appending its own "<impl proc>: ...
  ## saveWithMetaImpl/loadPrimaryWithMetaImpl..." message.
  result = ExampleDatabase(
    saveImpl: proc(testId: string, choices: seq[ChoiceNode],
                  maxEntries: int) = discard,
    loadPrimaryImpl: proc(testId: string): seq[seq[ChoiceNode]] = @[])

suite "RFC-0005 S8av (1) -- public cache macros route dbErrors, not discard":
  test "saveSymexWitness reports a metaReady failure via consumeSymexDbErrors":
    discard consumeSymexDbErrors()   # clear sink from any prior test
    let db = brokenMetaDb()
    let finding = SymexFinding(status: sfSat, witnessChoices: @[])
    saveSymexWitness(db, s8avMacroFn, tLabel("s8av_macro"),
                     defaultSymexSettings(), finding)
    let errs = consumeSymexDbErrors()
    check errs.len == 1
    check "saveSymexWitnessImpl" in errs[0]

  test "loadSymexWitnesses reports a metaReady failure via consumeSymexDbErrors":
    discard consumeSymexDbErrors()
    let db = brokenMetaDb()
    let witnesses = loadSymexWitnesses(db, s8avMacroFn, tLabel("s8av_macro"),
                                       defaultSymexSettings())
    check witnesses.len == 0
    let errs = consumeSymexDbErrors()
    check errs.len == 1
    check "loadSymexWitnessesImpl" in errs[0]

  test "saveSymexVerdict reports a metaReady failure via consumeSymexDbErrors":
    discard consumeSymexDbErrors()
    let db = brokenMetaDb()
    saveSymexVerdict(db, s8avMacroFn, tLabel("s8av_macro"),
                     defaultSymexSettings(), sfUnknown, Soundness())
    let errs = consumeSymexDbErrors()
    check errs.len == 1
    check "saveSymexVerdictImpl" in errs[0]

  test "loadSymexVerdict reports a metaReady failure via consumeSymexDbErrors":
    discard consumeSymexDbErrors()
    let db = brokenMetaDb()
    let got = loadSymexVerdict(db, s8avMacroFn, tLabel("s8av_macro"),
                               defaultSymexSettings())
    check got.isNone
    let errs = consumeSymexDbErrors()
    check errs.len == 1
    check "loadSymexVerdictImpl" in errs[0]

# =============================================================================
# (2) db.nim: optional closures raise DbError instead of SIGSEGV-ing
# =============================================================================

suite "RFC-0005 S8av (2) -- ExampleDatabase optional closures nil-check (F6 paths)":
  test "save(testId, choices, meta) raises DbError when saveWithMetaImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      db.save("t", @[], {"k": "v"}.toTable)

  test "loadPrimaryWithMeta raises DbError when loadPrimaryWithMetaImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      discard db.loadPrimaryWithMeta("t")

  test "saveSecondary raises DbError when saveSecondaryImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      db.saveSecondary("t", @[])

  test "loadSecondary raises DbError when loadSecondaryImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      discard db.loadSecondary("t")

  test "saveCorpus raises DbError when saveCorpusImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      db.saveCorpus("t", @[])

  test "loadCorpus raises DbError when loadCorpusImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      discard db.loadCorpus("t")

  test "saveSched raises DbError when saveSchedImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      db.saveSched("t", @[])

  test "loadSched raises DbError when loadSchedImpl is nil":
    let db = brokenMetaDb()
    expect(DbError):
      discard db.loadSched("t")

  test "a fully-wired backend (inMemoryDatabase) never raises on any of the above":
    let db = inMemoryDatabase()
    db.save("t", @[], {"k": "v"}.toTable)
    discard db.loadPrimaryWithMeta("t")
    db.saveSecondary("t", @[])
    discard db.loadSecondary("t")
    db.saveCorpus("t", @[])
    discard db.loadCorpus("t")
    db.saveSched("t", @[])
    discard db.loadSched("t")

# =============================================================================
# (3) a verdict cache hit also serves its stored gaps
# =============================================================================

let s8avVerdictProg = SymexProgram(body: mkBlock(@[]))
let s8avVerdictTarget = tLabel("s8av_verdict")

proc s8avPreFn(x: int) =
  if x == 42: symexTarget("s8av_pre")

proc s8avSensor(): int {.symexOpaque.} = 7
  ## Opaque and USED: `feOpaqueCallUnmodelled`, `dcSubstituted` -- a real
  ## SUT whose cold `sxUnknown` run carries a non-empty `gaps()` view.

proc s8avOpaque(x: int) =
  if s8avSensor() + x == 50:
    symexTarget("s8av_opaque")

suite "RFC-0005 S8av (3) -- verdict cache hit also serves gaps()":
  test "saveSymexVerdictImpl/loadSymexVerdictImpl round-trip non-empty gaps":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    let gaps = @[FindingGap(class: dcNoAnswer, kind: "beBudgetExhausted",
                            msg: "query ran out of rlimit")]
    saveSymexVerdictImpl(db, s8avVerdictProg, s8avVerdictTarget,
                         defaultSymexSettings(), sfUnknown, Soundness(),
                         errors, gaps)
    let loaded = loadSymexVerdictImpl(db, s8avVerdictProg, s8avVerdictTarget,
                                      defaultSymexSettings(), errors)
    check loaded.isSome
    check loaded.get.status == sfUnknown
    check loaded.get.gaps == gaps
    check errors.len == 0

  test "an entry saved with soundness but no gaps metadata (pre-S8av shape) " &
       "degrades to gaps: @[], not a miss":
    let db = inMemoryDatabase()
    let key = symexCacheKeyForFn(s8avPreFn, tLabel("s8av_pre"),
                                 defaultSymexSettings())
    # Hand-built: the exact shape `saveSymexVerdictImpl` wrote before S8av --
    # `"soundness"` metadata key present (`encodeSoundness`'s pinned
    # "1:0:0:0" for a default `Soundness()`), no "gapsv"/"gapsn" keys at all.
    db.save(key & cacheKeyUnknown, @[], {"soundness": "1:0:0:0"}.toTable,
           verdictCacheMaxEntries)
    let loaded = loadSymexVerdict(db, s8avPreFn, tLabel("s8av_pre"),
                                  defaultSymexSettings())
    check loaded.isSome
    check loaded.get.status == sfUnknown
    check loaded.get.gaps.len == 0
    check loaded.get.soundness == Soundness()

  test "end-to-end: a warm sfUnknown finding serves the same gaps as the cold one":
    let db = inMemoryDatabase()
    var cold, warm: SymexFinding
    for f in symexFindAllWitnesses(s8avOpaque, db):
      if f.targetDesc == "label(\"s8av_opaque\")": cold = f
    check cold.status == sfUnknown
    check not cold.fromCache
    check cold.gaps.len > 0
    var kinds: seq[string]
    for g in cold.gaps: kinds.add g.kind
    check "feOpaqueCallUnmodelled" in kinds
    for f in symexFindAllWitnesses(s8avOpaque, db):
      if f.targetDesc == "label(\"s8av_opaque\")": warm = f
    check warm.fromCache
    check warm.gaps == cold.gaps
    check warm.gaps.len > 0

# =============================================================================
# (4) the "raise-irrelevant-parameter witness sentinel" is not a sentinel: it
# is IndexDefect's own witness, misattributed by the E6 defect-pre-emption
# rule. Structurally identical to S8am's `seqAsgnOrder`/`orderRaiser`; see
# tests/tsymex_rfc0005_s8am_remainder.nim's corrected comments for the
# walker mechanism (`routeRaise`'s `wantsRaise` / `shouldStop`).
# =============================================================================

proc s8avRaiser(tag: string): int =
  raise newException(ValueError, "s8av_" & tag)

proc s8avSeqAsgn(i: int) =
  var s = @[1, 2, 3]
  s[i] = s8avRaiser("called")

suite "RFC-0005 S8av (4) -- raise-irrelevant-parameter witness is IndexDefect's own, concrete and replayable":
  test "searching for ValueError on an OOB-guarded seq write actually finds IndexDefect":
    let r = s8avSeqAsgn.symexFind(tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"

  test "the reported witness concretely replays the exact IndexDefect it claims":
    let r = s8avSeqAsgn.symexFind(tRaisedExn("ValueError"))
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
    let i = r.raisedWitness[0]
    check i notin 0 .. 2   # genuinely out of bounds -- not a don't-care sentinel
    var replayed = "none"
    try:
      s8avSeqAsgn(i)
    except IndexDefect:
      replayed = "IndexDefect"
    except ValueError:
      replayed = "ValueError"
    check replayed == "IndexDefect"

# =============================================================================
suite "RFC-0005 S8av walker version":
  test "symexWalkerVersion is at least S8av's":
    check parseInt(symexWalkerVersion) >= 195
