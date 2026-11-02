## RFC-0005 (soundness channels) slice S8az -- S8av's own remainder (its
## "Different mechanisms, reported and not fixed here" note). S8av widened
## only the `:unsat`/`:unk` verdict cache slot (`CachedVerdict`) to carry
## `gaps()`; the `:sat` witness slot and each `:raised:<type>` sentinel still
## returned `gaps: @[]` on a hit. S8az widens both, through the SAME
## `gapsMeta`/`storedGaps` encode/decode pair `CachedVerdict` already uses --
## no copy, one shared helper for all three slots.
##
##   (1) `CachedWitness` (the `:sat` cache value) gained a `gaps` field;
##       `saveSymexWitnessImpl` persists `finding.gaps` alongside
##       `finding.soundness`, `loadSymexWitnessesImpl` serves it back.
##   (2) `CachedRaised` (a new named tuple: `RawResult` + `gaps`) is what
##       `loadSymexRaisedImpl` now returns, in place of a bare
##       `seq[RawResult]` -- `RawResult` itself stays Z3-free-boundary-
##       correct (no `FindingGap` field: that type lives one layer up, in
##       `engine/types.nim`, same reason `SymexFinding.gaps` is a
##       `seq[FindingGap]` and not raw `SymexErrorInfo`). `saveSymexRaisedImpl`
##       takes a parallel `gaps: seq[seq[FindingGap]]`, indexed exactly like
##       its existing `found: seq[RawResult]`.
##   (3) Both slots keep S8av's degrade-not-miss rule: an entry with
##       soundness metadata but no gaps metadata (pre-S8az, or a third-party
##       writer) is still a HIT, served with `gaps: @[]`.
## `symexWalkerVersion` 195 -> 199 (the cache VALUE widened again, same
## reasoning as S8av's own bump; see `canonicalize.nim`).
import std/[unittest, options, strutils, tables]
import nelli
import nelli/symex
import nelli/db
import nelli/smt/[types, dsl, runtime, canonicalize]
import nelli/engine/types

# =============================================================================
# (1) the :sat witness cache slot also serves gaps()
# =============================================================================

let s8azWitnessProg = SymexProgram(body: mkBlock(@[]))
let s8azWitnessTarget = tLabel("s8az_witness")

suite "RFC-0005 S8az (1) -- :sat witness cache hit also serves gaps()":
  test "saveSymexWitnessImpl/loadSymexWitnessesImpl round-trip non-empty gaps":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    let gaps = @[FindingGap(class: dcSubstituted, kind: "feOpaqueCallUnmodelled",
                            msg: "opaque call s8azSensor")]
    let finding = SymexFinding(status: sfSat, witnessChoices: @[],
                               soundness: Soundness(pathTaint: {scSpurious}),
                               gaps: gaps)
    saveSymexWitnessImpl(db, s8azWitnessProg, s8azWitnessTarget,
                         defaultSymexSettings(), finding, errors)
    check errors.len == 0
    let loaded = loadSymexWitnessesImpl(db, s8azWitnessProg, s8azWitnessTarget,
                                        defaultSymexSettings(), errors)
    check loaded.len == 1
    check loaded[0].soundness == finding.soundness
    check loaded[0].gaps == gaps

  test "a :sat entry saved with soundness but no gaps metadata (pre-S8az " &
       "shape) degrades to gaps: @[], not a miss":
    proc s8azPreFn(x: int) =
      if x == 42: symexTarget("s8az_pre_sat")
    let db = inMemoryDatabase()
    let key = symexCacheKeyForFn(s8azPreFn, tLabel("s8az_pre_sat"),
                                 defaultSymexSettings())
    # Hand-built: the exact shape `saveSymexWitnessImpl` wrote before S8az --
    # `"soundness"` metadata key present, no "gapsv"/"gapsn" keys at all.
    db.save(key & cacheKeySat, @[], {"soundness": "1:0:0:0"}.toTable, 64)
    let loaded = loadSymexWitnesses(db, s8azPreFn, tLabel("s8az_pre_sat"),
                                    defaultSymexSettings())
    check loaded.len == 1
    check loaded[0].gaps.len == 0
    check loaded[0].soundness == Soundness()

  test "end-to-end: a warm sfSat finding serves the same gaps as the cold one":
    proc s8azSatConfirm(a: bool; x: int) =
      ## `a < a` on a bool is modelled as a FRESH symbol (`dcFreshSymbol`), so
      ## the only path to the target is `scSpurious`-tainted and replay
      ## decides. Reality: `a < a` is false, so `not o` holds and the replay
      ## confirms -- a genuine `sfSat` whose run still carries the
      ## fresh-symbol decline in its `gaps()`.
      let o = a < a
      if not o:
        if x == 42:
          symexTarget("s8az_sat_confirm")
    let db = inMemoryDatabase()
    var cold, warm: SymexFinding
    for f in symexFindAllWitnesses(s8azSatConfirm, db):
      if f.targetDesc == "label(\"s8az_sat_confirm\")": cold = f
    check cold.status == sfSat
    check not cold.fromCache
    check cold.gaps.len > 0
    for f in symexFindAllWitnesses(s8azSatConfirm, db):
      if f.targetDesc == "label(\"s8az_sat_confirm\")": warm = f
    check warm.fromCache
    check warm.gaps == cold.gaps
    check warm.gaps.len > 0

# =============================================================================
# (2) the :raised:<type> cache slot also serves gaps()
# =============================================================================

let s8azRaisedProg = SymexProgram(body: mkBlock(@[]))
let s8azRaisedTarget = tAssertionViolation()

suite "RFC-0005 S8az (2) -- :raised:<type> cache hit also serves gaps()":
  test "saveSymexRaisedImpl/loadSymexRaisedImpl round-trip non-empty gaps":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    let gaps = @[FindingGap(class: dcFreshSymbol, kind: "feUnsupportedOpHavoc",
                            msg: "a < a modelled as a fresh symbol")]
    let found = @[RawResult(status: sxRaised, raisedTypeId: "ValueError",
                            soundness: Soundness(pathTaint: {scSpurious}))]
    saveSymexRaisedImpl(db, s8azRaisedProg, s8azRaisedTarget,
                        defaultSymexSettings(), found, errors, @[gaps])
    check errors.len == 0
    let loaded = loadSymexRaisedImpl(db, s8azRaisedProg, s8azRaisedTarget,
                                     defaultSymexSettings(), errors)
    check loaded.len == 1
    check loaded[0].raw.status == sxRaised
    check loaded[0].raw.raisedTypeId == "ValueError"
    check loaded[0].gaps == gaps

  test "a :raised:<type> entry saved with soundness but no gaps metadata " &
       "(pre-S8az shape) degrades to gaps: @[], not a miss":
    let db = inMemoryDatabase()
    let settings = defaultSymexSettings()
    var errors: seq[string] = @[]
    let found = @[RawResult(status: sxRaised, raisedTypeId: "IOError")]
    # A normal S8az-era save populates the (private-keyed) index entry AND a
    # gaps-carrying per-type sentinel.
    saveSymexRaisedImpl(db, s8azRaisedProg, s8azRaisedTarget, settings, found,
                        errors, @[@[FindingGap(class: dcFreshSymbol, kind: "x",
                                               msg: "y")]])
    check errors.len == 0
    # Overwrite ONLY the per-type sentinel with the exact pre-S8az shape --
    # soundness metadata, no gaps metadata at all. The index entry (whose key
    # is private to `symex.nim`) is left untouched, so the type id is still
    # enumerable.
    let baseKey = symexCacheKey(s8azRaisedProg, s8azRaisedTarget, settings,
      z3Version        = z3FullVersion(),
      nimVersion       = NimVersion,
      walkerVersion    = symexWalkerVersion,
      renderingVersion = renderAsChoicesVersion)
    db.save(baseKey & cacheKeyRaised("IOError"), @[],
            {"soundness": "1:0:0:0"}.toTable, verdictCacheMaxEntries)
    let loaded = loadSymexRaisedImpl(db, s8azRaisedProg, s8azRaisedTarget,
                                     settings, errors)
    check loaded.len == 1
    check loaded[0].raw.status == sxRaised
    check loaded[0].raw.raisedTypeId == "IOError"
    check loaded[0].gaps.len == 0

  test "end-to-end: a warm sfRaised finding serves the same gaps as the cold one":
    proc s8azRaisedConfirm(a: bool) =
      ## Mirrors `s8azSatConfirm`'s shape (and RFC-0005 S10's
      ## `s10AllAssertConfirm`): `a < a` is false for real, so the raw
      ## `assert o` fails on every input -- a genuine `sfRaised`
      ## (AssertionDefect) replay-confirmed off an `scSpurious`-tainted
      ## candidate, whose run still carries the fresh-symbol decline.
      let o = a < a
      assert o, "s8az raised"
    let db = inMemoryDatabase()
    var cold, warm: SymexFinding
    for f in symexFindAllWitnesses(s8azRaisedConfirm, db):
      if f.status == sfRaised: cold = f
    check cold.status == sfRaised
    check not cold.fromCache
    check cold.gaps.len > 0
    for f in symexFindAllWitnesses(s8azRaisedConfirm, db):
      if f.status == sfRaised: warm = f
    check warm.fromCache
    check warm.gaps == cold.gaps
    check warm.gaps.len > 0

# =============================================================================
suite "RFC-0005 S8az walker version":
  test "symexWalkerVersion is at least S8az's":
    check parseInt(symexWalkerVersion) >= 199
