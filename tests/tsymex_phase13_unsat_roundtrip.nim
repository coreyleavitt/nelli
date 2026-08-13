## Phase 13 cycle 4 — UNSAT verdict round-trips through the
## content-addressed key, and bare-key entries are correctly
## invisible.
##
## Three regression pins:
## - (a) save/load symmetry under same (prog, target, settings).
## - (b) different prog → distinct H → load returns `none`.
##     Pins content-addressing at the verdict layer (the SAT-side
##     pin lives in `tsymex_phase7_assertcovered.nim:238`).
## - (c) a pre-RFC bare-key SAT entry (an old database from before
##     Phase 13) is invisible to `loadSymexWitnessesImpl`. Proves
##     the suffix migration is clean — the load doesn't fall back
##     to the bare key on miss.
import std/[unittest, options]
import nelli/symex
import nelli/db
import nelli/choice
import nelli/int128
import nelli/smt/[types, dsl, canonicalize]
import nelli/engine/types

let target = tLabel("verdict")

# Two distinct programs by IR body. Different bodies → different
# canonical encoding → different content-addressed hash.
let progA = SymexProgram(body: mkBlock(@[]))
let progB = SymexProgram(body: mkBlock(@[
  mkLet("x", tInt(64, true), mkIntLit(0))]))

suite "symex Phase 13 cycle 4 — UNSAT round-trip + migration":
  test "UNSAT save/load round-trip under same (prog, target, settings)":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, progA, target,
                         defaultSymexSettings(), sfUnsat, errors)
    let loaded = loadSymexVerdictImpl(db, progA, target,
                                       defaultSymexSettings(), errors)
    check loaded == some(sfUnsat)

  test "load under a different prog returns none (content-addressing)":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, progA, target,
                         defaultSymexSettings(), sfUnsat, errors)
    # progB differs from progA by body — different H, different key.
    let loaded = loadSymexVerdictImpl(db, progB, target,
                                       defaultSymexSettings(), errors)
    check loaded.isNone

  test "bare-key SAT entry from pre-RFC scheme is invisible after migration":
    # Simulate an old database where a SAT witness landed at the
    # bare key `"sx:" & H` (Phase 12's pre-RFC format). After Phase
    # 13's `:sat` suffix migration, the load must NOT find it —
    # otherwise stale entries would silently serve incorrect
    # results on upgrade.
    let db = inMemoryDatabase()
    let bareKey = symexCacheKey(progA, target, defaultSymexSettings(),
      z3Version        = z3FullVersion(),
      nimVersion       = NimVersion,
      walkerVersion    = symexWalkerVersion,
      renderingVersion = renderAsChoicesVersion)
    let prePhase13Witness = @[
      integerChoice(42'i64, low(int64), high(int64), 0'i64)]
    db.save(bareKey, prePhase13Witness, 64)
    # The bare key has an entry — sanity check.
    check db.loadPrimary(bareKey).len == 1
    # But the Phase-13 load (which only looks at `:sat`) does NOT
    # see it. Clean migration: stale entries are invisible, never
    # returned silently.
    var errors: seq[string] = @[]
    let loaded = loadSymexWitnessesImpl(db, progA, target,
                                         defaultSymexSettings(), errors)
    check loaded.len == 0
