## Phase 13 cycle 2 — SAT witnesses move to a `:sat`-suffixed key.
##
## Pre-RFC, `saveSymexWitnessImpl` stored witnesses at the bare
## content-addressed key `"sx:" & H`. Phase 13 introduces sibling
## keys `:sat`/`:unsat`/`:unk` so the three verdicts can coexist
## under one content-addressed namespace. SAT moves to `:sat` in
## this cycle; UNSAT/UNKNOWN land in cycle 3.
##
## This test pins the suffix participation directly: after saving
## a witness via the macro form, the DB has an entry at the
## suffix-decorated key AND no entry at the bare key. The new
## `symexCacheKeyForFn` macro derives the content-addressed hash
## at test time so the test can probe `db.loadPrimary` directly
## rather than going through the macro round-trip.
import std/[unittest, options]
import proptest/symex
import proptest/db
import proptest/choice
import proptest/int128
import proptest/engine/types
import proptest/smt/canonicalize

proc fnOne(x: int) =
  if x == 1:
    symexTarget("one")

suite "symex Phase 13 cycle 2 — :sat suffix":
  test "saveSymexWitness writes to H & ':sat', NOT to the bare key":
    let db = inMemoryDatabase()
    let witness = SymexFinding(
      targetDesc: "label(\"one\")",
      status: sfSat,
      witnessChoices: @[integerChoice(1'i64, low(int64), high(int64), 0'i64)],
      z3Version: z3FullVersion())
    saveSymexWitness(db, fnOne, tLabel("one"),
                     defaultSymexSettings(), witness)

    let h = symexCacheKeyForFn(fnOne, tLabel("one"), defaultSymexSettings())
    let satKey  = h & cacheKeySatSuffix
    let bareKey = h
    check db.loadPrimary(satKey).len == 1
    check db.loadPrimary(bareKey).len == 0
