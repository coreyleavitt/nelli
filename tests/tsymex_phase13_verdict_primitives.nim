## Phase 13 cycle 3 — verdict-cache primitives.
##
## `saveSymexVerdictImpl` / `loadSymexVerdictImpl` are the runtime
## bodies behind cycle-10's macro forms. They handle non-SAT
## verdicts (sfUnsat / sfUnknown) under the content-addressed key
## namespace established in cycle 2 (`:unsat` and `:unk` sibling
## slots). The sentinel value is an empty `seq[ChoiceNode]` (`@[]`).
##
## Both procs accept an `errors: var seq[string]` accumulator so
## cache failures (disk full, permissions, corruption) flow back
## to the caller's `Report.dbErrors` instead of aborting the
## analysis — fixing a pre-existing cross-layer DB-contract
## inconsistency surfaced by the v2 audit.
import std/[unittest, options, strutils]
import proptest/symex
import proptest/db
import proptest/smt/[types, dsl, runtime, canonicalize]
import proptest/engine/types

# Hand-built SymexProgram: empty body, no params. The IR isn't
# important — these tests exercise the DB round-trip mechanics,
# not Z3 / walker semantics.
let prog = SymexProgram(body: mkBlock(@[]))
let target = tLabel("verdict")

suite "symex Phase 13 cycle 3 — verdict primitives":
  test "save UNSAT, load returns some(sfUnsat)":
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, prog, target,
                         defaultSymexSettings(), sfUnsat, errors)
    let loaded = loadSymexVerdictImpl(db, prog, target,
                                       defaultSymexSettings(), errors)
    check loaded.isSome
    check loaded.get == sfUnsat
    check errors.len == 0

  test "tie-break: save UNSAT then UNKNOWN — load returns sfUnsat":
    # Both verdicts land at distinct keys (`:unsat` vs `:unk`).
    # The load checks `:unsat` first, returns sfUnsat without
    # ever reaching `:unk`.
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, prog, target,
                         defaultSymexSettings(), sfUnsat, errors)
    saveSymexVerdictImpl(db, prog, target,
                         defaultSymexSettings(), sfUnknown, errors)
    let loaded = loadSymexVerdictImpl(db, prog, target,
                                       defaultSymexSettings(), errors)
    check loaded.isSome
    check loaded.get == sfUnsat

  test "tie-break is LOAD-order not save-order: UNKNOWN saved first":
    # This is the only sequence that actually exercises the rule.
    # If an implementer wired loadSymexVerdictImpl to check `:unk`
    # first (e.g. by alphabetical order), this test fires: the load
    # would return sfUnknown because it was saved first. The
    # contract is that UNSAT wins regardless of save order.
    let db = inMemoryDatabase()
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(db, prog, target,
                         defaultSymexSettings(), sfUnknown, errors)
    saveSymexVerdictImpl(db, prog, target,
                         defaultSymexSettings(), sfUnsat, errors)
    let loaded = loadSymexVerdictImpl(db, prog, target,
                                       defaultSymexSettings(), errors)
    check loaded.isSome
    check loaded.get == sfUnsat

  test "db.save failure accumulates errors; analysis continues":
    # A test-only database whose saveImpl raises. The verdict save
    # must catch the failure, append a message to `errors`, and
    # return normally — the cache is best-effort.
    let failingDb = ExampleDatabase(
      saveImpl: proc(testId: string, choices: seq[ChoiceNode],
                     maxEntries: int) =
        raise newException(IOError, "disk full"),
      loadPrimaryImpl: proc(testId: string): seq[seq[ChoiceNode]] = @[])
    var errors: seq[string] = @[]
    saveSymexVerdictImpl(failingDb, prog, target,
                         defaultSymexSettings(), sfUnsat, errors)
    check errors.len == 1
    check "disk full" in errors[0]
    # Load returns none (loadImpl returns @[] — empty/miss).
    let loaded = loadSymexVerdictImpl(failingDb, prog, target,
                                       defaultSymexSettings(), errors)
    check loaded.isNone
