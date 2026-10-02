## Phase 13 cycle 10 — `saveSymexVerdict` / `loadSymexVerdict`
## macro forms.
##
## Mirror `saveSymexWitness` / `loadSymexWitnesses` (Phase 10) but
## for non-SAT verdicts. The `status: SymexFindingStatus` param is
## a runtime value (not `static`) — the suffix selection is
## runtime-dispatched. RFC-0005 S8av: error accumulation routes
## through `recordSymexDbError`/`consumeSymexDbErrors` (the same
## thread-local sink `symexFindAllWitnesses` drains into
## `Report.dbErrors`), so a caller of this standalone macro form
## sees a save/load failure there (see
## `tests/tsymex_rfc0005_s8av_remainder.nim`); callers wanting a
## locally-scoped `errors` seq instead use `saveSymexVerdictImpl` /
## `loadSymexVerdictImpl` directly.
import std/[unittest, options]
import nelli/symex
import nelli/db
import nelli/engine/types

proc fnXyz(x: int) =
  if x == 42:
    symexTarget("xyz")

suite "symex Phase 13 cycle 10 — verdict macro forms":
  test "saveSymexVerdict + loadSymexVerdict round-trip via the macro form":
    let db = inMemoryDatabase()
    saveSymexVerdict(db, fnXyz, tLabel("xyz"),
                     defaultSymexSettings(), sfUnsat, Soundness())
    let loaded = loadSymexVerdict(db, fnXyz, tLabel("xyz"),
                                   defaultSymexSettings())
    check (loaded.isSome and loaded.get.status == sfUnsat)
