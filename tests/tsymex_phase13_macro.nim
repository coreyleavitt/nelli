## Phase 13 cycle 10 — `saveSymexVerdict` / `loadSymexVerdict`
## macro forms.
##
## Mirror `saveSymexWitness` / `loadSymexWitnesses` (Phase 10) but
## for non-SAT verdicts. The `status: SymexFindingStatus` param is
## a runtime value (not `static`) — the suffix selection is
## runtime-dispatched. Error accumulation is internal and
## discarded, matching the existing witness macros; callers
## wanting error reporting use `saveSymexVerdictImpl` /
## `loadSymexVerdictImpl` directly with their own `errors` seq.
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
                     defaultSymexSettings(), sfUnsat)
    let loaded = loadSymexVerdict(db, fnXyz, tLabel("xyz"),
                                   defaultSymexSettings())
    check loaded == some(sfUnsat)
