## R4 (code review, medium/behavioral): `fuzz()` gated its corpus
## `loadCorpus`/`saveCorpus` calls on `settings.database.saveImpl != nil`
## (a proxy field) rather than on `loadCorpusImpl`/`saveCorpusImpl`
## themselves. db.nim's documented philosophy (module doc ~line 85-90) is
## that an unset section degrades to empty rather than crashing — but a
## hand-built `ExampleDatabase` object literal that sets `saveImpl` /
## `loadPrimaryImpl` while leaving the newer `saveCorpusImpl` /
## `loadCorpusImpl` fields nil (the partial-object-literal idiom already
## used elsewhere in this repo, e.g. tests/tsymex_phase13_verdict_primitives.nim)
## nil-derefed the instant `fuzz()` ran: `dbActive` was true (saveImpl set),
## so the loop unconditionally called `settings.database.loadCorpus(testId)`
## / `saveCorpus(...)`, which dispatch through the nil `loadCorpusImpl` /
## `saveCorpusImpl` closures with no nil-check.
##
## Fix: gate each corpus call on its OWN closure field's nil-ness, so a
## partial database degrades to "no corpus persistence" instead of crashing.

import std/unittest
import proptest

proc coverageByValue(): Target[int] =
  ## One hot edge per (x mod 8): distinct inputs light distinct edges, so the
  ## corpus grows and the loop takes the "admit + persist" path at least once.
  Target[int](run: proc(x: int): Observation[int] =
    var c = newSeq[byte](8)
    c[(x mod 8 + 8) mod 8] = 1'u8
    Observation[int](verdict: vOk, coverage: Coverage(counters: c)))

suite "fuzz: corpus load/save honor their own nil-ness (R4)":
  test "a database with saveImpl set but saveCorpusImpl/loadCorpusImpl nil does not crash":
    # Mirrors the partial-object-literal idiom from
    # tests/tsymex_phase13_verdict_primitives.nim: only the primary-section
    # closures are wired up. corpus-section closures are left nil, as a
    # minimal/older hand-built backend would.
    let partialDb = ExampleDatabase(
      saveImpl: proc(testId: string, choices: seq[ChoiceNode], maxEntries: int) =
        discard,
      loadPrimaryImpl: proc(testId: string): seq[seq[ChoiceNode]] = @[])
    check partialDb.saveImpl != nil
    check partialDb.saveCorpusImpl == nil
    check partialDb.loadCorpusImpl == nil

    var fr = newCoverageFrontier("bin1")
    let s = FuzzSettings(maxIterations: 300, seed: 1, database: partialDb,
                         persistKey: "camp")
    # Must not nil-deref-crash. Corpus persistence degrades to a no-op.
    let rep = fuzz(integers(0, 1000), coverageByValue(), fr, s)
    check rep.corpus.irEntries.len >= 1
