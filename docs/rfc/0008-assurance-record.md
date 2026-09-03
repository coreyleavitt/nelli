# RFC — the assurance record: one evidence artifact per property

- **Status:** seed — composed 2026-09-03 from the post-0005 architecture
  survey. Merges three survey candidates (evidence ledger, statistical
  distribution contracts, suite-level budget scheduler) because they share one
  mechanism; see §2. Not yet designed.
- Category: core
- Size: M
- Value: high
- **Depends on:**
  - RFC-0006 (reflective-strategies) — soft. The record can ship without it;
    value-level evidence (as opposed to choice-sequence evidence) needs it.

## §0 — Thesis

nelli computes an unusual amount of evidence about a property and then
scatters it across three unrelated shapes and drops the rest on the floor.

| engine | result type | site |
|---|---|---|
| PBT | `Report[T]` | `engine/types.nim:147` |
| fuzz | `FuzzReport` | `fuzz.nim:533` |
| symex | `SymexResult[T]` | `smt/types.nim:1610` |

No shared base, no composition, no aggregation. `MutationReport`
(`mutation.nim:42`) touches none of them — the mutation score is a measure
*of a property* that the property's own report cannot carry. There is no
artifact that says, for one property: *proven by symex under bounds X, fuzzed
N cases reaching Y edges, mutation score Z, distribution labels W.*

`Report[T]` is already halfway there — it carries `symexFindings`,
`coverageHits`, `crash`, `events`, `necessity`. The evidence is real. It is
just not addressable, not persisted, and not something CI can hold you to.

## §1 — Why this is the answer to "testing more explicit and complete"

Two failures are invisible today and both are silent:

- **Distribution drift.** `autoLabels` and `event` produce histograms; nothing
  *asserts* them. A generator that stops producing empty lists after a
  refactor passes 10,000 examples and reports success. The tests are green and
  the coverage they claim is fiction.
- **Assurance regression.** Someone widens a generator's bounds and a symex
  `sxUnsat` proof no longer holds under the new domain. Nothing fails. The
  proof was real when it was made and is now stale, and the suite cannot tell
  the difference.

Both are cases of *evidence that decayed without anyone being told*. That is
what a persisted, diffable record fixes and nothing else does.

## §2 — Why these three merge

They are one mechanism seen from three sides — a **per-property evidence
record that persists across runs**.

- The **record** is the substrate: what was checked, how hard, under what
  bounds, with what result.
- **`cover(pct, cond, label)`** *writes* a statistical verdict into it. It is
  not a separate feature with its own report; a distribution claim is
  evidence, and its natural home is the record's distribution section.
- The **suite scheduler** *reads* it to allocate budget ("which property is
  under-tested relative to its evidence?") and writes back what each property
  received.

Merging them is not thematic. Splitting them would mean designing the record
against a single consumer — the CI gate — and that is exactly how a shared
abstraction freezes into the shape of consumer one and has to be reshaped when
consumer two arrives. **The scheduler is the second consumer that validates
the record's interface**, and it should be spiked early in the design even if
it ships last.

## §3 — Scope

1. **`Assurance` record**, per property: examples run and outcome;
   distribution labels with any `cover` verdicts; symex verdict **together
   with the bounds it held under** (a proof without its bounds is not
   evidence); fuzz edges and corpus provenance; mutation score when available.
2. **`cover(pct, cond, label)`** backed by a sequential probability ratio test
   (Hughes' `checkCoverage` in QuickCheck): grow the sample adaptively until
   the hypothesis is decided, then report with confidence — *"expected ≥30%
   'empty', observed 0.4% over 12,800 examples, p < 0.001."*
3. **`nelli.assurance.json`** for a suite, plus a policy file (*"this property
   must be symex-proven, or mutation score ≥ 0.9"*) so CI fails on assurance
   regression, not just on test failure.
4. **Suite-level budget scheduler.** Today every property gets a flat
   `maxExamples`; a 400-property suite spends identical budget on the
   trivially-true one and on the one a single example away from a bug. Treat
   the suite as a bandit over properties, allocate by expected new behaviour,
   budget in wall-clock, persist across CI runs. **The machinery already
   exists at the wrong altitude** — `bandit.nim` and the corpus DB do exactly
   this *within* one fuzz campaign.

## §4 — Open questions for the design phase

- **Is `Assurance` a fourth report type, or does `Report[T]` grow into it?**
  Growing `Report[T]` keeps one door but makes the PBT type carry fuzz and
  symex concerns — the same coupling the M12 partitioning deliberately avoided
  when it split `FuzzSettings` from `Settings` (`fuzz.nim:339-342`). A
  separate record that the three engines *contribute to* is likelier correct,
  and is a genuinely different design.
- **Identity.** What keys a record across runs? `testId` is the PBT answer;
  fuzz uses `persistKey#targetId` (`fuzz.nim:1809-1828`). Two schemes exist
  and the record needs one.
- **Staleness policy.** When source changes, which evidence survives? Symex
  has a content-addressed answer (`symexCacheKeyForFn`); nothing else does.
- **`cover` and `maxExamples` interact.** An SPRT decides its own sample size;
  a fixed `maxExamples` fights it. Which wins, and does a `cover` failure
  falsify the property or report separately?
- **Scheduler scope.** Does it drive `nimble test`, or is it a separate
  `nelli` binary? A separate runner is a packaging surface nelli does not have
  today.

## §5 — First slice

The record, populated from what `Report[T]` **already carries**, serialized,
and diffable. No new evidence sources, no `cover`, no scheduler — prove the
shape holds the evidence that exists before adding evidence to it. Then spike
the scheduler against it (throwaway, to validate the interface), *then* build
`cover`.

## §6 — Why this is the capstone

The README's claim is "one engine, one API." Today that is true of the front
door and false of everything that comes back out. This makes it true in the
direction that matters — and nobody in the PBT or fuzzing space ships a
diffable per-property assurance artifact.
