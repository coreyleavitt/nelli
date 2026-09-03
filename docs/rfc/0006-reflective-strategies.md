# RFC — reflective strategies: give `Strategy[T]` an inverse

- **Status:** seed — composed 2026-09-03 from the post-0005 architecture
  survey. Not yet designed; §4 lists what must be settled before `/tdd`.
- Category: core
- Size: M
- Value: critical
- **Depends on:** none.

## §0 — Thesis

`Strategy[T]` is `{run, display, constraintDigest}` (`strategy.nim:76-91`).
It knows how to turn choices into a value. It has no idea how to turn a value
back into choices.

That single missing direction is the root cause of five separately-documented
weaknesses. They have been fixed, worked around, or given their own enum
value one at a time; none of them is independently fixable.

## §1 — The five symptoms, all one cause

1. **Explicit examples cannot shrink.** `engine.nim:230` states it plainly:
   *"we don't shrink them (no choice sequence to shrink)"*, and
   `phases.nim:101` reports `choices: @[]`. A user pins the one input that
   matters most and gets the *least* engine support for it.

2. **The regression corpus silently evaporates on a generator edit.** The DB
   persists choice bytes. A changed strategy makes replay raise `Overrun`
   (`datasource.nim:126`); `dbReusePhase` reads that as staleness and calls
   `removeMany` (`phases.nim:66-84`). Widen a bound, reorder two `given`
   bindings, add a draw — every stored witness for that test is deleted, with
   no diagnostic. The auto-prune is correct given what is stored; what is
   stored is the problem.

   **This costs a consuming team more than it looks.** Generator churn is not
   an occasional event in an application under active development — it is
   continuous, because generators track types that are still being designed.
   So the "failures replay across runs" promise degrades exactly when the
   application is moving fastest, and recovers only once the code stops
   changing. The regression DB is weakest in the phase it was built for.

3. **An outside value cannot enter the shrinker at all.** A production
   payload, a customer bug report, an AFL corpus file, a value pasted from a
   log — there is no door. The shrinker only minimizes sequences it recorded
   itself.

   For a consuming team this is the single most-wanted workflow nelli does not
   have: *production handed us this input, minimize it.* Today the answer is to
   hand-write a strategy that happens to reproduce the value, which is the
   manual shrinker the library's whole thesis exists to abolish.

4. **Symex witnesses replay by hand and can miss.** Witnesses are linearised
   via `renderAsChoices` and re-fed positionally; the failure mode is
   first-class enough to have its own status, `sfReplayMiss`
   (`engine/types.nim:31-38`), documented as diagnosing *"generator-skew
   issues where the witness's choice sequence no longer maps to the
   strategy's draw shape."* With an inverse, the witness value is re-parsed
   through the live strategy and the skew cannot arise.

5. **The fuzzer cannot recombine at the value level.** Crossover operates on
   choice IR (`fuzzir.nim`). Structure-aware, but blind to the value —
   splicing two valid values is not expressible.

## §2 — Mechanism (sketch, not a design)

Add an optional fourth field:

```nim
Strategy*[T] = object
  run*: proc(src: var DataSource): T {.closure.}
  display*: proc(t: T): string {.closure.}
  constraintDigest*: string
  parse*: proc(t: T, sink: var ChoiceRecorder): bool {.closure.}   # new
```

`parse` emits the choice sequence that would have produced `t`, or returns
false if `t` is outside this strategy's range. Every built-in combinator
either propagates it or explicitly declines.

**The precedent is already in the type.** `display` is exactly this shape —
an optional, type-indexed per-strategy function that combinators carry
forward where they can and deliberately drop where they cannot
(`strategy.nim:79-85` documents why `map`/`flatMap` drop it). `parse` is the
same discipline applied to a harder function. `map` drops it for the same
reason (no general inverse of `T → U`); `mapWithDisplay` has an obvious
sibling in `mapWithParse` / an invertible-map combinator.

This is Goldstein & Pierce's reflective generators (POPL 2023) transposed
from a free-monad generator to a choice-sequence engine. The transposition is
the interesting part and is where the design work lives.

## §3 — Scope

**In scope.** The `parse` field; propagation through every built-in
combinator; the partiality story (`filter` is the hard case); value-level
persistence in the example DB alongside choices; shrinkable explicit
examples; an ingestion door for outside values.

**Out of scope for this RFC** (named so the boundary is explicit): value-level
fuzz crossover, and the assurance record's value-level evidence. Both become
cheap once `parse` exists; both are separate RFCs.

## §4 — Open questions for the design phase

- **Partiality.** `filter`, `oneOf`, and `flatMap` are where an inverse gets
  hard. Is `parse` best-effort (returns false, caller falls back), or must a
  strategy declare invertibility in its type? Best-effort keeps the surface
  small; a declared property makes the guarantee checkable. This is the
  central design fork.
- **Round-trip law.** `parse` then `run` must reproduce the value. That is a
  property nelli can check about itself — and should, on every built-in
  combinator, as the RFC's own acceptance test.
- **DB schema.** Store the value *alongside* choices, or derive choices on
  demand from a stored value? The second is smaller but requires a `T`
  serializer the library does not have.
- **`display` and `parse` are converging** on "optional type-indexed function
  carried by a strategy." Two ad-hoc fields or one extension mechanism?

## §5 — First slice: the instrument, not the feature

**Slice 1 is a shrink-quality benchmark, and it lands before any of §2.**

There is no measurement of shrink quality anywhere in the repo. `tshrinker.nim`
asserts a handful of specific minima; nothing measures step counts, nothing
measures quality across combinator shapes, there is no per-pass timeout, and
the only guard is `maxShrinks = 500` (`shrinker.nim:411` — where `<= 0` reads
as *unbounded*).

Without a baseline, this RFC cannot show it improved anything, and cannot
show it broke nothing.

The benchmark corpus must cover the shapes where internal shrinking is known
to degrade: `filter` with a low acceptance rate, `flatMap` where the second
draw's shape depends on the first, `oneOf` across branches of different
lengths, `recursive` at depth, and stateful sequences with bundle dependencies.
Each case asserts a known minimum and a step-count budget.

**This slice has a second, independent payload.** Falsify's (de Vries, 2023)
contribution is precisely that internal shrinking is *not* automatically good
— that a linear sequence shrinks `flatMap` badly and a sample *tree* does not.
nelli's sequence is linear plus closed spans (`datasource.nim:26-49`), not a
tree. **Whether that costs us is currently an unanswerable question.** After
slice 1 it is a measured number. If the number is bad, that spawns its own
RFC — a shrinker representation change is not a slice of this one.

## §6 — Why this first

Of everything on the post-0005 board, this is the only item that is
simultaneously: a fix for five documented defects, a prerequisite for
value-level evidence in the assurance record, an enabler for value-level fuzz
crossover, and a single optional field on a type that already has the exact
precedent for it.

It is also the item peers cannot copy. Hypothesis has wanted an inverse for
years and cannot retrofit one onto its generator model.
