# RFC — config discipline: object literals silently disable the engine

- **Status:** seed — composed 2026-09-03 from the post-0005 architecture
  survey. The smallest item on the board and the only one carrying a live
  user-facing defect. Not yet designed.
- Category: core
- Size: S
- Value: med
- **Depends on:** none.

## §0 — Thesis

Nim object literals zero-fill unlisted fields. nelli's settings objects carry
meaningful non-zero defaults. The documented idiom is the object literal.

Therefore **the documented idiom silently ships a different engine than
`defaultSettings()`**, and it does so with no warning, no error, and no
observable symptom except worse testing.

The library has already met this problem four times and answered it four
different ways.

## §1 — The defect, in the README

`defaultSettings()` (`engine/types.nim:185-190`) sets seven non-zero fields.
The README's own headline example is:

```nim
with Settings(maxExamples: 7, seed: 42,
              testId: "kdl-keywords", dbPath: ".nelli-db")
```

That run silently gets:

| field | intended | actual | consequence |
|---|---|---|---|
| `flakyRetries` | 5 | **0** | the two-layer flakiness detector is off |
| `maxShrinks` | 500 | **0** | `shrinker.nim:411` reads `<= 0` as *unbounded* |
| `useSA` | true | **false** | the simulated-annealing escape never runs |
| `autoLabels` | true | **false** | no distribution labels |
| `printEvents` | true | **false** | no event output |

Every one of these is a feature the README sells one section later. A user
following the documentation gets an engine with the flakiness detector
disabled and an unbounded shrink loop, and is never told.

**Note who this lands on.** The object literal is what a team copies on day
one, while evaluating whether nelli is worth adopting. So the defect is
aimed precisely at the least experienced user, at the moment they are forming
a judgement, and it degrades the two things that judgement rests on — whether
failures are trustworthy (flakiness detection, off) and whether shrinking
terminates (unbounded). A slow or flaky first impression reads as "this
library is slow and flaky," not as "I mis-constructed the settings."

`tdsl.nim:42-44` and `tengine.nim:28` show the same idiom throughout the test
suite, which means the suite is partly testing a configuration no user
intends and no default produces.

## §2 — Four answers to one problem

| surface | policy | site |
|---|---|---|
| `Settings` | none — raw object literal | `engine/types.nim:80` |
| `IntegerBiasConfig` | all-zero sentinel, resolved at use | `distribution.nim:47-64` |
| `SymexSettings` | `withSymexSettings` mutator builder | `smt/types.nim:2955` |
| `ResourceBudget` | hand-written `+` comparing each field to its default | `smt/types.nim:2965-2986` |
| `FuzzSettings` | no default constructor at all | `fuzz.nim:338` |

`distribution.nim:47-54` is worth reading in full: someone hit exactly this
hazard, understood it precisely, and fixed **one field** with a bespoke
sentinel — explicitly *"so a caller can construct `Settings(...)` as an object
literal … and still get the default semantics."* The diagnosis was right and
the fix was scoped to the field in front of them.

`ResourceBudget`'s `+` is the worst of the four by construction: fourteen
hand-written per-field comparisons, one per field, where a forgotten line is a
silent wrong default. Every new field is a maintenance obligation that nothing
enforces.

## §3 — Scope

**In scope.**

1. **One policy for partial configuration**, applied to all five surfaces. A
   builder, a merge that is derived rather than hand-written, or a first-class
   optional-field representation — that is the design question.
2. **Fix the README** and the test-suite idiom that inherited it.
3. **`given x: int`** — implicit `arbitrary(T)` in the DSL, so the most common
   binding stops being the most verbose. Mechanical in `dsl.nim:60-70`.
4. **The one vague derive error.** `derive.nim:511` emits *"arbitrary: cannot
   derive a strategy for type X"*. Every other derivation failure path names
   the offending field and prescribes a fix (`derive.nim:118`, `:188`,
   `:269`). This one is the fallback — the one users hit most, and the only
   one that doesn't help.

**Out of scope.** Field-level strategy annotations on derived types (e.g.
`age: integers(0, 150)` inside an object). Real want, different mechanism,
its own RFC.

## §4 — Open questions for the design phase

- **Builder vs. derived merge vs. optional fields.** A macro-derived merge
  kills `ResourceBudget`'s per-field maintenance obligation permanently, which
  the mutator-builder does not. But it changes construction ergonomics for
  every existing call site. The library has evidence for both — this is the
  fork.
- **Is the object literal a supported way to build settings at all?** The
  cleanest answer may be that it isn't — make the type non-literal-constructible
  and force the builder. That breaks every existing call site, which by the
  project's own standing bar is a cost, not a veto.
- **Do the five surfaces share one mechanism**, or does each keep its own with
  a documented rule? One mechanism is right if a generic merge is achievable;
  five bespoke ones is what we have.

## §5 — First slice

Make the hazard visible before fixing it: a test that constructs each settings
type both ways and asserts the resulting *behaviour* differs. That test is
red today and is the RFC's acceptance criterion. It also enumerates every
affected surface, which §2 currently does by hand.

## §6 — Why bother with an RFC for this

Because the four existing answers show that patching the field in front of you
produces exactly this state. The fix worth making is the general one, and a
general fix that breaks call sites is a design decision, not a chore.
