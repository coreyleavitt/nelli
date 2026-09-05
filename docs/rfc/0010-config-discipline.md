# RFC — config discipline: object literals silently disable the engine

- **Status:** implemented — all 19 slices landed 2026-09-04 on
  `rfc-0010-config-discipline`, each gated by a whole-suite `sweep-diff`
  against a recorded baseline. End to end, pre-A1 baseline vs final tree:
  `unchanged=454 regressed=0`, plus the two new definition-of-done suites.
  All three Windows legs green on the first run (2026-09-05): `fuzzer-msvc`,
  `fuzzer-mingw`, `symex-mingw`. Not yet merged or tagged; the release gate is
  `0010-config-discipline.downstream-audit.md` §7. Seeded 2026-09-03 from the
  post-0005 architecture survey; `/architect` round 1 (2026-09-03, `fable`,
  five lenses) corrected the premises and settled the mechanism empirically,
  round 2 (2026-09-04) rebuilt the slice plan against the real files. See the
  handoff's execution log for what implementation found that review could not.
- Category: core
- Size: L
- Value: high
- **Depends on:** none.

## §0 — Thesis

Nim object literals zero-fill unlisted fields. nelli's settings objects carry
meaningful non-zero defaults. The documented idiom is the object literal.

Therefore **the documented idiom silently ships a different engine than
`defaultSettings()`**, and it does so with no warning, no error, and no
observable symptom except worse testing.

The library has already met this problem **nine** times across **eleven**
surfaces and answered it nine different ways — including two surfaces whose doc
comments actively recommend the hazardous idiom.

**Round 1 settled the mechanism.** Nim 2.2.10 object field defaults
(`maxExamples*: int = 100` in the type declaration) apply to partial object
literals *and* preserve explicitly-written zeros. That property — distinguishing
"unset" from "deliberately zero" at the language level — is exactly what every
sentinel/merge scheme lacks, and it fixes the defect at **zero call-site cost**.
The seed's three-way design fork (§4 as written) is answered by a fourth option
it never considered. See §4.

**The invariant this RFC establishes**, which is the part that outlives the ten
repairs:

> For every configuration object `T`, the empty literal `T()` **is** the
> documented default configuration, and a partial literal differs from it only
> in the fields it lists. A surface satisfies this either by declaring field
> defaults, or by designing every knob so that zero is correct (ADR-0031). Any
> constructor proc, builder, sentinel or merge introduced to work around unsafe
> partial construction is a defect of this RFC's class.

Stating it this way dissolves what round 1 called an "exemption": the ADR-0031
family is not exempt from the invariant, it **satisfies the invariant with
zeros**. One invariant with two conforming implementations is a design; two
policies reconciled by a test is the thing this RFC exists to end. The
distinction is already visible where it belongs — in the type declaration,
as the presence or absence of `= expr` on each field.

## §1 — The defect, in the README

`defaultSettings()` (`engine/types.nim:185-190`) sets **ten** fields to non-zero
values: `maxExamples`, `maxRejections`, `seed`, `flakyRetries`, `maxShrinks`,
`useSA`, `targetedSAIters`, `printEvents`, `autoLabels`, `integerBias`.

The README's own headline example (`README.md:33-34`) is:

```nim
with Settings(maxExamples: 7, seed: 42,
              testId: "kdl-keywords", dbPath: ".nelli-db")
```

It supplies `maxExamples` and `seed` itself, so it omits **eight** of the ten.
Seven of those eight are lost outright; the eighth, `integerBias`, is silently
rescued by `resolved()` at `phases.nim:260` — **the one field somebody
bespoke-fixed is the one field that survives the documented idiom**, which is
the whole argument of this RFC in a single data point. Verified by running the
README literal through the real `forAll` entry point on the pinned toolchain:

| field | intended | actual | consequence |
|---|---|---|---|
| `maxRejections` | 1000 | **0** | `phases.nim:295` reads `rejections > 0`, so the **first rejection ends the run as `otExhausted`** |
| `flakyRetries` | 5 | **0** | the two-layer flakiness detector is off |
| `maxShrinks` | 500 | **0** | `shrinker.nim:411` reads `<= 0` as *unbounded* |
| `targetedSAIters` | 200 | **0** | second, independent SA kill-switch (`targeting.nim:286-289`) |
| `useSA` | true | **false** | the simulated-annealing escape never runs |
| `autoLabels` | true | **false** | no distribution labels |
| `printEvents` | true | **false** | no event output |
| *(`integerBias`)* | defaults | *defaults* | **rescued by `resolved()`** — the exception that proves the thesis |

Measured output from that run:

```
auto.* label keys — default: 4   literal: 0
report.printEvents — default: true   literal: false
filtered strategy: default → otPassed (100 examples)
                   literal → otExhausted (2 examples)
```

`maxRejections` is the sharpest entry and the seed missed it: **any filtered or
`assume`-using property under the documented idiom reports `otExhausted` after
about two examples**, on a property that trivially holds.

`maxShrinks: 0` costs unbounded *time*, not non-termination — `shrinker.nim:411`
is a `while best != prev` fixpoint that exits when no pass makes progress.

**Note who this lands on.** The object literal is what a team copies on day
one, while evaluating whether nelli is worth adopting. So the defect is
aimed precisely at the least experienced user, at the moment they are forming
a judgement, and it degrades the two things that judgement rests on — whether
failures are trustworthy (flakiness detection, off) and whether the run is
meaningful at all (`otExhausted` on a satisfiable property). A spurious
"exhausted" reads as "this library is broken," not as "I mis-constructed the
settings."

**The test suite inherited it, but weakly.** 115 `Settings(...)` literal sites
across 24 test files omit `autoLabels` 115/115, `printEvents` 109/115, `useSA`
93, `maxShrinks` 39, `flakyRetries` 33. No assertion currently passes for the
wrong reason — the exposure is latent: any of those tests that later adds a
rejecting strategy inherits `maxRejections: 0`.

*Correction to the seed:* `tdsl.nim:42-44` is **not** an instance of the
accident. It explicitly sets `flakyRetries: 0, maxShrinks: 50, useSA: false,
targetedSAIters: 0` — a hand-written workaround by an author who already knew
about the hazard. `tengine.nim:28` (`Settings(maxExamples: 50, seed: 1)`) is the
accidental kind.

## §2 — Nine answers to one problem

The seed's survey found four (listing five rows). Round 1 found eight across ten
surfaces; round 2 found the eleventh. The real inventory:

| # | surface | policy | site |
|---|---|---|---|
| 1 | `Settings` | none — raw object literal | `engine/types.nim:80` |
| 2 | `IntegerBiasConfig` | all-zero sentinel, resolved at use | `distribution.nim:47-64` |
| 3 | `SymexSettings` | `defaultSymexSettings()` + `withSymexSettings` builder + `+` merge + named variants (`optimisedSymexSettings`/`looseSymexSettings`, `:3080-3092`) — **four answers on one type, and tests bypass all four with raw literals** | `smt/types.nim:2941,2955,2991` |
| 4 | `ResourceBudget` | hand-written `+` comparing each field to its default | `smt/types.nim:2965-2989` |
| 5 | `FuzzSettings` | **deliberate zero-is-the-default**, pinned by a test — *except* its nested `integerBias`, which is policy 2 | `fuzz.nim:338`, `:371` |
| 6 | `ExecutorConfig` / `GuidanceConfig` / `SchedulingConfig` | ADR-0031: additive knobs designed so zero *is* correct | `fuzz.nim:138,188,216` |
| 7 | `OrchestratorPolicy` | proc constructor with default parameters | `fuzz.nim:877`, ctor at `:1082-1094` |
| 8 | `BmcSettings` | none — **and the doc comment recommends the literal** | `bmc.nim:50` |
| 9 | `ConcolicAssist` | **resolve-at-use coercion** (`<= 0` → 1, `<= 0` → 8) plus coherence-by-refusal | `fuzz.nim:784-844`, `resolveAssist` at `:814-844` |
| — | `lawSettings` | in-library hand-copy of the defaults | `laws.nim:35-39` |
| — | `ResourceLimits`, `JobLimitPolicy` | zero-safe by construction | `fuzz.nim:2514`, `workerproto.nim:259` |

Four of these are worth reading in full:

`distribution.nim:47-54` — someone hit exactly this hazard, understood it
precisely, and fixed **one field** with a bespoke sentinel, explicitly *"so a
caller can construct `Settings(...)` as an object literal … and still get the
default semantics."* The same comment considers and rejects an `Option`-typed
field because it *"would change the literal construction ergonomics for every
existing test"* — i.e. §4's fork was already weighed once, and lost to the
call-site count.

`fuzz.nim:889-894` — the `OrchestratorPolicy` doc diagnoses the general defect
in as many words: three fields *"have non-zero defaults, so the zero-value
object literal would silently understate them."* The answer chosen there — a
proc constructor with default parameters — is a mechanism §4 never lists, and it
is the second doc-taught hazard site: the comment tells the reader the bare
literal is poisoned, and after this RFC it must not be.

`bmc.nim:50-58` — **a live, unlisted instance of the defect, actively taught**:
*"Non-generic so users can write `BmcSettings(maxDepth: 5, ...)` as an object
literal without spelling the state type."* Following that advice leaves
`maxStates: 0`, and `bmc.nim:86` (`if explored >= settings.maxStates`) returns
`bmcExhaustedBudget` before exploring a single state.

`fuzz.nim:814-844` — `ConcolicAssist` is a ninth policy: not a sentinel resolved
to defaults but a **coercion** (`stallRounds <= 0` becomes 1,
`maxBranchAttempts <= 0` becomes 8), which makes an explicit `0` unrepresentable
— the class §3 disqualifies. It is deliberate, shipped design from RFC-0004
round 2, already pinned at `tests/tfuzzconfigdefaults.nim:46-53`, and it
conforms to §0's invariant in its own way. It is **exempt and pinned**, not
reopened; the taxonomy simply needed the row.

`ResourceBudget`'s `+` is the worst by construction: thirteen hand-written
per-field comparisons where a forgotten line is a silent wrong default, and
there is a **second** copy of the same obligation for `SymexSettings`
(`smt/types.nim:2991-3003`) that the seed missed. Both also carry the
partial-as-full-value limitation: they key on *differs-from-default*, so **the
default value itself is unwritable through the merge** — with
`a.maxCallDepth = 10`, passing `b` with `maxCallDepth` set to the default 3
yields 10, silently. §4 explains why that is inherent to composition and not the
same defect as unsafe construction.

A tenth thing exists that the taxonomy has no row for, because it is a different
axis: `validateSymexSettings` (`smt/types.nim:3005`) encodes cross-field
*coherence* rules as runtime warnings, on one surface only — and it is exported,
unit-tested, and **called by nothing in `src/`**. Coherence is a real and
separate axis (on `Settings`, `useSA` needs `targetedSAIters > 0` to do
anything; `dbPath`/`testId`/`strictDb` form a persistence triple) with at least
three incompatible existing styles: warn (`validateSymexSettings`),
coerce (`resolveAssist`), and refuse (`ConcolicAssistError`, `fuzz.nim:642`).
Unifying those is its own design problem. **§5 puts it explicitly out of
scope** — but note that this RFC *shrinks* the live incoherence class as a side
effect: with `useSA: true` and `targetedSAIters: 200` both arriving as declared
defaults, the incoherent "SA on, zero iterations" state stops arising from any
partial literal and starts requiring two deliberate writes.

## §3 — The empirical result (rounds 1 and 2)

Probed on the pinned toolchain (Nim 2.2.10, `localhost/nelli-dev`, via
`scripts/dt-bounded.sh c`). Reproduced independently three times, the third
against a **full-shape `Settings` replica** (`Duration`, `uint64`,
`set[PhaseId]`, strings, a nested object with no initializer, and a
const-symbol default value) rather than a toy type.

| construction | declared field defaults applied? |
|---|---|
| `T(a: 7)` — partial literal | **yes** |
| `T()` — empty literal | yes |
| `T(a: 0, c: false)` — **explicit zeros** | **yes, and the zeros survive** |
| `default(T)` | yes |
| `const T(...)` — VM / compile time | yes |
| nested object field, no initializer | yes, recursively |
| object-variant branch fields | yes |
| `newSeq[T](n)` | yes |
| `new(ref T)` | yes |
| `var v: T` — bare declaration | **no — zero-fills** |
| `var a: array[N, T]` | **no — zero-fills** |
| module-level `var` / `{.threadvar.}` | **no — zero-fills** |
| `reset(x)` | **no — zero-fills, does not restore defaults** |
| `proc f(): T = discard` — result never constructed | **no — zero-fills** |

Row 3 is the decisive one. Field defaults distinguish *unset* from *explicitly
zero* **in the language**, which no sentinel or merge scheme can do. That
matters because zero is a legitimate, documented user intent across these types:

- `Settings.maxShrinks: 0` = unbounded (`shrinker.nim:411`)
- `Settings.targetedSAIters: 0` = SA off (`targeting.nim:286-289`, documented as
  "taken literally")
- `Settings.flakyRetries: 0` = retries off (used at `laws.nim:37`, `tdsl.nim:43`)
- `Settings.useSA` / `printEvents` / `autoLabels` — **bools whose default is
  `true`, so `false` *is* the zero value**. Under any zero-sentinel merge these
  three become impossible to turn off.
- `Settings.seed: 0` — a legitimate seed (`pipeline.nim:143`)
- `ResourceBudget.queryRLimit` / `maxFrontierSize` / `maxHeapDepth` /
  `maxSplitParts` — 0 = unlimited, *as the default* (`smt/types.nim:1656`)
- `FuzzSettings.maxIterations` / `timeBudget` / `checkpointCadence` — all
  documented "0 = off/uncapped"

**This disqualifies the zero-sentinel merge outright, and the
differs-from-default merge nearly so, as *construction* mechanisms.** Field
defaults are immune at construction. (§4 draws the line between construction and
composition, which is where the surviving merge lives.)

No in-scope field type is illegal or semantics-changing as a declared default:
all five in-scope types are flat value types with no floats, refs, procs or
Tables, so structural `==` is well-defined and free of NaN/identity/ordering
hazards — verified on the full-shape replica.

`{.requiresInit.}` composes with field defaults and closes the `var v: T` hole:
with every field carrying an explicit default, the partial literal stays legal,
the empty literal stays legal, explicit zeros survive, and `var v: T` becomes a
**compile error**. Verified. Two costs, also verified: `newSeq[T]`/`setLen`
emit `UnsafeDefault`/`UnsafeSetLen` warnings, and every field must then carry an
explicit `= expr`. Nesting is *not* affected — a containing object that omits
the field still gets the defaults.

## §4 — Mechanism (settled) and what remains

**Settled: declared field defaults, on `Settings`, `IntegerBiasConfig`,
`SymexSettings`, `ResourceBudget`, `BmcSettings` and `OrchestratorPolicy`.**
`defaultSettings()` collapses to `Settings()`. The README example becomes correct
as written. Zero call sites are forced to change.

**Why no new abstraction.** The deep module here is the compiler. The interface
is the type declaration itself — each default sits beside the field it governs,
visible at the definition — and the implementation it hides (partial literals,
`default(T)`, `const`/VM, `newSeq`, `new`, recursive nesting) is the language's,
verified in §3. A library-level substrate — a unified settings registry, layered
or scoped config, a capability split — would *add* interface to hide *less*
implementation, and would couple surfaces that legitimately differ:
`Settings` is a runtime value, `SymexSettings` is a `static` cache-keyed
`const`, `FuzzSettings` feeds an orchestrator. Grouping `Settings`' engine /
search / reporting / persistence knobs into sub-objects stays available forever
at the same price (§3: nested defaults recurse), so doing it now would spend
this RFC's best property — zero call-site cost — on aesthetics. The RFC stops at
the mechanism deliberately; §0's invariant is what generalises it.

**Construction versus composition.** §3 disqualifies differs-from-default
keying as a *construction* mechanism, because at construction the language can
do strictly better. `+` is not construction: it composes two values that are
already fully built, where presence information genuinely does not exist and
cannot be recovered. So retaining differs-from-default keying inside `+` is a
**narrowing of §3's disqualification, not a contradiction of it** — and this
sentence exists because two reviewers independently read it as a contradiction.
What §2 calls a "live bug" is precisely that the limitation was undocumented and
hand-duplicated across two bodies; what remains after §6 is the documented,
inherent limitation of representing a partial as a full value, with a one-line
escape hatch (set the field on the base).

**Deprecate, do not delete.** Round 1 scoped `resolved()`, `withSymexSettings`
and both `+` bodies for deletion. Round 2 established that all four are
**public** — `resolved` via `engine/types.nim:13`'s `export distribution`, the
others via `smt/dsl.nim:9-10` → `symex.nim:37-38` — and that
`withSymexSettings` alone has **28 invocation sites across 21 files** plus a
README teaching site at `:320-323`. Deleting them is a downstream compile break
in the same release that already ships a silent behaviour change to every
partial literal; that is two migrations at once, for no gain. So:

- `withSymexSettings` → `{.deprecated: "SymexSettings(...) partial literals now
  carry the defaults".}`. The deprecation message *teaches the new idiom at
  every remaining call site*, which is the cheapest documentation this RFC can
  buy. Migrate opportunistically; remove at the next major.
- `+` → deprecated, **bodies left as they are**. Round 2 verified it has
  **zero production callers**: the only call of `ResourceBudget.+` is inside
  `SymexSettings.+` (`smt/types.nim:2998`), and the only calls of
  `SymexSettings.+` in the entire tree are three tests *of the operator itself*
  (`tsymex_phase15_z3_infra.nim:86`, `tsymex_phase15_R1a_ir.nim:118`,
  `tsymex_phase16_R16_1_arithcheck_foundation.nim:137`). The doc comment's
  justification — "lets per-cluster overrides compose" — describes a composition
  that has never happened. Building a generic recursive `merged` plus a
  generative algebraic-law suite for an operator with no users is investment in
  a corpse; round 1 proposed exactly that and round 2 withdraws it. What is kept
  is one cheap forgotten-field pin, because a *deprecated* operator still rots
  silently when a field is added.
- `resolved()` → retired at C1 once `IntegerBiasConfig` carries defaults; keep
  the symbol as a deprecated identity function for one release.

The rejected alternatives, for the record:

- **Proc default parameters** (the `OrchestratorPolicy` answer) — genuinely
  gives named args, real defaults and zero-fill immunity, but duplicates every
  default in a second location (signature vs. type), which is
  `ResourceBudget.+`'s disease in a new organ; leaves the poisoned literal legal
  beside it; and doesn't compose into nested types, `default(T)`, `newSeq` or
  `const`.
- **`Option[T]` fields** — immune, but taxes every literal and every read; and
  the `distribution.nim` comment already rejected it once on call-site cost.
- **Mutator builder** — imperative where the config is declarative, doesn't
  nest, and its one advantage (perfect set-vs-unset knowledge) is matched by
  literals once defaults exist.
- **Bare `{.requiresInit.}` without defaults** — forces all 17 fields at every
  site; punitive.
- **Library-shipped presets or a scoped-override block** — unnecessary. `with`
  accepts an arbitrary expression (`dsl.nim:36-39`), so `const quick =
  Settings(maxExamples: 10)` … `with quick` already works today, and deriving
  one preset from another is `var s = quick; s.seed = 7`. Any preset API would
  re-introduce a second construction path beside the literal, which is the
  two-path mental model that caused the defect. C3a documents the
  preset-as-`const` idiom in one README paragraph instead.

### Residual design questions (recommendations, not forks)

- **`{.requiresInit.}`?** *Recommend: not in round A.* Field defaults already
  make the documented path *safe*, which satisfies the done-condition. The holes
  it closes (`var s: Settings`, `array[N, Settings]`, `reset`) have exactly two
  live occurrences in the tree, both in
  `tests/tsymex_phase14_b2_forcephases.nim:21,25`. Revisit as an independent,
  reversible follow-up slice; weigh it against the `newSeq` warnings and this
  toolchain's history of init-analysis front-end bugs.
- **`defaultSettings()`'s end state.** *Recommend: one name per surface — the
  type.* A `defaultX()` standing beside a now-safe `X()` is exactly the folklore
  that taught eight modules to invent `defaultResourceBudget`,
  `defaultIntegerBias`, `lawSettings` and `orchestratorPolicy()`. A2 flips the
  **nine** in-`src` default-parameter positions (`engine.nim:210,220,228,243`,
  `metamorphic.nim:29,43,56`, `symex.nim:426,463`) to `= Settings()` so the
  library demonstrates its own thesis. (Rounds 1 and 2 both wrote "twelve"
  while listing nine; the sites above are the complete set, counted at
  implementation.) There is a **tenth**, which neither round listed because it
  is not a default parameter: `dsl.nim:37` emits `newCall(bindSym"
  defaultSettings")` as the settings expression for a `property` block with no
  `with` clause, so it is the construction every DSL user gets by default. The `{.deprecated.}` pragma itself waits
  one release — deprecating a public symbol in the same release as a silent
  behaviour change is two migrations at once. Same disposition, one release
  later, for `defaultSymexSettings()` (~180 mechanical sites) and
  `optimisedSymexSettings()` — the latter is **already byte-identical to
  `defaultSymexSettings()`** since `isOptimised` became the default at the
  Phase-2 endpoint, while its doc comment still says the flip is pending.
  Fixing that stale comment is a C3a line item. `looseSymexSettings` stays: it
  is a genuine non-default preset.
- **`BmcSettings` defaults.** Needs chosen values, not just a mechanism. Pick
  during C2 and document them in the type. One constraint to record now: these
  defaults bound a *verification claim* — `bmcVerified` means "holds to depth
  `maxDepth`" — so the chosen depth changes what a green run asserts, and the
  doc comment C2 rewrites must say so. For `maxStates` specifically, weigh the
  ADR-0031 answer (0 = unlimited) against a finite default, since `bmc.nim:86`'s
  `explored >= maxStates` makes 0 the worst possible sentinel today.

## §5 — Scope

**In scope.**

1. **Field defaults on six surfaces** — `Settings`, `IntegerBiasConfig`,
   `SymexSettings`, `ResourceBudget`, `BmcSettings` (a live defect found in
   round 1) and `OrchestratorPolicy` (taxonomy row 7, found undisposed in
   round 2: §4 rejects its mechanism for new work, so leaving the existing
   instance untreated while §9 argues against exactly that would be incoherent).
2. **Deprecate** `withSymexSettings`, both `+` operators and `resolved()`, per
   §4. Not delete — see §5.6.
3. **Record the ADR-0031 family and `ConcolicAssist` as conforming via
   zero-is-correct**, and pin them. This replaces round 1's "exemption" framing
   per §0's invariant.
4. **Fix the docs that teach the idiom**: `README.md:33` and `:241`,
   `README.md:320-323` (which teaches `withSymexSettings`, the proc §5.2
   deprecates — round 1's doc list missed it), `docs/fuzz/INTERFACE.md:243-245`,
   `docs/fuzz/USAGE.md` (safe by design — pin as safe rather than "fix"),
   `bmc.nim:50` and `fuzz.nim:889`'s doc comments, and
   `examples/symex_loops.nim:60-63`, which **does not compile** (it sets
   `queryRLimit`/`maxFrontierSize`/`maxCallDepth`/`maxLoopUnwind` flat on
   `SymexSettings`; they moved onto `ResourceBudget` at CR-9(b)). Round 2
   compiled all six examples in the container: that one file is the only
   breakage, so round 1's single-file claim was exactly right.
5. **Stage the test-suite behavioural fallout** (§6 round A) — this is the real
   cost, and it is the opposite of the one the seed feared.
6. **A downstream audit, CHANGELOG entry and version decision** (§6 C5),
   following `docs/rfc/0004-z3-optional.downstream-audit.md`. **Correction to
   round 1:** its "no compile breaks" claim is true of the *defaults flip* and
   false of the *deprecations riding in the same RFC* — deprecation warnings are
   not breaks, but the audit must clear all four public symbols before any of
   them is removed. The audit's hard part is 0004's §4 — "behaviour change with
   no compile error" — which for 0010 is nearly the whole document.

**Out of scope.**

- Field-level strategy annotations on derived types (e.g. `age: integers(0, 150)`
  inside an object). Real want, different mechanism, its own RFC.
- **Cross-field coherence validation** (§2's tenth item). Separate axis,
  separate mechanism, three incompatible existing styles, and one dead exported
  validator to dispose of. Candidate future RFC. C3a spends one line deciding
  whether `validateSymexSettings` gets wired into the `runSymex` entry points or
  deleted; a validator that never runs on a real configuration is this RFC's own
  pattern sitting inside the RFC that exists to end it, and zero lines is the
  wrong number to spend on it.
- **A Linux CI leg.** Round 2 found there is none — the four workflows are
  `fuzzer-msvc`, `fuzzer-mingw`, `symex-mingw`, `tianguis-publish`, and
  **nothing in CI runs `nimble test`**. That is a real gap and it is why
  `examples/` rotted, but adding a CI leg is a repo-topology decision with a
  standing cost, well outside a config-discipline RFC. C3c does what can be done
  from inside this RFC (a compile gate on an existing leg) and records the rest.

**In scope, but quarantined to round D — see §8.** The seed's §3 items 3
(`given x: int`) and 4 (the `derive.nim:511` error message). They stay in this
RFC but never ride inside a config slice's blast radius.

## §6 — Slice plan

Staged **pin-then-flip**: make today's implicit values explicit first (a no-op),
then flip the defaults, so the behavioural fallout is drained in advance rather
than discovered as a red sweep.

Round 2 rebuilt this section against the actual files. Round 1 authored the
staging, which is sound; almost every *inventory* in it was wrong.

**Round A — `Settings`.**

- **A0 — a runnable sweep.** *Prerequisite, not optional.* A2's verification
  says "run the full PBT sweep"; **no such command exists**. `scripts/psweep.sh`
  sweeps only `tests/tsymex_*.nim`; `nelli.nimble`'s `test` task is a single
  serial loop over ~257 suites that includes the six `tsymex_r6_*` Linux
  hangers, so it never finishes in the container. Add a parallel runner over the
  nimble list minus the known hangers. Without this the implementing agent
  improvises a sweep mid-slice, under pressure, in the one round whose entire
  purpose is detecting behavioural fallout. *Blast radius: `scripts/`.*
- **A1 — pin the implicit zeros.** Write today's implied values explicitly into
  the at-risk literals. Round 1's file list was part wrong and part short:
  `tshrinker.nim` and `tvariantbind.nim` contain **zero** `Settings(` literals
  and call `forAll`, which already defaults to `defaultSettings()`
  (`engine.nim:210`) — A2 cannot change their behaviour; drop them. The
  remaining named files hold **63** literals, not ~40 (tengine 13, ttarget 9,
  tdb 6, tnested 6, tcovguided 6, treporter 6, tevents 5, tdisplay 5, texplain 3,
  tautolabels 3, tfrequency 1, `laws.nim` 1). Split:
  - **A1a** — output/event suites (tdisplay, treporter, tevents, texplain,
    tautolabels, tnested, tfrequency): `printEvents: false, autoLabels: false`.
  - **A1b** — engine suites (tengine, tdb, tcovguided, ttarget) plus
    `laws.nim:35`: add `useSA: false` in tcovguided/ttarget, `flakyRetries: 0`
    at `tengine.nim:28,42` where `r.notes.len == 2` is asserted after
    falsification, and `autoLabels: false` in `laws.nim`.
  - **A1c** — the **13 files round 1 never listed**, holding **52 more
    literals** (tpipeline 10, tmetamorphic 6, tengine_corpusreplay 6, tdeadline
    6, tengine_crashisolation 5, tbias 4, tfuzzcovcorpus 3, texamples 3,
    treservedlabel 2, tparallelcheck 2, tdbbackends 2, tbundles 2, tdsl 1).
    Most are workaround-style — they already set `flakyRetries`/`maxShrinks`/
    `maxRejections` explicitly, which independently confirms round 1's
    "the authors knew" thesis — so only `printEvents`/`autoLabels` flip there.
    Either pin them or make the per-vector safety argument explicitly; do not
    leave them unmentioned.
  - Also land the seed's characterization test here — the one asserting the
    literal and the defaults *differ*. It is green now and goes red at A2, which
    is what a characterization test is for; A3 deletes it. This is what keeps
    the defect under observation from slice 1 (see §7).
  *Blast radius: `tests/` + one `src` file, zero behaviour.*
- **A2 — the flip.** RED, in `tests/tconfigdefaults.nim`: **(a) structural** —
  `Settings(maxExamples: 7)` equals defaults-with-that-override field by field,
  plus pins for `const`/VM evaluation and `newSeq`; **(b) behavioural, through
  the real entry point** — the README's verbatim `Settings` literal run through
  `forAll` yields `auto.*` keys in `report.events.categorical`,
  `report.printEvents == true`, and — against a filtered probe strategy —
  `otPassed`, not `otExhausted`. Round 1 specified only (a), while §7 claimed
  the property ran end-to-end; **(b) is what makes §7 true**, and it is not
  redundant with (a), because an adapter can sit between the literal and the
  engine — `phases.nim:260` applies `resolved()` today, entirely invisible to
  any `==` on `Settings`. GREEN: field defaults in `engine/types.nim`;
  `defaultSettings()` body becomes `Settings()`; the nine in-`src`
  default-parameter positions become `= Settings()`, and so does `dsl.nim:37`'s
  macro-emitted default (see §4). Note the unstated
  dependency round 1 missed: `defaultSettings()` includes
  `integerBias: defaultIntegerBias`, and C1 is a round later, so A2 must declare
  `integerBias*: IntegerBiasConfig = defaultIntegerBias` (const-symbol field
  defaults are legal — probed) and pin it. `resolved()` stays live and harmless
  between A2 and C1. **Register the new file in `nelli.nimble`** and in the
  fuzzer legs' named contract lists — round 2 found it would otherwise run in no
  sweep and no CI: the nimble task is hand-maintained, `symex-mingw` takes only
  `tsymex_*` names, and the fuzzer legs glob `^(tfuzz|tdb|tengine_)` plus a named
  list. *Blast radius: `engine/types.nim` + one new test + `nelli.nimble` + two
  workflow lists.* Run A0's sweep and `scripts/dt-crosswin.sh`.
- **A3 — un-pin where the default was actually wanted.** Mechanical
  done-condition, so this is a slice and not an open-ended cleanup: *for every
  pin A1 added, either delete it (the suite stays green and still tests what it
  meant to test) or keep it with a one-line comment saying why; done = zero
  unjustified pins, sweep green.* Delete the characterization test here.

**Round B — symex** (a round, not a slice).

- **B1 — pin the const literals.** The inventory is **10 literals across 7
  files**, not 6 (`tsymex_g1b_concolic` 2, `tsymex_phase13_acceptunknown_guard`
  2, `tsymex_phase13_unknown_roundtrip` 2, `tsymex_phase13_layer1_wire` 1,
  `tsymex_phase13_rlimit` 1, `tsymex_phase7_assertcovered` 1, `tsymex_r4_strip`
  1). Two corrections that make B1 real rather than nominal:
  - **Four of those seven files are dark** — `tsymex_phase13_rlimit`,
    `_layer1_wire`, `_acceptunknown_guard`, `_unknown_roundtrip` appear nowhere
    in `nelli.nimble`, so they run in no sweep and no CI, and `symex-mingw`
    derives its corpus from that task. This is the `examples/` rot mechanism
    (§5.4) *inside the test suite*. B1 registers them. Both of the two that
    round 2 ran pass today; expect a surprise on their first Windows run.
  - **The pin list was incomplete.** Round 1 named `arithChecks: {}`,
    `defectExclusions: {}`, `inlinePolicy: ipAlwaysInline`. But every one of the
    ten literals writes a *partial* `ResourceBudget` listing only
    `queryRLimit`/`maxFrontierSize`/`maxCallDepth`/`maxLoopUnwind`, so B2 also
    flips nine omitted nested fields from 0 to `maxHeapDepth` 8,
    `maxFreshnessAssertions` 256, `maxClosureInlineCount` 64,
    `maxInstantiationsPerProc` 64, `maxSplitParts` 8, `maxBytesEncodingLen` 32,
    `seqInlineThreshold` 8, `maxVariantConstructorForks` 8,
    `maxVariantConstructorFieldAllocs` 64 — where **0 is documented as
    unlimited** (`smt/types.nim:1656`) and all nine are in the cache key
    (`canonicalize.nim:3948-3953`). As round 1 specified it, B1 was not the
    promised no-op and B2 was not a pure flip. Pin all twelve.
  Two parts of round 1's B1 do hold: all ten literals set `integerSemantics`
  explicitly (zero-fill would otherwise flip `isExact` → `isOptimised`), and
  `acceptUnknownAsCovered`'s zero equals the post-flip default.
- **B1b — per-site review.** *Its own ledger row*, because it changes behaviour
  where B1 does not, and the F5 fields make "should this site get the real
  defaults?" a genuine judgement (`maxHeapDepth: 0` means unlimited today).
  Separate commits where results change. Not a sweep. A stall here should be
  visible as a stalled slice, not hidden inside B1.
- **B2 — flip `SymexSettings` + `ResourceBudget`** to field defaults. Verify
  with `tsymex_canonicalize`, `tsymex_phase15_CR2_cachekey` (the key-stability
  oracle — name it explicitly even though this is not a version bump) and the
  seven affected suites. **Confirmed at source:** `canonicalize` folds every
  verdict-relevant field into `symexCacheKey` (`canonicalize.nim:3873-3958`), so
  a site whose effective settings change gets a *new* key and a cold recompute —
  there is no path for silent stale reuse — and `defaultSymexSettings()`'s
  values are unchanged, so pins built from it keep their keys. This is **not** a
  `symexWalkerVersion` bump. One consequence round 1 missed, for the audit:
  symex witnesses are **persisted** into `ExampleDatabase` under that key
  (`symex.nim:210,236`), so a downstream with partial-literal settings and a
  witness DB silently loses reachability of its stored witnesses — they go dark
  and are re-solved, not reused-wrong. In-tree this is drained by B1.
- **B3 — deprecate the merge and pin it.** GREEN: `{.deprecated.}` on
  `withSymexSettings` and both `+` operators, bodies unchanged, per §4. Keep two
  pins so a deprecated-but-live operator cannot rot silently: (i) a
  forgotten-field pin driving **all thirteen `ResourceBudget` fields *and* the
  five top-level `SymexSettings` fields** non-default — round 1 said "thirteen",
  which covers only the budget; (ii) a **nested-composition** pin — `a` and `b`
  each setting a *different* single budget subfield, asserting both survive.
  Round 1's spec would have passed under a whole-object merge that silently
  drops one side's nested overrides, which is exactly the bug a naive
  `fields()`-based rewrite would have introduced. Migrating the 28
  `withSymexSettings` sites is *not* in this slice — deprecation is precisely
  what lets that happen opportunistically instead of as an unscheduled round.
  *Blast radius: `smt/types.nim` + one test.*

**Round C — periphery.**

- **C1 — `IntegerBiasConfig` field defaults**, retire `resolved()`. *Three
  modules, not two* — `datasource/distribution.nim`, `engine/phases.nim:260`
  and `fuzz.nim:2028` — so it is the one slice that falsifies the two-module
  note below, while remaining genuinely slice-sized. Two consequences round 1
  never stated: (i) **the defaults recurse into the conforming-by-zeros
  surface** — `FuzzSettings` embeds `integerBias` (`fuzz.nim:371`), so after C1
  `FuzzSettings()` is no longer all-zero. Behaviour is preserved end-to-end
  (`resolved(zero)` produced the same values at use), `tfuzzconfigdefaults.nim`
  asserts nothing about `integerBias` today so nothing reds, and the fix is to
  say so and extend the pin. (ii) An *explicit* all-zero `IntegerBiasConfig`
  literal changes meaning — today rescued to defaults, afterwards honoured as
  the degenerate config `distribution.nim:56-59` documents. That is the correct
  behaviour and it is the C1 RED test: **zero-survival, not
  omission-equivalence**. Omission-equivalence is already **green today** via
  the sentinel — round 1 would have written a test that passes before and after.
- **C2 — `BmcSettings`** — choose defaults (§4's residual note), fix the doc
  comment, RED on the instant-`bmcExhaustedBudget` path. All twelve existing
  `BmcSettings` literals set both fields, so no in-tree fallout.
- **C3a — docs.** README `:33`, `:241`, `:320-323`; `docs/fuzz/INTERFACE.md:243`
  and `USAGE.md` pinned as safe; `bmc.nim:50` and `fuzz.nim:889` doc comments;
  `optimisedSymexSettings`'s stale comment; the preset-as-`const` paragraph
  (§4); the one-line disposition of `validateSymexSettings` (§5).
  Criterion: living teaching docs get pins, historical phase-15 and plan docs
  are left alone.
- **C3b — repair `examples/symex_loops.nim`.** One file, one-line scale; the
  other five examples compile clean.
- **C3c — a compile gate for `examples/`.** Its own slice because it crosses the
  platform fork. State honestly what is achievable: adding examples to the
  nimble task yields **zero** CI coverage, since nothing in CI runs `nimble
  test`. Real coverage means a compile-only step on an existing Windows leg, or
  a local script plus an explicit statement that examples are locally gated
  only. Do not silently claim CI coverage that does not exist — that claim is
  what let `symex_loops.nim` rot.
- **C4 — `OrchestratorPolicy`** field defaults, doc-comment flip
  (`fuzz.nim:889`), and `orchestratorPolicy()` reduced to a deprecated shim.
  Note it is genuinely production-called today as a default parameter value
  (`fuzz.nim:1234,1268,1953`), so the constructor stays until the deprecation
  window closes.
- **C5 — downstream audit, CHANGELOG, version decision.** Round 1 put this in
  scope (§5.6) and gave it no slice. Following the 0004 model, it must contain:
  runnable grep specs for `Settings(` / `SymexSettings(` / `ResourceBudget(` /
  `BmcSettings(` / `IntegerBiasConfig(` / `OrchestratorPolicy(` literals; the
  per-surface field delta table (§1's table, generalised) — which doubles as the
  **only** practical detection aid, since after the flip the language erases
  set-versus-unset at runtime and no discovery mode is possible; the intent
  triage recipe (A1's pin procedure, exported as "if you meant the zeros, write
  them *before* upgrading"); the `var s: Settings` divergence note (a bare `var`
  still zero-fills, so a literal and a `var` of the same type now disagree — a
  new reader trap); B2's witness-key flush; and a re-dated re-check of 0004's
  amoxtli clearance. Gate: before tag.

**Round D — the two riders.** See §8. Two independent one-module slices:
**D1** `given x in int` (`dsl.nim:59-68`), **D2** the `derive.nim:511` error
message. May not start until round A is green; blocks nothing.

**Verification budget.** A0 makes the sweep runnable at all. None of the ten
symex literal sites is in the six `tsymex_r6_*` suites that hang on
Linux/podman, so the symex surfaces are fully locally verifiable. Branch must be
named `rfc-0010-*` or the three Windows legs never trigger. Don't run the same
test file concurrently (shared-binary clobber). Field defaults and `fields()`
are front-end/compile-time, so no msvc/mingw/gcc codegen divergence is expected
— run `fuzzer-msvc` anyway.

**Blast-radius note.** After round 2's corrections: A1 is a round split into
A1a/A1b/A1c; B is a round; C1 spans three modules; C3 is split into three;
everything else is slice-sized. Round 1's blanket "no slice spans more than two
modules" was true only because the work it omitted was unassigned.

## §7 — Liveness and definition of done

**Load-bearing property:** *any literal, `default(T)`, `const`, `newSeq`, `new`
or nested-field construction reachable through a documented entry point behaves
identically to that surface's defaults in every field not explicitly listed.*

The quantifier is scoped deliberately. Round 1 wrote "any settings
construction", which is **falsified by a fork this RFC has already closed**:
`var s: Settings` zero-fills (§3) and stays legal because `{.requiresInit.}` is
deferred, so the universal claim is untrue after A2 and untestable by any suite.
**Residual, recorded:** bare `var v: T`, `array[N, T]`, `reset(x)` and
never-assigned proc results still zero-fill; live occurrences are two, both in
`tests/tsymex_phase14_b2_forcephases.nim:21,25`; the deferred `requiresInit`
slice is that hole's designated closer. Verified separately: no settings type is
serialized or crosses the fuzzer worker process boundary
(`workerproto.nim`/`fuzzworker.nim`/`serialize.nim`/`parallel.nim` reference
none of them), and nothing in the tree parses settings from JSON, TOML, CLI
flags or the environment — so B2's persisted witness key is the *only*
settings-derived persistence in the tree.

Behavioural, at the entry point — not a unit test on a merge function, because
the defect lives in whether the documented idiom routes through the mechanism at
all. All five in-scope surfaces admit an end-to-end behavioural test; none is
structural-only. The entry points are `forAll` (`engine.nim:209`) and
`property`/`with` (`dsl.nim:36-43`) for `Settings`; the `static SymexSettings`
macros (`symex.nim:1092,1197,1228,1284`) for `SymexSettings`/`ResourceBudget`;
`Settings.integerBias` → `phases.nim:260` → `drawInteger` for
`IntegerBiasConfig`, made deterministic by probing with `boundaryPercent: 100,
shrinkTowardsWeight: 100` so no statistical assertion is needed; and `bmcCheck`
(`bmc.nim:110`) for `BmcSettings`.

**What the DoD can and cannot assert.** Per-field *behavioural* equivalence is
not feasible in general — observing `flakyRetries` requires a flaky property,
`maxShrinks` a shrink-bounded run. The honest criterion, and the one A2 ships,
is **structural equality on every field, plus behavioural spot-checks through
the entry point for the headline symptoms**. §3 verified that structural
equality is sound here: all five types are flat value types with no floats,
refs, procs or Tables. Round 1's "behavioural equivalence on every unlisted
field" was unfalsifiable as written.

**The producer is scheduled first — with one deliberate exception, recorded.**
A1 is a pure no-op pin, so slice 1 of this RFC produces nothing live, and A2 is
the first live slice. That tension is real and pin-then-flip wins it anyway:
flipping first would buy slice-1 liveness at the cost of a red sweep across two
dozen files that conflates behavioural fallout with the mechanism and destroys
A2's bisectability. The mitigation is that A1 lands the characterization test,
so the defect is **under observation** from slice 1 even though the fix is not
yet live.

**Every in-scope surface's DoD assertion has an owning slice.** Round 1 named
one file in one slice and then required it to cover all five surfaces. Explicitly:
A2 owns `Settings`; B2 extends the symex file; C1 owns `IntegerBiasConfig`
zero-survival; C2 owns `BmcSettings`; C3a owns the conforming-by-zeros pins.

**Two files, not one.** `tests/tconfigdefaults.nim` (Settings,
IntegerBiasConfig, BmcSettings, the conforming-by-zeros pins) stays **Z3-free**;
`tests/tsymexconfigdefaults.nim` carries SymexSettings, ResourceBudget and the
merge pins. Round 1's single file would have imported the symex stack and made
the definition of done Z3-linked, undoing for that file exactly what RFC-0004
made true of `import nelli`, and restricting it to one of the three Windows
legs. Neither file lands in the six `tsymex_r6_*` hangs.

**Red/green direction, stated per surface**, because round 1 caught the seed
asserting the wrong direction and then inherited a milder version of it:
Settings structural **red**; Settings behavioural **red**; `const`/`newSeq`
pins **red**; SymexSettings/ResourceBudget equivalence **red**; BmcSettings
**red**; the conforming-by-zeros pins **green by design**, correctly framed as
pins; the merge pins **green today** (both `+` bodies currently cover every
field) and correctly framed as regression pins, not acceptance tests; and
`IntegerBiasConfig` **omission-equivalence green today** — the sentinel already
works for the omission case — so C1's RED must be **zero-survival** instead.

**The seed's §5 acceptance criterion was inverted and is replaced.** It proposed
a test asserting the two constructions *differ*, and called it "red today". The
behaviours **do** differ today, so that test is **green** now and would go
**red** on success — it is a characterization of the bug, not an acceptance
test. A1 writes it as exactly that; A3 deletes it.

**Done:** two commands — `scripts/dt-bounded.sh c tests/tconfigdefaults.nim` and
`scripts/dt-bounded.sh c tests/tsymexconfigdefaults.nim` — pass suites that, for
each in-scope surface, take that surface's documented partial-construction idiom,
run it through the surface's real entry point, and assert structural equality on
every unlisted field plus the surface's headline behavioural observable;
**plus** the README's verbatim `Settings` literal, run through `forAll`, yields
`auto.*` keys in `report.events.categorical`, `report.printEvents == true`, and
`otPassed` rather than `otExhausted` against a filtered probe (named as `Report`
fields, not as stdout — the README example itself cannot run verbatim, since it
references a user-defined `roundTrip`); **plus** the conforming-by-zeros
surfaces (`FuzzSettings`, `ExecutorConfig`, `GuidanceConfig`,
`SchedulingConfig`, `ConcolicAssist`) pinned as *deliberately* agreeing, so the
suite records which implementation of §0's invariant each surface uses.

Make that registry self-checking rather than descriptive, using §3's own rows —
one assertion shape covers both conforming implementations, and a surface added
later cannot satisfy neither without failing:

```nim
proc conforms[T](documented: T) =
  var z: T                          # zero-filled (§3)
  check default(T) == documented    # T() IS the documented default
  # z == documented  → conforms via zero-is-correct (ADR-0031 family)
  # z != documented  → conforms via declared field defaults
```

## §8 — The two riders: round D (decided)

The seed's §3 bundled two items that share no file, mechanism or root cause with
zero-fill construction:

- **item 3** — `given x: int` implicit `arbitrary(T)` in the DSL.
- **item 4** — the vague `derive.nim:511` fallback error.

All five review lenses independently flagged these as scope creep.
`SEED-SET-2026-09-03.md:44` records the bundling as a deliberate composition
decision ("merges the ergonomics items under one root cause"), which is true of
items 1–2 and not of 3–4 — so the split was escalated rather than made silently.

**Decided 2026-09-04 (Corey): they stay in this RFC as an explicitly separate
trailing round D, never interleaved with A/B/C.** Both are one-module,
independently green slices — too small to justify their own RFC, but they must
not ride inside a config slice's blast radius, and a reviewer of an A/B/C slice
must never have to context-switch into macro hygiene to judge it. Round D may
not start until round A is green; it shares no dependency with A/B/C in either
direction, so it can equally be deferred indefinitely without blocking anything.

One correction that governs item 3's slice: it is **not** "mechanical in
`dsl.nim:60-70`".
The parse loop requires `nnkCommand(given, nnkInfix(in, x, s))` and hard-errors
otherwise (`dsl.nim:59-68`); `given x: int` parses as the `cmd arg: stmt` form —
a different AST shape — and `given x: int, y in lists(...)` does not parse as
intended at all, because the colon swallows the remainder. The genuinely
mechanical variant is **`given x in int`**: accept a typedesc RHS and wrap it in
`arbitrary(...)`, preserving the single AST shape and mixed bindings.

## §9 — Why bother with an RFC for this

Because the nine existing answers show that patching the field in front of you
produces exactly this state — and the reviews kept finding more of them:
`BmcSettings`, whose documentation *teaches* the hazard; `OrchestratorPolicy`,
whose documentation *diagnoses* it and then leaves the literal poisoned;
`ConcolicAssist`, which coerces zero out of existence; ten literals inside the
symex test suite; four test files that run in no sweep at all; and one example
that stopped compiling with nobody noticing. The fix worth making is the general
one, and §0's invariant is the part that has to outlive the repairs — otherwise
surface twelve arrives next quarter with a tenth bespoke answer.

That the general fix costs zero call sites is this work's best news. That it
changes the behaviour of 115 existing test literals is its real cost, and §6
stages it.
