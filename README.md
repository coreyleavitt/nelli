# proptest

Property-based testing for [Nim](https://nim-lang.org), built on an internal
**choice-sequence** engine — the same architecture that powers Python's
[Hypothesis](https://hypothesis.works). Generators are parsers over a recorded
sequence of typed primitive choices, so **shrinking is automatic, composable,
and survives `map` / `filter` / `flatMap`** — no hand-written shrinkers, ever.

> **Name note:** there is a well-known Rust crate also called `proptest`. This
> is the unrelated Nim library — search "proptest nim". Different ecosystem,
> no conflict.

```nim
import std/[unittest, algorithm]
import proptest

suite "list properties":
  property "reversing a list twice is the identity":
    given xs in lists(integers(0, 9))
    ensure xs.reversed.reversed == xs

  property "addition commutes":
    given a in integers(-50, 50), b in integers(-50, 50)
    ensure a + b == b + a

  # Custom Settings (DB persistence, fixed seed, smaller budget for a
  # finite input space, etc.) opt-in via `with` as the first body line.
  property "reserved-keyword names round-trip":
    with Settings(maxExamples: 7, seed: 42,
                  testId: "kdl-keywords", dbPath: ".proptest-db")
    given keyword in sampledFrom(["true", "false", "null", "inf", "-inf", "nan", "0"])
    ensure roundTrip(keyword) == keyword
```

That compiles. That runs. That **shrinks**. And `nimble test` reports the
results natively. Inline value-dependent rejection lives in the property
body via `assume(cond)` (see "Inline rejection" below).

## Why

Nim's existing property-testing options are QuickCheck-style — a generator
paired with a separate, hand-written shrinker — and either don't shrink or
break shrinking the moment you compose generators. `proptest` takes the
modern approach instead: a `Strategy[T]` only *draws* primitives from a
`DataSource` that records every draw; the shrinker minimizes that recorded
sequence and re-runs the generator. Shrinking is a property of the recording,
not the type.

## What's in the box

### Engine + IR
- **Choice-sequence engine** with a typed IR (`int`/`float`/`bool`/`bytes`/`string`),
  recording, replay, overrun handling, and spans. Reproducibility lives in the
  recorded sequence, not the seed.
- **Owned 128-bit integer primitive** (`Int128`) so every native Nim integer
  type — including the full `uint64` range — round-trips losslessly.
- **All five primitive draws** with **distribution biasing**: small-magnitude
  bias around `shrinkTowards`, boundary injection (`0`, `±1`, `min`, `max`,
  `NaN`, `±Inf`, `±0`), and **swarm testing** with replay-deterministic mute
  masks in `oneOf`.

### Strategies
- **`Strategy[T]` combinators** — `just`, `map` (unary functor **and** the
  variadic applicative product: `map(sa, sb, sc)` → `Strategy[(A, B, C)]`,
  `map(sa, sb, sc, f)` applies `f` to the drawn values — no intermediate
  tuple; trailing-`do`-block form supported), `filter` (+`Rejection`),
  `flatMap`, `oneOf`, `sampledFrom`, `sampledFromWhere` (eager-filter for
  finite corpora), `recursive`, and `displayWith` (custom counterexample
  renderer; sugar `mapWithDisplay` / `flatMapWithDisplay` attaches the
  new-`T` renderer in one call).
- **Built-in strategies** — `integers`, `booleans`, `floats`, `lists`
  (element-at-a-time → cheap deletion shrinking), `strings` (ASCII default
  + `strings(intervalSet, …)` overload for arbitrary Unicode), `tables`,
  `sets`, `enums` (handles holes), weighted `integers(weights = …)`.
- **Inline rejection shortcuts** — `assume(cond)` for post-draw filtering;
  `assumeOk(expr)` / `assumeSome(expr)` for the recurring `assume r.isOk;
  r.get` pattern (duck-typed on `.isOk`/`.isSome` + `.get`).

### Runner + reporting
- **Property runner** — `forAll` returns a deterministic `Report` carrying
  `outcome`, `counterexample: Option[T]`, `choices`, `seed`, `paretoFront`,
  `dbReplays`, `notes`, `events`, `necessity`, `displayed`, `partialWitness`
  and `divergingOp`; two-layer flakiness detection;
  **crashes (`Defect`s like `IndexDefect`) caught as falsifications**.
- **`renderReport(r, format)`** — `OutputFormat = ofText | ofJson | ofJunit |
  ofGithubAnnotation` for CI tooling.
- **`note(label, value)`** for debugging long chains — attaches
  `(label, $value)` pairs to the current example; the *shrunk*
  counterexample's notes appear in `Report.notes` and DSL checkpoints.
- **`event(label)` / `event(label, numericValue)`** — cross-example
  accumulators (categorical counts + min/max/mean/p50/p90/p99 numeric
  summaries) for distribution observability.
- **`Settings.autoLabels`** (#108) — built-in strategies emit distribution
  labels under the reserved `auto.` prefix (`auto.int:near-lo`,
  `auto.list-len:empty`, …). Combined with `Report.events.categorical` you
  get free histograms of which corners of the input space your generators
  actually visited — without writing a single `event` call.
- **`explain` phase** (M10) — perturbs each `ChoiceNode` after shrink and
  annotates `Report.necessity[i]` as `nNecessary` / `nFree` so `repro()`
  shows which choices the failure actually depends on.
- **Shortlex shrinker** — per-kind passes for integers, floats, bools,
  bytes, strings; span-directed deletion; fixpoint with a budget; public
  `sortKeyLess` for explicit shortlex comparison.

### DSL
- **`given` DSL** — `property "name": given a in sa, b in sb, …: ensure …`
  with arbitrary arity, expanded to a `std/unittest` `test` block. Optional
  `with mySettings` clause as the first line of a property body opts into
  DB integration, a custom seed, or any other `Settings` field. Optional
  `examples <expr>` clause (M10) pins user-supplied regression seeds that
  run before the random phase.

### Auto-derivation
- **`arbitrary(MyType)`** synthesizes a strategy for primitives (every
  native int/uint family member, `float`/`float32`, `bool`, `char`, `byte`,
  `string`), `Option[T]`, `seq[T]`, fixed `array[N, T]`, `Table` /
  `HashSet` / `set[T]`, tuples, plain objects (any field types), enums
  (with holes), ref objects, object variants (with single- or multi-field
  branches), generic instantiations (`Box[int]`), `distinct U`, **and
  directly-recursive types** (variant trees, linked lists, JSON-AST shapes
  with `seq[Self]`) which auto-emit `recursive(base, extend, 4)` with a
  synthesized leaf. Mutual recursion is detected at compile time and
  points at the manual `recursive(...)` combinator.
- **Refinement types** (#111) — `arbitrary(range[1..10])`, `Natural`,
  `Positive`, and any user `range[lo..hi]` type derive directly. The
  generated strategy is `Strategy[R]` (the refinement type), not
  `Strategy[BaseInt]` — so the constraint flows through subsequent
  `map`/`flatMap` calls without manual casts.
- **`proptest/derive/detect`** (#104) — recursive-type detection helpers
  (`RecursionKind` verdict) are a public, separately-testable seam under
  the `arbitrary(T)` macro.

### Example database
- **`<dbPath>/<safeKey>.bin`** per test id, atomic write, multi-entry
  primary corpus with LRU + dedup, stale entries auto-pruned on next run,
  secondary corpus of high-scoring non-failures so targeted PBT resumes
  across runs.
- **Closure-record `ExampleDatabase`** with factories `directoryBasedDatabase`,
  `inMemoryDatabase`, `multiplexedDatabase(local, shared)`,
  `readOnlyDatabase(inner)`; new `forAllUsing(db, …)` entry point; DB
  errors flow through `Report.dbErrors` (or short-circuit on
  `Settings.strictDb`).

### Stateful testing
- **Rule-based state machines** with `initial: Strategy[S]` (use `just(value)`
  for a fixed seed, any strategy for a varying one — `arbitrary(S)`,
  `sampledFrom(corpus)`, etc.) and an optional per-step `invariant` (catches
  transient mid-sequence violations final-state checks would miss); model
  comparison falls out of the same mechanism. The initial state is part of
  the recorded choice sequence so the shrinker minimizes it alongside the
  rule selections.
- **`Bundle[S, V]`** (M10) — typed value-flow between rules with
  auto-precondition when the pool is empty; consumed index is shrinkable.
- **Symbolic refs** (#109) — `producingRule[S, A, V]` returns a value into
  a typed promise store under `(name, occ)`; `consumingRule[S, A, V0]` (and
  arity-2 variant) takes a `SymRef[V0]` and is auto-disabled until the ref
  is fulfilled. Identity-preserving, dependency-respecting shrinking with
  no shrinker work — orphan consumers hit the runtime predicate after a
  producer is deleted from the plan. Coexists with `Bundle`.

### Beyond per-example PBT
- **Targeted PBT** — `target(score)` + post-random hill-climb (log-scaled
  `±2^k` deltas) + simulated-annealing escape (Cauchy proposals,
  augmented-Tchebycheff scalarization, T₀ scaled to observed score
  magnitude). Pareto front persists across runs via secondary corpus v2.
- **Coverage-guided PBT** (#107) — set `Settings.coverageGuided = true` and
  the engine wraps every property call so the per-example **coverage delta**
  is written into `currentFrame().scores["__coverage__"]`. The existing
  targeting machinery (Pareto front, hill-climb, SA) then treats coverage
  as just-another-objective. Instrument SUT procs with `{.cover.}`
  (8192-edge AFL-style bitmap, source-location hash IDs); runtime gate
  via `setCoverageMode(cmOff | cmRecording)` so a `{.cover.}`'d proc costs
  zero unless coverage is on.
- **Coverage-guided fuzzing** (M12) — `proptest/fuzz` module:
  `fuzzOnce(s, prop, bytes)` makes every property a libFuzzer/AFL target;
  `fuzzWith(s, prop, FuzzSettings) → FuzzReport` runs a coverage-guided
  loop with corpus mutation. **Default mutation mode is `fmIR`** (#110) —
  schema-aware mutators preserve the typed-IR structure (bit-flips and
  byte-replaces are still available as `fmBytes`).
- **Algebraic laws** — `eqLaws[T]`, `ordLaws[T]`, `semigroupLaws[T]`,
  `monoidLaws[T]` each return a `seq[NamedProperty]` so a failure points
  at the exact broken law.
- **Metamorphic combinators** — `metamorphic(s, prop, transform, relation)`
  for the general form; `unchangedUnder` is the equality specialization;
  `metamorphics` is the multi-transform fan-out. Built on the nested-`forAll`
  context stacking from M11.

### Verification (M15)
- **Linearisability checker** (#96) — `isLinearisable[State, OpId, Ret]`
  Wing-Gong implementation: happens-before-respecting backtracking with
  Wing-Gong memoization (bitmask + state hash, capped at history.len ≤ 64).
  Returns `LinResult` carrying `linearisable`, `witness`, `partialWitness`
  (longest valid prefix of any attempted ordering), and `divergingOp`
  (first event where the SUT broke).
- **`parallelCheck`** (#101) — thread-based runner over `isLinearisable`:
  jitter delays are drawn from the choice sequence so the shrinker pulls
  jitter toward the minimal pattern that exposes the bug. Racy bugs are
  reported as `otFlaky` (the correct diagnosis for nondeterminism).
- **`bmcCheck`** (#113) — bounded model checking for stateful machines.
  Enumerates every enabled rule firing breadth-first to depth `maxDepth`;
  invariant holds for every plan of length ≤ maxDepth is a *verification*
  claim, not a bug-finding result. Arg strategies are sampled with
  deterministic per-branch seeds; use `just(...)` args for true exhaustive
  coverage.
- **Bisimulation** (#115) — `bisim(sm1, sm2, observe1, observe2, depth)`
  decides observational equivalence between two state machines via
  lock-step BFS over `(state1, state2)` product pairs. Returns a
  distinguishing plan when they diverge. The use case: a reference impl
  vs. an optimized impl, up to the depth bound.
- **JSON Schema → strategy** (#97-A) — `strategyFromJsonSchema(schema:
  JsonNode): Strategy[JsonNode]` covering `type`/`enum`/`const`/bounds/
  `properties` + `required`/`items`/`oneOf`. Pattern (regex), `anyOf`/
  `allOf`, conditional, `$ref` deferred.

### Higher-order PBT
- **Property mining** (#114) — `mineProperties[I, O](inputs, fut,
  templates)`. The user supplies a strategy for inputs, a function under
  test, and a template library of candidate invariants; the miner runs the
  fut across traces and reports templates that always held — the "likely
  invariants" the human reviews to accept or reject. Daikon-style.
- **Mutation testing** (#116) — `mutantsOf(...)` macro walks a proc body's
  AST and emits one mutant per (site, mutator) pair (swap `<` for `<=`,
  flip boolean, replace integer literal with 0, …); the runtime scoring
  loop runs each through a user-supplied property closure and counts which
  mutants the property kills. High kill rate = property catches a wide
  range of bug classes; survivors are test gaps.

## Inline rejection: `assume` vs `Strategy.filter`

Two ways to skip an example; the right one depends on *when* the predicate
can be evaluated.

**`Strategy.filter(pred)` — pre-draw.** The predicate inspects the
generated value alone, so it's applied at strategy-construction time. Use
for shape constraints baked into the strategy:

```nim
let evens = integers(0, 100).filter(proc(x: int): bool = x mod 2 == 0)
property "even × even is even":
  given a in evens, b in evens
  ensure (a * b) mod 2 == 0
```

**`assume(cond)` — post-draw.** The predicate depends on state computed
*after* the draw (parsing the input, looking up a derived value, …). Lives
in the property body, raises `Rejection` on miss, and the engine counts it
against the rejection budget:

```nim
property "doc with removable prop preserves structure":
  given src in sampledFrom(corpus)
  let parsed = parse(src)
  assume parsed.isOk                       # decision depends on draw output
  let doc = parsed.get
  assume doc.hasRemovableProp
  let smaller = doc.removeProp()
  ensure isStructurallyValid(smaller)
```

There's also `sampledFromWhere(items, pred)` — an *eager* filter for
finite corpora that computes the matching subset at strategy construction
and draws uniformly from that. Use it instead of `sampledFrom(items)
.filter(pred)` when you have a known list and want to avoid burning the
rejection budget at runtime.

The `assumeOk(expr)` / `assumeSome(expr)` shorthands collapse the common
two-liner `let r = expr; assume r.isOk; let v = r.get` into one
expression — duck-typed on `.isOk` / `.isSome` + `.get`, so they work
with any Result-shaped type as well as `Option[T]`.

## Example: finding (and shrinking) a real bug

```nim
import std/unittest
import proptest

type Shape = object
  case kind: enum skCircle, skSquare
  of skCircle: radius: float
  of skSquare: side: float

suite "shape area":
  property "area is non-negative":
    given s in arbitrary(Shape)              # strategy auto-derived
    ensure (case s.kind
            of skCircle: s.radius * s.radius
            of skSquare: s.side * s.side) >= 0.0
```

If the property fails, the engine reports the shrunk-minimal counterexample
and `repro(report)` formats a one-pasteable string with seed, outcome,
counterexample, and the recorded choice sequence.

## Status

**Production-ready.** v1 + M10 through M17 (selectively) landed.
**385+ tests** across 50 test files; four rounds of multi-agent ultrareview;
issue-tracker is source of truth on open work.

### v1 milestones (M1–M9)

Choice IR & DataSource, strategies & combinators, engine & outcomes,
shortlex shrinker, `given` DSL + `std/unittest` adapter, strategy
auto-derivation, example database, stateful testing, targeted PBT.
Side issue #71 (distribution biasing — 5 layers) closed alongside.

Integration-driven wishlist (#72–#82, all landed): `Report.counterexample:
Option[T]`, `Report.dbReplays`/`notes`/`displayed`, `note(label, value)`,
`assumeOk`/`assumeSome`, `sampledFromWhere`, `strings(intervalSet, …)`,
DSL `with Settings(...)` clause, `StateMachine.initial: Strategy[S]`,
`Strategy.displayWith` + `mapWithDisplay`/`flatMapWithDisplay`,
hex-escape `safeKey`, surrogate-codepoint enforcement in `intervals()`.

### Post-v1 milestones

- **M10** — UX parity with Hypothesis: per-example `Settings.deadline` +
  `Settings.derandomize`, `event(label[, numericValue])` cross-example
  observability, DSL `examples <expr>` clause for pinned seeds, stateful
  `Bundle[S, V]`, **explain phase** (`Report.necessity` → per-choice
  `nNecessary`/`nFree` tags in `repro()`).
- **M11** — Architectural hygiene round 1: nested `forAll` composes via
  per-example frame stack; `ChoiceKind` codec table with compile-time
  exhaustiveness check; `Int128` shrinker bisection + log-scaled
  hill-climb perturbations (`logScaledIntDeltas`); `ExampleDatabase`
  closure-record with `inMemoryDatabase`/`multiplexedDatabase`/
  `readOnlyDatabase` factories + `forAllUsing(db, …)`; `Report.dbErrors`
  + `Settings.strictDb`; `renderReport(r, format)` for `ofText`/`ofJson`/
  `ofJunit`/`ofGithubAnnotation`.
- **M12** — Coverage-guided fuzzing (#94–#95): `proptest/fuzz` module,
  `newReplaySourceFromBytes` + `fuzzOnce(s, prop, bytes)` for
  libFuzzer/AFL targets, `{.cover.}` pragma with 8192-edge AFL-style
  bitmap, `fuzzWith(s, prop, FuzzSettings) → FuzzReport` coverage-guided
  loop. Now defaults to **`fmIR` mutation mode** (#110) — schema-aware
  IR mutators preserve typed structure; `fmBytes` remains for raw
  libFuzzer-style input.
- **M13** — Concurrency + schemas: **linearisability checker** (#96 —
  `isLinearisable`, Wing-Gong with memoization, best-partial-witness +
  diverging-op reporting), **JSON Schema → strategy** (#97-A —
  `strategyFromJsonSchema` covering type/enum/const/bounds/properties+
  required/items/oneOf). Follow-up **#101 `parallelCheck`** thread-based
  runner with choice-sequence-drawn jitter (shrinker pulls scheduling
  toward minimal-bug pattern) landed alongside.
- **M14** — Algebraic laws + metamorphic (#98 + #99): `eqLaws`,
  `ordLaws`, `semigroupLaws`, `monoidLaws` each return
  `seq[NamedProperty]` (failures point at the exact broken law);
  `metamorphic(s, prop, transform, relation)` + `unchangedUnder` +
  `metamorphics` (multi-transform fan-out), built on M11's nested-forAll
  context stacking.
- **M15 (verification + bug-finding extensions, partial)** — landed:
  - **#106** coverage runtime gate (`cmOff`/`cmRecording`) — `{.cover.}`
    procs cost zero unless caller opts in.
  - **#107** coverage-as-PBT-target (`Settings.coverageGuided`) —
    per-example coverage delta becomes a targeting objective via the
    existing Pareto + hill-climb + SA machinery. No fuzz↔engine cycle.
  - **#108** strategy distribution auto-labels (`Settings.autoLabels`,
    `auto.` reserved prefix). Built-in strategies emit
    `auto.int:near-lo`/`auto.list-len:empty`/etc. into the events
    categorical histogram — free distribution observability.
  - **#109** symbolic refs (`producingRule` / `consumingRule` /
    `SymRef[V]` / typed `PromiseStore`). Identity-preserving rule
    composition; dependency-respecting shrinking with no shrinker work.
  - **#110** IR-aware fuzz mutation (`fuzzir.nim`, default `fmIR` mode).
  - **#111** refinement-type derive — `arbitrary(range[1..10])`,
    `Natural`, `Positive` derive directly into typed `Strategy[R]`.
  - **#113** **BMC** (`bmcCheck`) — bounded model checking for stateful
    machines. Verification claim ("invariant holds for every plan of
    length ≤ maxDepth"), not bug-finding. Per-branch deterministic arg
    sampling; `just(...)` args for true exhaustive sweep.
  - **#114** **property mining** (`Template[I, O]` library, survival
    ranking). Daikon-style: user supplies inputs + fut + templates,
    miner reports invariants that always held.
  - **#115** **bisimulation** (`bisim`, lock-step BFS over state-pair
    products) — observational equivalence with distinguishing-plan
    witness.
  - **#116** **mutation testing** (`mutantsOf(...)` macro + scoring
    loop). High kill rate = property catches a wide bug spectrum;
    survivors are test gaps.

  M15 deferred: **#100** SMT-guided generation (research-grade);
  Paige-Tarjan partition-refinement for true non-deterministic
  bisimulation; PIT-style sandboxed child-process mutation.

- **M16** — Architectural hygiene round 2 (#119 + #120). The
  property-runner is now a pluggable pipeline of 7 phases
  (`dbReuse → explicit → random → targeted → shrink → explain →
  finalize`), each a deep module behind `Phase[T].run(state) →
  PhaseAction`. Engine subsystem extracted to 8 files
  (`engine/{types, frame, eval, render, pipeline, targeting,
  phases}.nim` + `engine.nim` 124-LOC shim). 92% reduction from the
  pre-#119 1521-LOC monolith. Future #100 / #107 / custom user phases
  inject as new `Phase[T]` entries — no runner fork.
- **M17** — Best-in-class integration & ergonomics. **Partially
  landed** via M15's overlap (#107 / #108 / #109 / #110 / #111).
  Remaining: #112 distributed corpus — deferred until a concrete
  consumer needs cross-machine corpus sync.

### Open

- **M13** sub-tasks B (Protobuf, #117) and C (OpenAPI, #118) — split
  from old #97; deferred pending consumer.
- **M15** research items: #100 SMT-guided generation, the
  partition-refinement bisimulation upgrade, the sandboxed mutation
  runner.
- **M17** #112 distributed corpus.

## Running

```bash
nimble test
# or, for an isolated toolchain:
podman run --rm -v "$PWD":/app:z -w /app docker.io/nimlang/nim:2.2.0 nimble test
```

## License

Apache License 2.0 © Corey Leavitt
