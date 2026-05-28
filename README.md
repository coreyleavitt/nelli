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

- **Choice-sequence engine** with a typed IR (`int`/`float`/`bool`/`bytes`/`string`),
  recording, replay, overrun handling, and spans. Reproducibility lives in the
  recorded sequence, not the seed.
- **Owned 128-bit integer primitive** (`Int128`) so every native Nim integer
  type — including the full `uint64` range — round-trips losslessly.
- **All five primitive draws** with **distribution biasing**: small-magnitude
  bias around `shrinkTowards`, boundary injection (`0`, `±1`, `min`, `max`,
  `NaN`, `±Inf`, `±0`), and **swarm testing** with replay-deterministic mute
  masks in `oneOf`.
- **`Strategy[T]` combinators** — `just`, `map`, `filter` (+`Rejection`),
  `flatMap`, `oneOf`, `sampledFrom`, `sampledFromWhere` (eager-filter for
  finite corpora), `tuples` (variadic), `recursive`, and `displayWith`
  (custom counterexample renderer; sugar `mapWithDisplay` /
  `flatMapWithDisplay` attaches the new-`T` renderer in one call).
- **Built-in strategies** — `integers`, `booleans`, `floats`, `lists`
  (element-at-a-time → cheap deletion shrinking), `strings` (ASCII default
  + `strings(intervalSet, …)` overload for arbitrary Unicode), `tables`,
  `sets`, `enums` (handles holes), weighted `integers(weights = …)`.
- **Inline rejection shortcuts** — `assume(cond)` for post-draw filtering;
  `assumeOk(expr)` / `assumeSome(expr)` for the recurring `assume r.isOk;
  r.get` pattern (duck-typed on `.isOk`/`.isSome` + `.get`).
- **Property runner** — `forAll` returns a deterministic `Report` carrying
  `outcome`, `counterexample: Option[T]`, `choices`, `seed`, `paretoFront`,
  `dbReplays`, `notes`, and `displayed` (custom render from `displayWith`);
  two-layer flakiness detection;
  **crashes (`Defect`s like `IndexDefect`) caught as falsifications**.
- **`note(label, value)`** for debugging long chains — attaches
  `(label, $value)` pairs to the current example; the *shrunk*
  counterexample's notes appear in `Report.notes` and DSL checkpoints.
  No effect on generation or shrinking.
- **Shortlex shrinker** — per-kind passes for integers, floats, bools, bytes,
  strings; span-directed deletion; fixpoint with a budget; public `sortKeyLess`
  for explicit shortlex comparison.
- **`given` DSL** — `property "name": given a in sa, b in sb, …: ensure …`
  with arbitrary arity, expanded to a `std/unittest` `test` block. Optional
  `with mySettings` clause as the first line of a property body opts into
  DB integration, a custom seed, or any other `Settings` field.
- **Macro auto-derivation** — `arbitrary(MyType)` synthesizes a strategy for
  primitives (every native int/uint family member, `float`/`float32`,
  `bool`, `char`, `byte`, `string`), `Option[T]`, `seq[T]`, fixed `array[N,
  T]`, `Table`/`HashSet`/`set[T]`, tuples, plain objects (any field types),
  enums (with holes), ref objects, object variants (with single- or multi-
  field branches), generic instantiations (`Box[int]`), `distinct U`, **and
  directly-recursive types** (variant trees, linked lists, JSON-AST shapes
  with `seq[Self]`) which auto-emit `recursive(base, extend, 4)` with a
  synthesized leaf. Mutual recursion is detected at compile time and
  points at the manual `recursive(...)` combinator.
- **Example database** — `<dbPath>/<safeKey>.bin` per test id, atomic write,
  multi-entry primary corpus with LRU + dedup, stale entries auto-pruned on
  next run, secondary corpus of high-scoring non-failures so targeted PBT
  resumes across runs.
- **Stateful testing** — rule-based state machines with
  `initial: Strategy[S]` (use `just(value)` for a fixed seed, any strategy
  for a varying one — `arbitrary(S)`, `sampledFrom(corpus)`, etc.) and an
  optional per-step `invariant` (catches transient mid-sequence
  violations final-state checks would miss); model comparison falls out
  of the same mechanism. The initial state is part of the recorded choice
  sequence so the shrinker minimizes it alongside the rule selections.
- **Targeted PBT** — `target(score)` + post-random hill-climb pushes toward
  pathological inputs; the choice-sequence representation makes mutation cheap.

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

**Production-ready.** All nine milestones closed; **230 tests** green; four
rounds of multi-agent ultrareview applied + an integration-driven wishlist
pass (issues #72–#82, all landed) that brought: `Report.counterexample:
Option[T]`, `Report.dbReplays` / `Report.notes` / `Report.displayed`,
`note(label, value)` for debugging context, `assumeOk` / `assumeSome`
shorthand templates, `sampledFromWhere` eager-filter combinator,
`strings(intervalSet, …)` overload, `with Settings(...)` DSL clause,
`StateMachine.initial: Strategy[S]`, `Strategy.displayWith` (+
`mapWithDisplay` / `flatMapWithDisplay` sugar) for custom counterexample
rendering, hex-escape `safeKey` for collision-free DB filenames,
`runTargetedPhase` extraction, and the surrogate-codepoint enforcement
in `intervals()`.

Post-v1 roadmap landed (M10 — UX parity with Hypothesis, #84–#88): per-example
`Settings.deadline` + `Settings.derandomize` for hermetic CI; `event(label)` /
`event(label, numericValue)` for cross-example distribution observability
(categorical counts + min/max/mean/p50/p90/p99 numeric summaries); DSL
`examples <value>` clause for user-pinned regression seeds; stateful
`Bundle[S, V]` for typed value-flow between rules (auto-precondition-disabled
when the pool is empty; consumed index is shrinkable); and the **explain
phase** — `Report.necessity` annotates each choice as `nNecessary` (the
failure depends on its value) or `nFree` (it doesn't), surfaced as
per-choice tags in `repro()`.

Open milestones: M11 (architectural hygiene), M12 (coverage-guided fuzzing
+ libFuzzer adapter), M13 (concurrency + schemas), M14 (laws + metamorphic),
M15 (research / SMT — deferred).

## Running

```bash
nimble test
# or, for an isolated toolchain:
podman run --rm -v "$PWD":/app:z -w /app docker.io/nimlang/nim:2.2.0 nimble test
```

## License

Apache License 2.0 © Corey Leavitt
