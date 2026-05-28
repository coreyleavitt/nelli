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
```

That compiles. That runs. That **shrinks**. And `nimble test` reports the
results natively.

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
  `flatMap`, `oneOf`, `sampledFrom`, `tuples` (variadic), `recursive`.
- **Built-in strategies** — `integers`, `booleans`, `floats`, `lists`
  (element-at-a-time → cheap deletion shrinking), `strings`, `tables`, `sets`,
  `enums` (handles holes), weighted `integers(weights = …)`.
- **Property runner** — `forAll` returns a deterministic `Report` (`otPassed`,
  `otFalsified`, `otExhausted`, `otFlaky`); two-layer flakiness detection;
  **crashes (`Defect`s like `IndexDefect`) caught as falsifications**.
- **Shortlex shrinker** — per-kind passes for integers, floats, bools, bytes,
  strings; span-directed deletion; fixpoint with a budget; public `sortKeyLess`
  for explicit shortlex comparison.
- **`given` DSL** — `property "name": given a in sa, b in sb, …: ensure …`
  with arbitrary arity, expanded to a `std/unittest` `test` block.
- **Macro auto-derivation** — `arbitrary(MyType)` synthesizes a strategy for
  most user types (primitives, `seq[T]`, plain objects with any field types,
  enums, ref objects, named tuples, object variants). Recursive types use a
  `recursive(base, extend, maxDepth)` combinator (auto-derivation of those is
  guarded by a clear compile-time error).
- **Example database** — `<dbPath>/<safeKey>.bin` per test id, atomic write,
  multi-entry primary corpus with LRU + dedup, stale entries auto-pruned on
  next run, secondary corpus of high-scoring non-failures so targeted PBT
  resumes across runs.
- **Stateful testing** — rule-based state machines with optional per-step
  `invariant` (catches transient mid-sequence violations final-state checks
  would miss); model comparison falls out of the same mechanism.
- **Targeted PBT** — `target(score)` + post-random hill-climb pushes toward
  pathological inputs; the choice-sequence representation makes mutation cheap.

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

**Production-ready breadth.** Seven of nine milestones complete; 121 tests.
Remaining open: a few auto-derivation tail items (generic instantiation,
distinct types, array/`Table`/`set` deriving, fully-automatic recursive-type
deriving — combinator already exists) and the advanced targeting refinements
(simulated-annealing escape, multi-objective Pareto front).

The library is **dogfood-ready** for real Nim libraries today.

## Running

```bash
nimble test
# or, for an isolated toolchain:
podman run --rm -v "$PWD":/app:z -w /app docker.io/nimlang/nim:2.2.0 nimble test
```

## License

Apache License 2.0 © Corey Leavitt
