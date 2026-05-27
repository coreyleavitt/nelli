# proptest

Property-based testing for [Nim](https://nim-lang.org), built on an internal
**choice-sequence** engine — the same architecture that powers Python's
[Hypothesis](https://hypothesis.works). Generators are parsers over a recorded
sequence of typed primitive choices, so **shrinking is automatic, composable,
and survives `map` / `filter` / `flatMap`** — no hand-written shrinkers, ever.

> **Name note:** there is a well-known Rust crate also called `proptest`. This
> is the unrelated Nim library — search "proptest nim". Different ecosystem, no
> conflict.

## Why

Nim's existing property-testing options are QuickCheck-style (a generator paired
with a separate, hand-written shrinker) and either don't shrink or break
shrinking the moment you compose generators. `proptest` takes the modern
approach instead: a `Strategy[T]` only *draws* primitives from a `DataSource`
that records every draw; the shrinker minimizes that recorded sequence and
re-runs the generator. Shrinking is a property of the recording, not the type.

```nim
import proptest

property "reversing a list twice is the identity":
  given xs in lists(ints())
  ensure xs.reversed.reversed == xs
```

## Status

Early development. Targeting the full feature set before 1.0:
choice-sequence core, shortlex shrinking, macro-based strategy auto-derivation,
`std/unittest` integration, a persistent example database, stateful
(rule-based) testing, and targeted property testing.

## License

Apache License 2.0 © Corey Leavitt
