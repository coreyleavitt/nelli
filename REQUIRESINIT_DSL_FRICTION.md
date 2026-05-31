# Friction: `given` DSL can't bind `{.requiresInit.}` types

> **✅ RESOLVED (2026-05-31).** Fixed in `tests/trequiresinit.nim` +
> `src/proptest/{strategy,engine,engine/eval,shrinker}.nim`. The root cause was
> as diagnosed (`valueType`'s `default(T)`), but driving real `requiresInit`
> values end-to-end surfaced **four** default-construction sites, not one — all
> eliminated so proptest now *never* default-constructs a user's element type at
> runtime (it does not merely silence the warning):
>
> 1. **`strategy.nim` `valueType`** — `default(T)` body → `raise`-terminated body
>    (type-checks for any `T`, constructs nothing). *The fix suggested below.*
> 2. **`engine/eval.nim`** — `var x: T` + try-assign → a `try`-**expression**
>    `let x` (no default ctor; also clears a pre-existing `ProveInit` warning).
> 3. **`shrinker.nim` `tryFalsifies`** — same `var x: T` → `try`-expression.
> 4. **`engine.nim` explicit examples** — `@explicit` / `@[]` (zero-filling
>    `newSeq`) → `reqInitSafeSeq` (`newSeqOfCap` + `add`, never defaults) /
>    `emptyExamples`. The residual stdlib `UnsafeSetLen`/`UnsafeDefault` is a
>    verified false positive, silenced at the call site (a `push` at a generic's
>    *definition* is not honoured for instantiation-time warnings).
>
> A co-located `tests/trequiresinit.nim.cfg` escalates `UnsafeDefault` /
> `UnsafeSetLen` / `ProveInit` to **compile errors**, so any reintroduced
> default-construction breaks the build there rather than warning silently on a
> strict-def Nim consumer. The `given` reproduction below now compiles and runs;
> the tuple-proxy workaround is no longer required (it remains valid).

**Type:** enhancement / papercut (not a correctness bug). **Severity:** medium —
blocks the most ergonomic path (`given x in arbitrary(T)` / a hand-written
`Strategy[T]`) for any type marked `{.requiresInit.}`, which is common in
defensive Nim codebases (object variants, value types that must be fully
initialized).

## Symptom

Binding a strategy whose element type is `{.requiresInit.}` fails to compile:

```
Error: The <T> type requires the following fields to be initialized: ...
```

The error points into `strategy.nim` (`valueType`), not the user's code, so it's
not obvious what's wrong.

## Root cause

The `given`/`property` DSL extracts the element type `T` from a strategy via the
phantom helper:

```nim
# strategy.nim
proc valueType*[T](s: Strategy[T]): T = default(T)
  ## Phantom used by the `property` DSL to extract `T` from a strategy via
  ## `typeof(valueType(strat))`. Never actually called at runtime — only its
  ## type matters.
```

Only the *type* of `valueType(strat)` is used (`typeof(...)`), but the proc body
`default(T)` still has to compile — and `default(T)` is illegal for a
`{.requiresInit.}` type. So a strategy that is otherwise perfectly valid can't
be bound through the DSL purely because of how `T` is recovered.

## Minimal reproduction

```nim
import std/unittest
import proptest

type
  Ev {.requiresInit.} = object
    case kind: bool
    of true:  a: int
    of false: discard

proc evs(): Strategy[Ev] =
  oneOf(@[
    just(Ev(kind: true, a: 0)),
    just(Ev(kind: false)),
  ])

suite "requiresInit":
  property "binds a requiresInit type":
    given e in evs()          # <-- Error: The Ev type requires ... to be initialized
    ensure e.kind or not e.kind
```

`evs()` itself is fine (its strategy never default-constructs `Ev`); only the
DSL's type-extraction step breaks.

## Real-world context

Hit in `nopal`, whose state machine marks its value types `{.requiresInit.}`
(`StateEvent`, `TrackerSnapshot`, `StateDecision`). Property-testing the pure
`decide(snap, event)` function couldn't bind those types directly.

### Current workaround (consumer-side)

Generate a plain (default-constructible) tuple, and build the `requiresInit`
object inside the property body:

```nim
type EvT = (bool, int)                      # default-constructible proxy
proc toEv(t: EvT): Ev =
  if t[0]: Ev(kind: true, a: t[1]) else: Ev(kind: false)

property "...":
  given t in tuples(booleans(), integers(0, 9))
  let e = toEv(t)                           # build requiresInit object here
  ensure ...
```

Works, but it's boilerplate and leaks an artificial proxy type into every test
file that touches a `requiresInit` type.

## Suggested fix

`valueType`'s body never runs — make it not require default-constructibility.
Replace the `default(T)` body with one that satisfies the return type without
constructing a `T`:

```nim
proc valueType*[T](s: Strategy[T]): T =
  ## Phantom: never called at runtime, only `typeof(valueType(s))` is used.
  raise newException(Defect, "valueType is a phantom; never call it")
```

A body that always `raise`s type-checks for any `T` (no value construction), so
`typeof(valueType(strat))` keeps working while `{.requiresInit.}` types compile.
(If the DSL can instead recover `T` without evaluating a proc body at all —
e.g. a `typedesc`-returning helper or a `distinct`/concept seam — that's even
cleaner, but the `raise` change is a one-line, behavior-neutral fix.)

### Test to add

A `tests/` case binding a `{.requiresInit.}` object variant through `given`
(the reproduction above), asserting it compiles and runs.
