# proptest / symex

Symbolic execution for branch-targeted coverage proof. Shape B of
[proptest #100](https://github.com/coreyleavitt/proptest/issues/100).

> Given a Nim proc and a labelled point inside it, find a concrete
> input that drives execution to that point — or prove no such input
> exists.

The walker is a path-frontier interpreter over a small Nim-IR that
the parser builds at macro time. Each surviving path carries a Z3
formula; the target is encoded as a query to that formula. The
output is `SymexResult[ParamTuple]` carrying the witness when
satisfiable.

## Where to start

| If you want to… | Read |
|---|---|
| See it work | [examples/symex_simple.nim](../../examples/symex_simple.nim) |
| Walk through the model from first principles | [tutorial.md](tutorial.md) |
| Verify your random test covers a hard branch | [examples/symex_assert_covered.nim](../../examples/symex_assert_covered.nim) |
| Bring your own opaque proc under symex | [extending-stdlib.md](extending-stdlib.md) |
| Understand why the answer is what it is | [abstraction-internals.md](abstraction-internals.md) |
| Reason about Z3-version drift | [determinism.md](determinism.md) |

## The three target kinds

| Target | What it asks | Where to use |
|---|---|---|
| `tLabel("name")` | Find an input that reaches `symexTarget("name")`. | Coverage of arbitrary named branches. |
| `tAssertionViolation()` | Find an input that fails any `symexAssert(cond)`. | Bug-hunting for invariants. |
| `tIndexError()` | Find an input that drives any `arr[i]` out of bounds. | Memory-safety witnesses. |

## Public surface

The single import:

```nim
import proptest/symex
```

re-exports the supported Nim type bridge (`proptest/smt/dsl`),
the choice IR (`proptest/choice`), the example DB
(`proptest/db`), and the engine `SymexFinding` type.

### Driver

```nim
macro symexFind*(fn: typed, target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): SymexResult[ParamTuple]
```

### Verifier (Phase 7)

```nim
macro assertCoveredBy*(fn: typed, target: static SymexTarget,
                       testFn: typed = nil, settings = …)
macro assertCoveredBy*(fn: typed, targets: static openArray[SymexTarget], …)
```

### Markers (dual-mode procs — usable in random PBT too)

| Marker | Outside symex | Inside symex |
|---|---|---|
| `symexTarget(name)` | feeds capture hit-set (if active) | label the parser recognises |
| `symexAssert(cond)` | `doAssert cond` | fork point under `tAssertionViolation` |
| `symexAssume(cond)` | no-op | conjoin into path condition |

### Extension pragma

```nim
proc myFFI(): int {.symexOpaque.} = ...
```

Tells the walker not to enter the body: fresh symbolic return, path
marked uncertain. See [extending-stdlib.md](extending-stdlib.md).

### Witness ↔ choice-IR + DB (Phases 7 + 10)

```nim
proc renderAsChoices*[T](w: T): seq[ChoiceNode]

# Content-addressed persistence (Phase 10) — key is derived from the
# SUT IR, target, witness-relevant settings, Z3 / Nim / walker
# versions. See determinism.md for the full contract.
macro saveSymexWitness*(db, fn, target, settings, finding, maxEntries = 64)
macro loadSymexWitnesses*(db, fn, target, settings): seq[seq[ChoiceNode]]

# Pure, testable key derivation
proc symexCacheKey*(prog: SymexProgram, target: SymexTarget,
                    settings: SymexSettings,
                    z3Version, nimVersion, walkerVersion: string): string
```

See [determinism.md](determinism.md) for the content-addressed
persistence contract and the proof-obligation table for every input
that does (or does not) participate in the cache key.

## Settings

```nim
SymexSettings(
  integerSemantics:        isOptimised,  # ADR-0001
  queryTimeoutMs:          5000,
  maxFrontierSize:         256,
  maxCallDepth:            3,
  maxLoopUnwind:           5,
  acceptUnknownAsCovered:  false)
```

Constructors: `defaultSymexSettings()` / `optimisedSymexSettings()` /
`looseSymexSettings()`.

## Supported Nim fragment

### Types (`IRTypeKind`)

| Kind | Nim source shape | Phase | Notes |
|---|---|---|---|
| `itInt`    | `int`, `int8..int64`, `uint8..uint64`, `Natural`, `Positive`, `range[lo..hi]`, enums | 2 | BV[W] + selective Z3Int (ADR-0001) |
| `itBool`   | `bool` | 1 | |
| `itString` | `string` | 5 | Z3 string theory |
| `itTuple`  | tuples, objects, variant objects (flat-tuple lowering) | 4 | variant witnesses currently `default(Object)` stub |
| `itArray`  | `array[N, T]` (any element type) | 4 | nested arrays via rectify round 1 |
| `itSeq`    | `seq[T]` | 5 | `len + Z3Array data` |
| `itTable`  | `Table[K, V]` | 5 | `data + present + size` |
| `itSet`    | `HashSet[T]`, `set[T]` | 5 | `members + size` |

### Statements (`IRStmtKind`)

| Kind | Nim source shape | Phase |
|---|---|---|
| `isBlock` / `isIf` / `isLet` / `isAssign` | block/if/elif/else, `let`, `=` | 1 / 5 |
| `isWhile` / `isBreak` / `isContinue` | `while`, `break`, `continue` | 6 |
| For loops | `for i in a..b`, `for x in arr`, `for x in seq` | 6 (desugared) |
| `case` | `case … of …` | 6 (if-elif lowering) |
| `isReturn` | `return [expr]` | 1 |
| `isAssert` | `symexAssert(cond)` | 1 |
| `isCall` | user-proc + stdlib-model calls | 3 / 5 |
| `isIndex` | `arr[i]`, `s[i]`, `t[k]` | 4 / 5 |
| `isTargetLabel` | `symexTarget(name)` | 1 |
| `isUnsupported` | macro-time diagnostic for unmodelled AST | — |

### Container mutations

| Op | Source | Phase |
|---|---|---|
| seq `add`/`del`/`insert`/`pop` | `s.add(v)`, etc. | 5 / rectify round 1 |
| Table `[]=`/`del` | `t["k"] = v`, `t.del("k")` | 5 / rectify round 1 |
| HashSet `incl`/`excl` | `s.incl(x)`, `s.excl(x)` | 5 / rectify round 1 |

### Out of scope for v1 (diagnosed at macro time)

- Unbounded loops without invariants (k-unwind exhaustion → `sxUnknown`)
- Cross-module private callees (Nim `getImpl` returns empty)
- Concurrency / threads / channels
- Closures with environment capture (single-pointee `ref T` works)
- Floats (planned later)
- Generics beyond simple typedesc substitution

A SUT outside the fragment is rejected with a macro-time error
naming the offending node — never silently elided.

## Architectural decision records

| | Title | Status |
|---|---|---|
| [ADR-0001](ADR-0001-integer-semantics.md) | Integer semantics — BV[W] floor with selective `Z3Int` abstraction | Accepted 2026-05-31 |
| [ADR-0002](ADR-0002-dsl-factoring.md) | Predicate-DSL factoring — three-layer `proptest/smt/` split | Accepted 2026-05-31 |

An ADR is a short document recording one architectural decision:
the context that forced the choice, the options considered, the
resolution, and the consequences. When revisited, the ADR is
amended in place with a "Superseded by …" header. Reference:
[Michael Nygard, *Documenting Architecture Decisions*, 2011](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions).

## Status

Phases 0-7 shipped. Phase 9 (this doc set + examples + boundary
analysis) is the current focus. See
[../SYMEX_PLAN.md](../SYMEX_PLAN.md) for the live plan and commit
references.
