# nelli / symex

Symbolic execution for branch-targeted coverage proof. Shape B of
[nelli #100](https://github.com/coreyleavitt/nelli/issues/100).

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

## The four target kinds

| Target | What it asks | Where to use |
|---|---|---|
| `tLabel("name")` | Find an input that reaches `symexTarget("name")`. | Coverage of arbitrary named branches. |
| `tAssertionViolation()` | Find an input that fails any `symexAssert(cond)`. | Bug-hunting for invariants. |
| `tIndexError()` | Find an input that drives any `arr[i]` out of bounds. | Memory-safety witnesses. |
| `tFieldDefect()` | Find an input that drives a variant arm-field access whose discriminator is outside that field's arm set. | Memory-safety / soundness witnesses on variant types. Phase 11. |

## Public surface

The single import:

```nim
import nelli/symex
```

re-exports the supported Nim type bridge (`nelli/smt/dsl`),
the choice IR (`nelli/choice`), the example DB
(`nelli/db`), and the engine `SymexFinding` type.

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
| `itTuple`  | tuples, plain objects (no `nnkRecCase`) | 4 | flat positional + named fields |
| `itArray`  | `array[N, T]` (any element type) | 4 | nested arrays via rectify round 1 |
| `itSeq`    | `seq[T]` | 5 | `len + Z3Array data` |
| `itTable`  | `Table[K, V]` | 5 | `data + present + size` |
| `itSet`    | `HashSet[T]`, `set[T]` | 5 | `members + size` |
| `itVariant` | Nim variant objects (`case kind: …`) | 11 | first-class sum type: per-arm fields, walker forks at access, witness via case-dispatch construction |

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
| `isVariantField` | A-normalised `let x = obj.field` on a variant arm field | 11 |
| `isVariantReassign` | `obj.kind = staticTag` | 11 |
| `isTargetLabel` | `symexTarget(name)` | 1 |
| `isUnsupported` | macro-time diagnostic for unmodelled AST | — |

### Container mutations

| Op | Source | Phase |
|---|---|---|
| seq `add`/`del`/`insert`/`pop` | `s.add(v)`, etc. | 5 / rectify round 1 |
| Table `[]=`/`del` | `t["k"] = v`, `t.del("k")` | 5 / rectify round 1 |
| HashSet `incl`/`excl` | `s.incl(x)`, `s.excl(x)` | 5 / rectify round 1 |

### Variant-object specifics (Phase 11)

| Feature | Phase 11 cycle |
|---|---|
| `nnkRecCase` lowered to first-class `itVariant` | 2 |
| Discriminator-only field access | 3 |
| Arm-field access (single & multi-arm via ite-chain) | 4 |
| `tFieldDefect()` target | 5 |
| Discriminator reassignment `obj.kind = staticTag` | 6 |
| Witness via case-dispatch construction (drops `default(Object)` stub) | 7 |
| `renderAsChoices` for variants (positional: disc + active-arm fields) | 8 |
| Discriminator interval `[min, max]` in `r.abstractions` (under `isOptimised`) | 9 |
| Nested variants (recursive composition) | 10 |

Walker version `"2"` (was `"1"` for Phases 0-10); persisted witnesses
from the old flat-tuple representation are correctly invalidated by
the content-addressed cache key.

## Input-source seeding (Phase 12)

Symex has a second role beyond verification: lifting its witnesses
into the random-PBT loop as **forced seeds**. The user writes one
SUT proc; symex auto-discovers every target the SUT exposes, runs
Z3 per target, and replays each SAT witness through the engine —
where the shrinker minimises it the same as any random
falsification.

### Auto-discovery

The macro scans the SUT's IR (transitively through
`parseProc.procs` for `isCall` bodies — same Phase-3 cross-module
limit applies) and includes a target per IR construct it finds:

| IR construct in the SUT | Auto-included target |
|---|---|
| `symexTarget("name")` (one per occurrence) | `tLabel("name")` |
| `symexAssert(cond)` (any `isAssert`) | `tAssertionViolation()` |
| `arr[i]` / `s[i]` / `t[k]` (any `isIndex`) | `tIndexError()` |
| variant arm-field read (any `isVariantField`) | `tFieldDefect()` |

No defect-triggering construct and no markers → exactly one
`SymexFinding(status: sfNotApplicable, targetDesc:
"no-targets-discovered")` audit entry is produced; no Z3 calls.

### Escape hatch — `excludeTargets`

```nim
symexForAll(integers(), handle, db = db,
            excludeTargets = @[tIndexError(), tFieldDefect()])
```

Filter is by `SymexTargetKind`. Excluding `tLabel(...)` suppresses
all label targets; label-by-name suppression is a deferral (see
[PHASE12_PLAN.md](PHASE12_PLAN.md) deferrals table).

The constructor-form spelling is the same vocabulary as
`assertCoveredBy(..., tIndexError())`. The seq-literal form
(`@[…]` rather than `[…]`) is required because a bare static
openArray default crashes Nim 2.2's macro evaluator — see the
plan-doc deferrals for the toolchain bug.

### Three-layered API

```nim
# Layer 1 — primitive. Macro-scans fn's IR for every auto-target,
# runs symex per target (cache-first via the Phase 10 content-
# addressed key), returns one SymexFinding per. Also deposits
# each finding into the per-thread sink so finalizePhase can
# drain them into Report.symexFindings.
macro symexFindAllWitnesses*(fn: typed,
                              db: ExampleDatabase,
                              symexSettings: static SymexSettings =
                                defaultSymexSettings(),
                              excludeTargets: seq[SymexTarget] = @[]
                             ): seq[SymexFinding]

# Layer 2 — engine entry. Custom pipeline that slots
# `symexSeedPhase(seeds)` between `explicit` and `random`.
proc forAllWithSymexSeeds*[T](seeds: seq[seq[ChoiceNode]],
                              s: Strategy[T], prop: proc(x: T),
                              settings: Settings = defaultSettings()
                             ): Report[T]

# Layer 3 — sugar. fn doubles as the property AND as the IR-scan
# target. Multi-arg fns + `map(s1, s2, ...)` strategies are
# supported via a macro-emitted tuple-splatting wrapper.
macro symexForAll*(s: typed, fn: typed,
                   db: ExampleDatabase,
                   symexSettings: static SymexSettings =
                     defaultSymexSettings(),
                   forAllSettings: Settings = defaultSettings(),
                   excludeTargets: seq[SymexTarget] = @[]
                  ): untyped
```

### Pipeline order

```
dbReuse → explicit → symexSeed → random → targeted → shrink → explain → finalize
```

The `symexSeed` phase consumes the seed list end-to-end on each
seed via `evalReplay`:

- `ekFalsified` → set `rawFalsification` with the replayed choice
  sequence so `shrinkPhase` can minimise the witness.
- `ekRejected` (Overrun from a shape-mismatched seed OR property
  `reject`/`assume`) → deposit one `sfNotApplicable` audit entry
  and continue.
- `ekPassed` → continue silently.

Self-gates when an upstream source phase (e.g. `dbReuse`) already
set `rawFalsification`.

### Warm-run note

When the DB already holds a stored failure for the SUT,
`dbReusePhase` runs first and sets `rawFalsification` → the
self-gate in `symexSeedPhase` skips it on that run. This is the
common case in active development. Callers who want a symex audit
even when dbReuse falsifies should call `symexFindAllWitnesses`
directly (Layer 1) and inspect the returned findings — Layer 1's
sink-deposit behaviour is independent of the engine pipeline.

### Cold-cache latency

On a fresh DB the worst-case cost for one
`symexFindAllWitnesses` invocation is

```
N targets × per-target solver cost (bounded by SymexSettings.queryRLimit
                                    if set; unbounded if 0)
```

where `N` is the number of auto-discovered (post-`excludeTargets`)
targets and per-target solver cost is measured in Z3 logical
steps (`queryRLimit`), not wall-clock ms — Phase 13 wired the
field to Z3's `rlimit` parameter for deterministic resource
bounds. Default `queryRLimit = 0` means unbounded; opt in by
setting a positive value.

**Warm-run cost** (after Phase 13's verdict caching): one DB
load per target. SAT, UNSAT, and UNKNOWN findings all cache
under the content-addressed key. `SymexFinding.fromCache` flags
the load-vs-derive provenance so consumers can audit the cache
hit rate:

```nim
let report = symexForAll(s, fn, db)
let hits = report.symexFindings.countIt(it.fromCache)
echo "cache hit rate: ", hits, "/", report.symexFindings.len
```

### Upgrade note from Phase 12 → Phase 13

Phase 13 rotates the cache key once across two axes:

1. `SymexSettings.queryTimeoutMs` (uint, ms — never wired) was
   renamed to `queryRLimit` (uint, Z3 logical steps — now wired
   via `Z3_solver_set_params`). The canonical-form tag prefix
   changed from `";to="` to `";rl="`. Every Phase 12 cache
   entry rotates.
2. SAT witnesses moved from the bare `"sx:" & H` key to
   `"sx:" & H & ":sat"` to make room for the new sibling slots
   `:unsat` and `:unk`.

On upgrade: **first run after Phase 13 re-derives every
previously cached SAT witness**; one-time cold cost. From the
second run onward, UNSAT/UNKNOWN verdicts cache too — net win
even for cache-warm SUTs that previously paid `N × queryTimeoutMs`
on every UNSAT-prone target.

See [determinism.md § Verdict caching](determinism.md#verdict-caching-phase-13)
for the full contract.

### Upgrade note from Phase 11

`renderAsChoicesVersion` bumped `"1"` → `"2"` in Phase 12 to
invalidate the latently-broken length-prefix encoding of
`seq[T]` / `HashSet[T]` / `Table[K, V]` witnesses (the old
encoding could not be replayed through `lists`/`tables`/`sets`
strategies; the new continue-boolean encoding matches what those
strategies actually consume). Effect on existing DBs:

- **Collection witnesses** persisted under `renderAsChoicesVersion
  = "1"` become invisible on the next run and re-derive once.
- **Non-collection witnesses** (int / bool / string / tuple /
  object / variant) are unaffected — their choice encoding did
  not change.

Walker version stays at `"3"`; non-collection witnesses across
the Phase 12 upgrade keep their cache entries.

### Out of scope for v1 (diagnosed at macro time)

- Unbounded loops without invariants (k-unwind exhaustion → `sxUnknown`)
- Cross-module private callees (Nim `getImpl` returns empty)
- Concurrency / threads / channels
- Closures with environment capture (single-pointee `ref T` works)
- Floats (planned later)
- Generics beyond simple typedesc substitution
- Variant object **inheritance** (`type Foo = object of Bar`)
- Variant **`else:` branches** in `nnkRecCase` (use exhaustive `of`)
- Variants with **multiple `nnkRecCase` members** per object
- **Symbolic** discriminator reassignment (`obj.kind = someVar`)
- **Composite arm-field types under reassignment** (only primitives zero-init on `obj.kind = staticTag`)

A SUT outside the fragment is rejected with a macro-time error
naming the offending node — never silently elided.

## Architectural decision records

| | Title | Status |
|---|---|---|
| [ADR-0001](ADR-0001-integer-semantics.md) | Integer semantics — BV[W] floor with selective `Z3Int` abstraction | Accepted 2026-05-31 |
| [ADR-0002](ADR-0002-dsl-factoring.md) | Predicate-DSL factoring — three-layer `nelli/smt/` split | Accepted 2026-05-31 |
| [ADR-0030](ADR-0030-boundary-normalization.md) | Boundary normalization — the walker's input language is defined by what the boundary emits, not what the compiler can produce | Partial (D1, D2 Accepted) 2026-08-14 |

An ADR is a short document recording one architectural decision:
the context that forced the choice, the options considered, the
resolution, and the consequences. When revisited, the ADR is
amended in place with a "Superseded by …" header. Reference:
[Michael Nygard, *Documenting Architecture Decisions*, 2011](https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions).

## Status

Phases 0-13 shipped: full SUT fragment, four target kinds, the
content-addressed DB (now with three sibling slots for SAT /
UNSAT / UNKNOWN verdicts), first-class variant soundness, the
input-source role lifting witnesses into the random-PBT loop via
the three-layered `symexFindAllWitnesses` / `forAllWithSymexSeeds`
/ `symexForAll` API, Z3 `rlimit` wired for deterministic UNKNOWN
caching, and `SymexFinding.fromCache` provenance for cache-hit
audit. See [../SYMEX_PLAN.md](../SYMEX_PLAN.md) for
the live plan and commit references.
