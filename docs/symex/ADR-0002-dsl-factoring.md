# ADR-0002 — Predicate-DSL factoring

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-05-31 |
| **Deciders** | nelli maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [SYMEX_PLAN.md § ADR-0002](../SYMEX_PLAN.md), nelli [#124](https://github.com/coreyleavitt/nelli/issues/124) (Shape A umbrella), [#125](https://github.com/coreyleavitt/nelli/issues/125) (`arbitrary[where(...)]`) |

## Context

A **predicate DSL** translates a Nim-source predicate (a procedure
expression or a `where`-style macro argument) into a Z3 constraint.
Concretely:

```nim
where(x: int, x mod 3 == 0)
# → Z3: (mod x 3) == 0   where x is a Z3Int symbol
```

Two consumers in the nelli design need this translation:

- **Symex (#100)** — `symexFind(f, target, constraint = proc(input: T): bool = …)`.
  The constraint restricts which inputs symex considers reachable.
- **Shape A (#125)** — `arbitrary[where(x: int, x mod 3 == 0)]`.
  The constraint defines the strategy's support set.

The two consumers use the same translation pipeline. The question this
ADR resolves is *where the translator lives* — specifically: should the
translator be inside the symex codebase (with Shape A importing from
symex when it ships), or factored into a shared module?

The decision affects v1 scope (because the translator has to ship in v1
to enable symex's `constraint` param) and affects the v1 module layout
that Shape A will later have to live with.

## Options considered

### Option A — Build the DSL inside the symex codebase

`nelli/symex/dsl.nim` is the home. Shape A imports it as
`from nelli/symex/dsl import …` when #125 builds.

**Pros**: smallest v1 footprint; no speculative cross-module API.
**Cons**:
- Architecturally odd: the DSL "belongs to" symex despite Shape A being
  arguably its larger consumer (Shape A's DSL is user-facing on every
  strategy; symex's DSL is opt-in per `symexFind` call).
- Re-architecture cost when #125 fires: Shape A has to import from a
  symex submodule, which forces a circular-dependency check (does Shape
  A's strategy module need anything from symex, or vice versa?). The
  resolution is mechanical but the diff is noisy.
- The shared infrastructure list (typedesc → Z3 family resolution,
  symbolic-environment binding) ends up in a symex-namespaced module
  even though it's not symex-specific.

### Option B — Factor into a shared `nelli/smt/` namespace from day one

Both consumers depend on `nelli/smt/dsl.nim`. The `nelli/smt/`
namespace becomes the home for all Z3-touching code that isn't a
consumer adapter.

**Pros**:
- Future-proofs the v1 layout. When Shape A's first sub-feature builds,
  its consumer adapter is one new file (`nelli/smt/strategy.nim`)
  that imports the same DSL the symex consumer already uses.
- Makes the cross-cutting nature of the DSL explicit in the directory
  structure.
- Creates a natural home for *other* future Z3-touching code (a
  refinement-type checker that uses Z3 for satisfiability, the Z3-based
  shrinker probe from #126, etc.).

**Cons**:
- One extra module path in v1.
- Speculative: we're shipping the namespace before its second consumer
  exists.

## Decision

**Adopt Option B, refined into three layers.**

```
nelli/smt/
  dsl_parser.nim       # Layer 1: pure Nim-AST → Z3-expression
  dsl_typebridge.nim   # Layer 2: typedesc → Z3 family resolution
  dsl.nim              # Layer 3: ergonomic constructors, re-exports
```

Consumer adapters live next to their consumers:

```
nelli/symex.nim              # consumes dsl + walker
nelli/smt/strategy.nim       # consumes dsl + strategy machinery
                                #   (lands with #125, not in v1)
```

### Layer 1 — `dsl_parser.nim` (pure translator)

Stateless function from a typed Nim AST node + a symbol→Z3 binding
environment to a Z3 expression. Handles:

- `nnkIntLit`, `nnkFloatLit`, `nnkStrLit` → Z3 literal constructors
- `nnkInfix` for arithmetic + boolean + comparison
- `nnkPrefix` (`not`, unary minus)
- `nnkCall` (limited — see § Allowed callables)
- `nnkIfStmt` → `ite`
- `nnkBracketExpr` (array index, generic instantiation)
- `nnkDotExpr` (field access)
- `nnkSym` (variable reference; looked up in the binding env)

The parser is **testable in isolation**. The Layer 1 tests
(`tests/tsymex_phase1_dsl.nim`) feed it small Nim AST fixtures and
assert on the produced Z3 expression structure — no walker, no Z3
context state, no proc machinery.

This is the hardest, most algorithmically subtle layer. Isolating it
is the main practical win of the three-layer split.

#### Allowed callables in Layer 1

A whitelist of stdlib + nim-z3 ops the parser recognizes. v1 set:

- Arithmetic: `+ - * div mod`
- Comparison: `== != < <= > >=`
- Boolean: `and or xor not`
- `in` / `notin` over `seq`, `Table`, `HashSet` (Phase 5)
- `len` over `seq`, `Table`, `HashSet`, static array

Unknown callables in Layer 1 either:

- (a) Get resolved via the symex stdlib model registry if they're stdlib
  procs symex knows how to model — the DSL parser asks the registry by
  symbol identity.
- (b) Get rejected with a macro-time diagnostic naming the unknown call.

The DSL is intentionally not Turing-complete; the diagnostic message
points the user at the supported subset.

### Layer 2 — `dsl_typebridge.nim` (typedesc → Z3 family)

The bridge from a Nim `typedesc` to a Z3 sort + family. v1 cases:

| Nim type | Z3 family |
|---|---|
| `int`, `int8`/16/32/64 | `Z3BitVec[W]` or `Z3Int` (per ADR-0001) |
| `uint`, `uint8`/16/32/64 | `Z3BitVec[W]` (unsigned) |
| `bool` | `Z3Bool` |
| `char` | `Z3BitVec[8]` |
| `string` | `Z3String` |
| `float`, `float32`/64 | `Z3Fp[E, S]` |
| `seq[T]` | `(Z3Int, Z3Array[Z3Int, sortOf(T)])` (len + data; Phase 5) |
| `array[N, T]` | `Z3Array[Z3Int, sortOf(T)]` (static; Phase 4) |
| `tuple[...]` | per-field families (Phase 4) |
| `object` | per-field families (Phase 4) |
| `Table[K, V]` | `(Z3Array[K, V], Z3Array[K, Z3Bool])` (Phase 5) |
| `HashSet[T]` | `Z3Array[T, Z3Bool]` (Phase 5) |

The bridge wraps nim-z3's `sortOfType` machinery. It is a derive-style
operation — separately maintained means we extend one place when a
new Nim type becomes supported.

### Layer 3 — `dsl.nim` (ergonomic re-exports)

The user-facing import surface. Wraps Layer 1 + Layer 2 in the
ergonomic constructors:

```nim
import nelli/smt/dsl

# As a constraint:
let c = constraint(x: int): x mod 3 == 0

# As a strategy refinement (lands with #125):
let s = arbitrary[where(x: int, x mod 3 == 0)]
```

Layer 3 is thin. Its job is import-surface ergonomics, not algorithmic
work.

## Consequences

### Intended

- The hardest layer (the parser) is testable without either consumer.
  Bug surface area is bounded; bugs caught early.
- Shape A's eventual build (#125) is mechanical: one new file under
  `nelli/smt/`, importing the same DSL the symex consumer uses.
  The cross-consumer infrastructure is already in place and tested.
- The `nelli/smt/` namespace is established as the home for all
  future Z3-touching infrastructure (refinement-type checking, the
  Z3-shrinker probe from #126, etc.). Future Z3 features have an
  obvious place to land.
- Consumer adapters stay thin and orthogonal — each lives next to its
  consumer, doesn't infect the other consumer's API.

### Accepted as cost

- The v1 module surface includes three `nelli/smt/` files even
  though only one consumer (symex) exists at v1.0.
- The DSL's allowed-callable whitelist has to be maintained as the
  stdlib coverage grows. The cost is bounded — one match arm per new
  callable, colocated in `dsl_parser`.

### Not addressed by this ADR

- *How* the DSL is invoked at the symex API boundary —
  `symexFind(..., constraint = proc(x: int): bool = …)` vs. a
  `constraint[T](pred)` macro vs. a `where`-style block. That's an
  ergonomics decision for Phase 1; ADR-0002 only fixes the
  layer-boundary architecture, not the surface syntax.
- The interaction between `constraint` and `where` once Shape A
  lands. Both consume Layer 1+2; the user-facing surfaces may or may
  not converge syntactically. That's a Shape-A-era decision.

## Validation

ADR-0002's three-layer split is validated by:

- **Layer 1 isolation**: `tests/tsymex_phase1_dsl.nim` exercises the
  parser against Nim AST fixtures with no walker / no Z3 context state.
  If this test grows hard to write (requires walker or runtime context
  to make assertions), the layer boundary has leaked.
- **Layer 2 reuse**: when Shape A's `arbitrary[where(...)]` builds
  (#125), the only Layer 2 work is consumer-adapter glue. No new
  typedesc → Z3 family code is needed. If it is, the layer boundary
  was wrong.
- **Consumer-adapter thinness**: `nelli/symex.nim` should be a
  small file (hundreds of lines, not thousands) — most code lives
  under `nelli/smt/` and `nelli/symex/`. If the consumer adapter
  grows large, code is escaping the shared layer.
