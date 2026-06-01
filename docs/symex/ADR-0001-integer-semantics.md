# ADR-0001 — Integer semantics for the symex walker

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-05-31 |
| **Deciders** | proptest maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [SYMEX_PLAN.md § ADR-0001](../SYMEX_PLAN.md), proptest [#111](https://github.com/coreyleavitt/proptest/issues/111) refinement-type derivation, [nim-z3 v1.0.0](https://github.com/coreyleavitt/nim-z3) |

## Context

Symbolic execution requires choosing a Z3 encoding for Nim integers. The
naive choice — "use `Z3Int` everywhere" — is not sound for our purpose,
and the obvious sound choice — "use `Z3BitVec[W]` everywhere" — sacrifices
1–2 orders of magnitude of solver performance on the cases where it isn't
needed.

The decision matters because integer-heavy SUTs are the dominant case in
the consumer profile (parsers, interpreters, optimization passes,
arithmetic-rich domain logic), and because the walker's per-query SMT
cost dominates total symex runtime.

### What "sound for symex" means

Symex's `symexFind` returns an input that drives the SUT to a named
target. **Soundness for our purpose** means: if symex returns a witness
`w` claiming "running `f(w)` reaches target T", then running `f(w)` at
runtime actually reaches T. A walker that admits witnesses that overflow
at runtime — taking a branch the BV semantics would have rejected — is
**unsound**: it lies to the user.

This is the same correctness requirement bounded model checkers operate
under, and the same trap that hand-rolled symex tools (KLEE notwithstanding)
have historically fallen into.

### The Nim-specific complication

Nim's default integer operations are **silently modular**. `x + y` on
`int32` wraps at runtime; no overflow trap, no signal. The
`-d:nimDangerous` / range-check pragmas can change this per-build, but
the default — and the default the proptest user is testing against — is
silent wrap.

This means the **runtime semantics of every fixed-width Nim integer op
is exactly bit-vector semantics**. Any encoding that diverges from BV
on fixed-width values is *unsound* in the sense above, not merely
imprecise.

## Options considered

### Option A — Always unbounded `Z3Int`

Every Nim integer maps to `Z3Int`. All arithmetic is unbounded-integer
arithmetic in Z3.

**Pros**: simplest encoding; fastest solver time (Int theory ≪ BV theory).
**Cons**: **Unsound**. The walker emits witnesses that satisfy the path
condition under unbounded arithmetic but overflow at runtime under
modular arithmetic, taking different branches than predicted. Examples:

```nim
proc f(x: int32, y: int32): bool =
  x + y < 0   # target: "this branch fires"
```

Under `Z3Int`, the walker finds no witness (`x + y < 0 ∧ x ≥ 0 ∧ y ≥ 0`
is UNSAT over `Z3Int`). Under runtime semantics, `x = int32.high, y = 1`
fires the branch via wrap. The Z3Int walker would report this branch
unreachable; a real test would reveal the lie.

**Rejected outright**. No amount of perf wins justifies unsound reachability
claims from a tool whose value proposition is "the witnesses are correct."

### Option B — Always `Z3BitVec[W]`

Every Nim integer maps to `Z3BitVec[sizeof(T)*8]`. All arithmetic is BV.

**Pros**: sound by construction. The encoding mirrors runtime semantics
exactly. The walker's per-AST-kind dispatch table has one path per op.
**Cons**: 10–100× slower per query on Int-shaped fragments (loops over
bounded counters, refinement-type-constrained variables). Z3's BV solver
is competent but not free; on common cases — `for i in 0..n: …` where
`n` is small and `i` never overflows — paying the full BV cost is
strictly wasted work.

### Option C — Hybrid (Int by default, BV when triggered)

Naive form: use `Z3Int` until a "BV-specific" operation appears (bit
shift, mask, fixed-width cast), then switch.

**Pros**: optimistic optimization.
**Cons**: **Also unsound for the same reason as Option A**. The trigger
set "operations whose semantics differs between Int and BV" includes
*every fixed-width arithmetic operation*, because every fixed-width
Nim arithmetic op is silently modular. Once the trigger set is widened
to be sound, it covers all integer ops and the hybrid collapses to
Option B.

A user staring at the trigger list might object: "but `0..100` plus
`0..100` never overflows int32; why pay BV cost there?" The answer is:
that's the right intuition — but the soundness-preserving way to express
it is not a trigger-based hybrid. It's *abstraction* (Option B-prime
below).

### Option B-prime — BV floor with selective `Z3Int` abstraction proved sound

Use Option B as the *soundness floor* — BV[W] is always semantically
correct. Then, when the walker can statically prove that a variable's
value range fits inside a non-overflowing window for the operations
applied to it, **abstract** that variable to `Z3Int` for as long as
the proof holds. Z3 solves the Int formula; the result is back-translated
to BV at the abstraction boundary.

This is sound because we *proved* — at walker compile-time, before
emitting any Z3 — that the BV semantics and Int semantics agree over the
relevant value range and op set. The proof is the artifact; the
optimization is the consequence.

Failed abstraction is not a soundness loss, only a performance loss:
the variable stays BV, and the encoding remains Option-B-correct.

## Decision

**Adopt Option B-prime.**

Default `SymexSettings.integerSemantics = isOptimised`. The walker:

1. Encodes every fixed-width Nim integer as `Z3BitVec[sizeof(T)*8]` by
   default.
2. Runs a static range analysis (see § Abstraction layer) over each
   procedure's local variables.
3. Promotes a variable to `Z3Int` when range analysis proves the
   promotion sound. Records the promotion + its proof obligation in
   `Path.abstractions: Table[Symbol, AbstractionProof]` for audit.
4. Stays in BV when promotion fails.
5. Bridges Int↔BV at explicit cast points via `Z3_mk_int2bv` /
   `Z3_mk_bv2int` (both already in nim-z3).

User-facing override:

```nim
type IntegerSemantics* = enum
  isExact      ## BV[W] always. Sound, slowest, simplest. Use when
               ## the abstraction layer's static analysis is itself
               ## in doubt — escape hatch for the cautious user.
  isOptimised  ## BV[W] + selective Int abstraction proved sound.
               ## Default.
  isLoose      ## Int everywhere, no soundness proof. May produce
               ## false-positive witnesses. Research / educational
               ## mode only; prints a per-run banner on stderr.
```

`isLoose` is documented as **a footgun** — included because researchers
comparing symex performance across configurations occasionally need the
unsound baseline for parity studies, and because the per-run banner
makes the unsoundness loud. If no user adopts it within v1, drop in
Phase 9 cleanup.

## Abstraction layer — proof techniques for v1

The walker's static range analysis must produce a sound interval
`[lo, hi]` for each candidate variable. v1 supports three proof
techniques in increasing sophistication:

### 1. Range-type info from the type system

Nim's standard library exposes `range[lo..hi]`, `Natural`, `Positive`,
and user-declared `range` subtypes carry **exact, decidable** range
information at the type level. The walker reads `getType(sym)` and seeds
the range table directly:

```nim
proc f(x: range[0..100]): int = …
# walker seeds: ranges[x] = (0, 100)
```

This is the highest-yield technique. The intersection with proptest
[#111](https://github.com/coreyleavitt/proptest/issues/111) (refinement-type
derivation) means range-typed parameters are already idiomatic in
proptest-heavy code.

### 2. Refinement constraints from the predicate DSL

When the user passes a `constraint: proc(input: T): bool` to
`symexFind`, the DSL parser (ADR-0002) extracts symbolic range info
from the constraint expression:

```nim
symexFind(f, target, constraint = proc(x: int): bool = x in 0..100)
# DSL parser → range table: ranges[x] = (0, 100)
```

The DSL parser passes the extracted range info to the walker's range
table *in addition to* asserting the constraint to the solver as
`0 ≤ x ≤ 100`. Both happen; they reinforce each other.

### 3. Trivial interval arithmetic

For derived variables, compose the source intervals via standard interval
arithmetic:

| Op | Result interval |
|---|---|
| `a + b` | `[lo_a + lo_b, hi_a + hi_b]` |
| `a - b` | `[lo_a - hi_b, hi_a - lo_b]` |
| `a * b` | `[min(lo_a·lo_b, lo_a·hi_b, hi_a·lo_b, hi_a·hi_b), max(…)]` |
| `a div b` (b > 0) | `[lo_a div hi_b, hi_a div lo_b]` (signs adjusted) |
| `a mod b` (b > 0) | `[0, hi_b - 1]` |

The abstraction succeeds for a variable iff *every* operation in its
def-use chain produces an interval that fits in `[T.low, T.high]`
without overflow. As soon as one interval exits the window, that
variable demotes to BV for the remainder of the path.

The composition rule is monotonic: once a variable demotes to BV, downstream
variables that consume it inherit BV. This avoids the unsoundness of
"mostly-Int with surprise BV at the bottom".

### Operations that *force* BV

Bit-twiddling operations (`shl`, `shr`, `and`, `or`, `xor`, `not`) on
integer types have no faithful unbounded-Int counterpart and always
force the variable into BV, regardless of range info.

This is enforced at the walker's dispatch layer: the per-op handlers
for the bit-twiddling kinds skip the abstraction check.

## Consequences

### Intended

- The dominant case in real consumer code — range-typed loop counters,
  refinement-constrained parameters — runs at near-`Z3Int` speed.
- Bit-twiddling code (byte parsers, hash mixing) runs at full `Z3BitVec`
  cost, which is the right floor for correctness.
- The walker's per-AST-kind dispatch table has one BV path per op plus
  one abstraction check at variable-binding sites — modest implementation
  complexity.
- The `Path.abstractions` audit log gives users an investigative tool:
  "why did symex think this branch was reachable?" → look at which
  variables abstracted and check the proof obligations.

### Accepted as cost

- The abstraction layer is real code that has to be maintained. Its
  correctness is itself audit-worthy (`tests/tsymex_phase2_overflow.nim`
  is the regression test that pins it).
- `isLoose` is a deliberate footgun in the API surface, justified for
  research transparency.

### Deferred (each gets its own follow-up issue from Phase 0)

These would each enable additional abstraction opportunities but are
not in v1 scope:

1. **Loop-invariant inference**. When a loop body's range info is
   stable across iterations (induction-variable shape), promote the
   loop-carried variable to `Z3Int` for the whole loop. Phase 6
   k-unwinds without invariant tracking, so loops never promote in v1.
2. **Assertion-based range refinement**. `assert x > 0` tightens
   `ranges[x]` to `[1, hi_x]`. v1 ignores assertions during the
   abstraction pass.
3. **Refinement carried through user-defined function calls**. When
   the walker inlines a callee, the caller's range info doesn't flow
   into the callee's param ranges. v1 starts every inlined call with
   fresh (type-derived) ranges.

Each deferral preserves soundness; the cost is only missed promotion
opportunities.

## Validation

ADR-0001 is validated end-to-end by Phase 2 (`tests/tsymex_phase2_overflow.nim`):

- An input where the BV semantics says "branch reachable only with overflow"
  must be **rejected** by `isExact` and by `isOptimised` (both refuse the
  unsound witness), and **accepted** by `isLoose` with the banner printed.
- An input that fits the abstraction window must be solved measurably
  faster under `isOptimised` than under `isExact` on a benchmark with at
  least a 2× expected ratio.

If the abstraction layer is silently incorrect — promoting a variable
whose range eventually overflows — the overflow regression test
catches it before any user sees a false-positive witness.
