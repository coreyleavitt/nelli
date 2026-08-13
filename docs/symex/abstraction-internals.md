# Abstraction internals

The proof obligations that keep `isOptimised` mode sound, plus the
worked examples a user needs to understand "why did symex give me
*that* witness".

This is the user-facing companion to
[ADR-0001](ADR-0001-integer-semantics.md). The ADR records the
decision; this doc records the *intuition* and the *failure modes*
you'll see in practice.

## Why an abstraction layer

Direct BV reasoning is correct everywhere but sometimes slow. A
formula like `0 ≤ i ≤ 10000 ∧ 0 ≤ j ≤ 10000 ∧ i + j > 15000`
takes Z3 many BV operations to solve; in integer theory it's a
trivial linear-arithmetic query.

`isOptimised` mode keeps BV[W] as the floor — every concrete value
*is* a BV[W] — but tracks an *abstract interval* alongside.
When the interval provably stays within the BV window, the walker
substitutes the cheaper Z3-integer encoding for that value, with
no loss of soundness.

The key invariant: **a value's interval contains its concrete
runtime range.** Anything that would violate that invariant
(overflow, underflow, ambiguous-sign conversion) falls back to BV.

## The six proof obligations

Each obligation below is what `isOptimised` must satisfy for the
witness to be sound — i.e. for "Z3 says SAT" to mean "the program
on this concrete input would execute the satisfying path".

### O1 — Window containment

For a value `v: int W` (signed):

    interval(v) ⊆ [−2^(W−1), 2^(W−1) − 1]

Unsigned analogue: `interval(v) ⊆ [0, 2^W − 1]`.

If this holds, the integer encoding of `v` and its BV[W] encoding
agree bit-for-bit on every value the interval admits.

**Worked example**: `let x: int32 = readInput()`. The walker
allocates a fresh symbolic `x_sym: BV[32]` and assigns it
`interval(x) = [-2^31, 2^31 - 1]` — the widest int32 window. O1
trivially holds. If a downstream operation produces a value whose
interval would *exceed* the window, that operation falls back to
BV (see O3).

### O2 — Interval composition under monotone arithmetic

For binary ops where the result interval can be computed
exactly from the operand intervals (`+` on aligned-sign operands,
`*` on positive operands, etc.):

    interval(a op b) = composeInterval(interval(a), interval(b), op)

The composition function is implemented in
`src/nelli/smt/abstraction.nim::tryEvalInterval`. The closure
proof is structural: each composition rule is verified by hand
to produce an interval that contains every possible concrete
result.

**Worked example**: `let z = x + y` with `x ∈ [0, 100]` and
`y ∈ [0, 200]`. `composeInterval(+, [0,100], [0,200]) = [0, 300]`,
which fits in `BV[32]` (300 ≤ 2^31 - 1). O1 holds for `z`, so the
walker emits the addition in Z3-integer theory.

### O3 — BV window-exit fallback

When `composeInterval(op, ia, ib)` would produce an interval
that escapes the BV window:

    fitsBVWindow(result_interval, W) == false

the walker re-encodes both operands as BV[W] and performs the
operation in BV. The resulting value's interval is widened to the
full window.

**Worked example**: `let z = x * y` with `x ∈ [0, 65536]` and
`y ∈ [0, 65536]`. `composeInterval(*, …)` gives `[0, 2^32]`. For
`BV[32]`, the window is `[0, 2^32 - 1]` — *just barely* exceeds.
The walker promotes to BV. (Note this is conservative; the
*concrete* product might still fit, but proving so per-query is
more expensive than the BV operation itself.)

### O4 — Cross-representation reconciliation

When a Z3-integer-typed value flows into a context expecting BV
(e.g., a `BV[64]` parameter receives an `int` argument), the
walker emits `int2bv(value, W)` from nim-z3's bridge. The
reverse direction uses `bv2int`.

Both directions are bit-exact under O1: as long as the value's
interval fits in the target width, the conversion preserves the
encoded value.

**Worked example**: a callee with `proc(x: int32)` receiving a
Z3-int-encoded actual. The walker emits `int2bv(arg, 32)` at the
call site; the callee's body sees a `BV[32]`. The pre-call
interval is preserved (assuming O1 held for the actual), so the
callee's reasoning is unaffected.

### O5 — Assertion-based refinement (Phase 7 rectify round 2 / #134)

When the SUT contains an assertion `symexAssert(x op K)` with
`op ∈ {<, ≤, >, ≥, ==}` and `K` a concrete integer, the walker
mines that information *before* solving:

    refine(x, op, K) → interval(x) ∩ {values satisfying x op K}

This tightens the interval and may make further compositions fall
under O1's window guarantee.

The refinement only fires under non-`tAssertionViolation` targets —
under that target, the violating branch is the one we're trying
to solve, so we mustn't pre-constrain `x` to satisfy the
assertion. The check is in
`abstraction.nim::collectAssertRanges`.

**Worked example**: a SUT with `symexAssert(x < 100)` and a
later use of `x * x`. Without refinement, `x ∈ [-2^31, 2^31 - 1]`,
so `x * x` ∈ `[0, 2^62]` — falls back to BV under O3. With
refinement, `x ∈ [-2^31, 99]`, so `x * x ∈ [0, (2^31)^2 = 2^62]`
— still BV. But for `symexAssert(0 ≤ x < 100) ∧ x * x`, the
refinement gives `x ∈ [0, 99]`, so `x * x ∈ [0, 9801]` — Z3-int.

### O6 — Variant discriminator convex-hull range (Phase 11 cycle 9)

For a variant-typed parameter `p: T` with arms tagged
`{t_1, t_2, …, t_n}`, the discriminator's interval is recorded as:

    interval(p.kind) = [min(t_i), max(t_i)]

The actual *set* of legal discriminator values is `{t_i}`, which
may be non-contiguous for enums with explicit ordinals (e.g.,
`enum a = 1, b = 7, c = 100`). The convex hull `[min, max]` is a
sound over-approximation: any discriminator value outside it is
infeasible.

The exact set is enforced by a separate path condition built at
allocation:

    p.kind == t_1 ∨ p.kind == t_2 ∨ … ∨ p.kind == t_n

So gaps inside the convex hull (values *inside* `[min, max]` but
not in `{t_i}`) are rejected by the disjunction, while values
outside the hull are rejected by the interval. The two layers
together preserve soundness.

`isOptimised` mode logs an `AbstractionEntry` named
`"<param>.<discName>"` (e.g., `"s.kind"`) with `evidence:
aeTypeRange` and `derivation` recording the arm count. The disc
itself remains BV-encoded for v1 — full Z3Int promotion of disc
is tracked as a follow-up; see `docs/symex/PHASE11_PLAN.md`'s
deferral table #12.

**Worked example**: `proc f(s: Shape)` with
`type ShapeKind = enum skCircle, skSquare` and Shape a variant on
`kind: ShapeKind`. The audit log contains:

    AbstractionEntry(name: "s.kind", interval: [0, 1],
                     evidence: aeTypeRange,
                     derivation: "variant discriminator constrained "
                                 "to [0, 1] across 2 arms")

For a SUT path like `if ord(s.kind) > 5: …`, the abstraction layer
proves it infeasible without ever consulting Z3.

## Failure modes you'll observe

### "The witness is a giant number"

Z3's bit-vector theory has no a-priori preference for small
magnitudes. A SAT query like "find x such that x mod 3 == 0 and
x > 0" can return any positive multiple of 3, including
`0x4321a2b5...`. This is *not* unsound — it's just unergonomic.
The fix is to feed the witness through nelli's random/shrink
pipeline; symex finds reachability, the shrinker finds minimality.

### "sxUnknown when I expected sxSat"

The path made it through a loop k-unwind exhaustion, an opaque
proc, or some operation outside the supported fragment (which the
walker marked uncertain instead of failing hard). Each of those
sites is honest about admitting ignorance. The remedies:

- bump `maxLoopUnwind` if it's a loop;
- accept UNKNOWN as covered via `acceptUnknownAsCovered = true`
  if the uncertainty is from trusted code;
- refactor the SUT to keep the relevant reasoning inside the
  fragment.

### "sxUnsat when I think there's a witness"

Most often: an `symexAssume` precondition is over-constraining
the input domain, or your `symexAssert` is being mined for range
refinement and tightening past what you intended. Try removing
assumes/asserts incrementally.

Less often: a bug in the abstraction. If you have a small SUT
where `isOptimised` returns sxUnsat but `isExact` (force BV
everywhere) returns sxSat, that's a soundness bug — file an
issue with the SUT.

### "isLoose gave me a witness, isOptimised didn't"

`isLoose` is unsound by design — it ignores overflow. Its
witnesses can be *wrong* (the program would not actually take the
satisfying path). Treat it as an exploratory mode; the stderr
banner at startup is your reminder.

## Where to look in the code

| Concept | File | Symbol |
|---|---|---|
| Interval type | `src/nelli/smt/types.nim` | `Interval` |
| BV-window helpers | `src/nelli/smt/abstraction.nim` | `fitsBVWindow`, `bvWindow` |
| Interval composition | `src/nelli/smt/abstraction.nim` | `tryEvalInterval` |
| Assertion mining | `src/nelli/smt/abstraction.nim` | `collectAssertRanges` |
| Variant disc convex-hull log | `src/nelli/smt/runtime.nim` | param-loop `of itVariant:` (Phase 11 cycle 9) |
| Variant disc legal-tag disjunction | `src/nelli/smt/runtime.nim` | `allocateSym` `of itVariant:` |
| Z3int ↔ BV reconciliation | `src/nelli/smt/runtime.nim` | `bvToZ3Int`, `toZ3Int` |
| isLoose stderr banner | `src/nelli/smt/runtime.nim` | grep for `"isLoose"` |

## References

- ADR-0001 — the original decision and trade-off analysis.
- N. Bjørner, A.-D. Phan. *νZ — An Optimizing SMT Solver*. TACAS 2015.
  (Z3's bit-vector tactic landscape.)
- B. Dutertre, L. de Moura. *A Fast Linear-Arithmetic Solver for DPLL(T)*. CAV 2006.
  (Why integer theory is fast where it applies.)
- The classic interval-arithmetic textbook: R. E. Moore, R. B. Kearfott,
  M. J. Cloud. *Introduction to Interval Analysis*. SIAM 2009.
