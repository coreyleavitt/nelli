# ADR-0005 — Float NaN/Inf semantics for the symex walker

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-06-06 |
| **Deciders** | proptest maintainers |
| **Supersedes** | — |
| **Superseded by** | — |
| **Related** | [SYMEX_PLAN.md § ADR-0005](../SYMEX_PLAN.md), proptest Phase 15 Cluster F, [nim-z3 v1.0.0 `z3/fp.nim`](https://github.com/coreyleavitt/nim-z3) |

## Context

IEEE 754 floating-point introduces two classes of exceptional values
— Not-a-Number (NaN) and infinity (±Inf) — whose semantics diverge
from the algebraic model that underpins the rest of the symex engine.
Both create correctness hazards if mishandled:

- NaN is **unordered** with respect to every value, including itself:
  `NaN < x`, `NaN > x`, `NaN == x`, and `NaN == NaN` are all `false`
  under IEEE 754. This violates the reflexive law of equality. A symex
  engine that models `==` with Z3's unbounded-equality predicate
  instead of Z3's FP-theory equality will silently produce unsound
  witnesses (it will claim `x == NaN` is satisfiable when it is not).

- NaN payloads: IEEE 754-2019 permits a NaN to carry a 51-bit payload
  (float64) or a 22-bit payload (float32) alongside the sign and
  quiet/signaling bit. These payloads are **not observable through
  any standard Nim language operation** under `-d:release`. The only
  way to observe them is via `cast[uint64](x)` or equivalent unsafe
  bit-manipulation. A proptest SUT, which is a pure Nim predicate, can
  never distinguish two NaN values by payload.

- Infinity arithmetic is well-specified by IEEE 754 and maps directly
  to Z3 FP-theory: `Inf + 1.0 == Inf`, `Inf - Inf == NaN`, `1.0/0.0
  == Inf` (under IEEE, which Nim uses on all common targets).

- Signed zero: `+0.0 == -0.0` is `true` under IEEE 754 equality and
  under Z3's `Z3_mk_fpa_eq`.

The engine must make a discrete choice for each of these cases. A
wrong choice either (a) admits witnesses that fail at Nim runtime
(unsoundness), (b) rejects witnesses that would succeed at Nim runtime
(incompleteness/false UNSAT), or (c) blows up solver performance
unnecessarily.

### The NaN-payload question is load-bearing

NaN payloads appear cosmetically irrelevant but have a direct impact
on the SMT encoding cost. If distinct NaN values are modeled, Z3 must
reason over the 52-bit payload space simultaneously with the
arithmetic. The FP theory in Z3 4.x handles this but the search space
expands: queries that incidentally touch a NaN-valued expression
become harder, and model extraction for NaN witnesses becomes
non-deterministic (Z3 may return any of ~2^52 NaN variants, requiring
a normalization step before comparison). For proptest, the user never
calls `cast[uint64]` in a SUT — the one operation that could observe
a payload — so modeling multiple NaN payloads adds cost with zero
observable benefit.

## Options considered

### NaN encoding

#### Option A — Single canonical NaN (`mkFpNaN[E,S]()`)

Model NaN as a single Z3 FP NaN value. Nim's `math.NaN` constant,
any runtime computation that produces NaN (e.g. `0.0/0.0`, `Inf - Inf`),
and any literal `NaN` in a SUT all map to the same Z3 NaN. The
`fpBitsToUint64` extractor returns a stable bit-pattern for the
extracted witness.

**Pros:**
- Deterministic NaN witnesses: every SAT model that includes a NaN
  produces the same bit-pattern. The proptest user sees a stable
  witness value.
- No payload search space: the solver can resolve NaN questions
  without ranging over 52-bit payload values.
- Correct for all observable Nim behavior: Nim's `isNaN(x)`,
  `classify(x)`, and all arithmetic operate identically on all NaN
  payloads under `-d:release`.

**Cons:**
- Technically unsound for a SUT that `cast`s a NaN to `uint64` and
  checks the payload bits. Such a SUT is not a well-formed proptest
  SUT (it uses unsafe bit manipulation), and the engine's documented
  scope excludes `cast` semantics, so this is an accepted limitation,
  not a soundness gap in scope.

#### Option B — Payload-distinct NaN family

Model NaN as a parameterized Z3 FP value where the payload bits are
a free bitvector. Every occurrence of NaN in the SUT is potentially
a distinct NaN.

**Pros:** Technically sound for `cast`-using SUTs.
**Cons:**
- Massively increases solver complexity on any path that touches a
  NaN. Z3 must explore 2^51 quiet-NaN variants (float64) simultaneously
  with the arithmetic constraints.
- Witnesses are non-deterministic: two runs with the same seed may
  extract different NaN bit-patterns, breaking proptest's
  determinism guarantee.
- No proptest user can write a SUT that observes payload bits without
  using `cast`, which is outside the engine's DSL scope.

**Rejected.**

### IEEE comparison semantics

#### Option C — Z3 FP-theory operators throughout (`Z3_mk_fpa_eq` etc.)

Use Z3's native FP-theory comparison operators for all float `==`,
`!=`, `<`, `<=`, `>`, `>=`. These honor NaN-unordered semantics
automatically: `NaN == NaN` evaluates to `false`, `NaN < x` evaluates
to `false` for all `x`.

**Pros:** Exactly matches Nim's observable comparison behavior.
Correct for all IEEE-754-conformant targets.
**Cons:** None at this scope.

#### Option D — Z3 structural equality for `==`

Use Z3's `Z3_mk_eq` (structural/universal equality) for float `==`.
Under Z3's type system, two `Z3Fp` values are structurally equal iff
their bit-patterns match — which makes `NaN == NaN` `true` structurally
even though it is `false` under IEEE. This diverges from Nim's runtime
semantics and produces unsound witnesses.

**Rejected.** Structurally equal NaN witnesses would pass the engine's
path condition but fail the SUT's body at Nim runtime.

### ±Inf encoding

#### Option E — Z3 FP-theory Inf constructors (`mkFpInf[E,S](negative: bool)`)

Positive and negative infinity map to `mkFpInf[11,53](negative=false)`
and `mkFpInf[11,53](negative=true)`. All arithmetic on Inf follows
Z3 FP theory, which matches IEEE 754 exactly (including `Inf - Inf
== NaN`).

**Pros:** Correct. No special cases needed in the walker.
**Cons:** None.

**Accepted by default** — no competing option proposed.

### Signed-zero semantics

#### Option F — Preserve signed-zero distinction in Z3 FP, rely on `Z3_mk_fpa_eq` for equality

Z3 FP theory correctly models `+0 == -0` as `true` via `Z3_mk_fpa_eq`.
The walker emits `mkFpZero[E,S](negative=true)` for `-0.0` literals
and `mkFpZero[E,S](negative=false)` for `0.0`. The equality operator
produces `true` for both pairs. Comparisons (`<`) treat `+0` and `-0`
as equal per IEEE 754.

**Pros:** Correct. Nim's observable behavior matches.
**Cons:** None.

**Accepted by default.**

## Decision

1. **Single canonical NaN.** All NaN values in the engine — from
   literals, from arithmetic producing NaN, from free-variable
   witnesses — use `mkFpNaN[11,53]()` (float64) or `mkFpNaN[8,24]()`
   (float32). NaN payload bits are not modeled. This is sound for all
   SUTs expressible in the proptest DSL.

2. **IEEE comparison operators throughout.** `==`, `!=`, `<`, `<=`,
   `>`, `>=` on float `SymVal` use `Z3_mk_fpa_eq` /
   `Z3_mk_fpa_lt` / `Z3_mk_fpa_leq` / `Z3_mk_fpa_gt` / `Z3_mk_fpa_geq`
   exclusively. `Z3_mk_eq` is never used for float operands.

3. **`NaN != NaN` is unequal in path conditions.** A SUT branch
   `if x == y` where both `x` and `y` are NaN will take the `false`
   branch in the engine, matching Nim runtime. A constraint
   `f == NaN` (equality to a NaN literal) is UNSAT in Z3 FP theory
   and the engine reports `sxUnsat`. This is intentional and correct.

4. **±Inf via FP-theory constructors.** `Inf` and `-Inf` from
   `std/math` map to `mkFpInf[11,53](negative=false/true)`. Arithmetic
   on Inf follows Z3 FP theory.

5. **Signed zero preserved.** `-0.0` literal maps to
   `mkFpZero[11,53](negative=true)`. `+0.0 == -0.0` is `true` via
   `Z3_mk_fpa_eq`, matching Nim's IEEE equality.

6. **Z3 FP theory selection.** The engine uses the
   `(set-logic QF_FP)` fragment implicitly via nim-z3's typed
   `Z3Fp[E,S]` API. No quantifiers are introduced in the float
   cluster. This keeps float queries in the decidable QF_FP fragment.

## Z3 FP-theory API mapping

| Nim operation | Z3 API | nim-z3 wrapper |
|---|---|---|
| `NaN` literal | `Z3_mk_fpa_nan` | `mkFpNaN[E,S]()` |
| `Inf` literal | `Z3_mk_fpa_inf` | `mkFpInf[E,S](negative=false)` |
| `-Inf` literal | `Z3_mk_fpa_inf` | `mkFpInf[E,S](negative=true)` |
| `-0.0` literal | `Z3_mk_fpa_zero` | `mkFpZero[E,S](negative=true)` |
| `x == y` | `Z3_mk_fpa_eq` | `proc \`==\`[E,S]` |
| `x < y` | `Z3_mk_fpa_lt` | `proc \`<\`[E,S]` |
| `x <= y` | `Z3_mk_fpa_leq` | `proc \`<=\`[E,S]` |
| `isNaN(x)` | `Z3_mk_fpa_is_nan` | `fpIsNaN[E,S]` |
| `isInf(x)` | `Z3_mk_fpa_is_infinite` | `fpIsInfinite[E,S]` |
| `isNormal(x)` | `Z3_mk_fpa_is_normal` | `fpIsNormal[E,S]` |
| `signbit(x)` | `Z3_mk_fpa_is_negative` | `fpIsNegative[E,S]` |
| NaN witness extraction | `Z3_mk_fpa_to_ieee_bv` + `Z3_get_numeral_uint64` | `evalFloat64Opt` (with `model_completion=true`) |

## Consequences

### Intended

- All IEEE 754 float paths in a SUT are modeled correctly and soundly
  for the observable-behavior scope.
- NaN witnesses are deterministic: the same SUT under the same seed
  always extracts the same NaN bit-pattern.
- Solver performance on float-heavy SUTs is not degraded by NaN-payload
  search.
- `isNaN(f)`, `isInf(f)`, `isFinite(f)`, `isNormal(f)` all have
  direct Z3 FP-native encodings (Cluster F, cycle F6).

### Accepted as cost

- A SUT that uses `cast[uint64](x)` to observe NaN payload bits will
  receive an incorrect witness (the engine produces a canonical NaN;
  the `cast` may produce a different bit-pattern on the target machine).
  Such a SUT is outside the documented DSL scope; the engine emits
  `feUnsupportedOp` for `cast` expressions.
- `classify(f)` returning `fcNaN` vs `fcSignalingNan` is not
  distinguishable by the engine (single-canonical-NaN decision). The
  engine defers `classify(f)` enum-result modeling to Phase 16 and
  emits `feUnsupportedOp` (classified, `severity: sevError`) for
  paths that branch on `classify(f)`.

### Deferred

1. **Signaling NaN distinction.** `fcSignalingNan` vs `fcNaN` in
   `std/math.FloatClass` is not modeled. Phase 16 backlog.
2. **Payload-distinct NaN witnesses for `cast`-using SUTs.** Out of
   scope for the proptest DSL; would require a separate `cast`-aware
   execution mode.
3. **Extended precision (float80 / `long double`).** Not a Nim ABI
   concern on the current target set; not modeled.

## Validation

ADR-0005 is validated by Cluster F cycle tests:

- F2 DoD: `proc f(x: float): bool = x == x` for the `NaN` path
  confirms `sxUnsat` (NaN literal constraint is unsatisfiable under
  Z3 FP equality).
- F4 DoD: `proc f(x: float): bool = not (x == x)` confirms `sxSat`
  (the NaN witness is reachable via the unordered-equality path).
- F7 DoD: extracted NaN witness verified via `classify(w) == fcNaN`
  (canonical NaN round-trips correctly through `fpBitsToUint64`).
- F6 DoD: `isNaN`, `isInf`, `isFinite`, `isNormal` produce `sxSat`
  with the appropriate witnesses; `classify(f)` emits
  `feUnsupportedOp` with `severity: sevError`.
