# RFC — the trace as a first-class value, and properties over it

- **Status:** seed — composed 2026-09-03 from the post-0005 architecture
  survey. Not yet designed.
- Category: core
- Size: S
- Value: high
- **Depends on:** none.

## §0 — Thesis

Every checker in nelli accepts the same shape of property: a predicate on one
state.

- `stateful.nim:35-40` — `invariant: proc(s: S)`
- `bmc.nim:60-64` — `invariant: proc(s: S): bool`
- `bisim.nim` — `observe1`/`observe2` on a state pair
- `symbolic.nim:31-40` — `applyModel` over a history the caller assembled

A repo-wide search finds no LTL, no fairness, no `eventually`, no `until`, no
`leadsTo`. `stateful.nim:111` returns only the **final** state; the trace that
produced it is discarded and is not available to user code after a run.

**Consequence: every liveness property is currently inexpressible.** A queue
that never drains. A lock acquired and never released. A retry loop that never
terminates. A cache entry never invalidated. A leader election that never
elects. nelli cannot state these, let alone check them — and they are the bugs
that survive longest in real systems, because a final-state assertion cannot
see them.

## §1 — The second, quieter problem

There are already two unrelated notions of history in the library:

- `symbolic.nim`'s `LinEvent[OpId, Ret]` — `(threadId, invokeTime,
  responseTime, opId, observedRet)`, assembled by the *user*, consumed by
  `isLinearisable`.
- `stateful.nim`'s implicit step sequence — built by the engine, wrapped in
  spans (`stateful.nim:115,134`) so the shrinker can delete a command, and
  then **thrown away**.

`bmc` builds a third (its BFS plan), `bisim` a fourth (its lock-step pair
walk), `parallel` a fifth (`parallel.nim:257-265`, real-time stamped). Five
checkers, five private representations of "what happened," none reusable, and
the one the engine builds most carefully is the one the user cannot see.

This is the deep-module argument for the RFC. The temporal operators are the
headline; **one `Trace` type that all five checkers speak** is the structural
payoff, and it is what makes the operators cheap to add rather than a sixth
bespoke mechanism.

## §2 — Mechanism (sketch, not a design)

1. **`Trace[S, Cmd]` becomes a value** on the stateful report: the initial
   state, and per step the command, the arguments drawn, the resulting state,
   and any per-step observations. It is already constructed internally; this
   stops discarding it.

2. **A monitor algebra over traces** — `always p`, `eventually p`, `never p`,
   `p leadsTo q`, and weak fairness — compiled to incremental automata so each
   operator costs O(1) per step rather than a post-hoc scan.

3. **`bmcCheck` verifies temporal properties, not just invariants.** This is
   the real prize. BMC already enumerates every enabled firing breadth-first
   to a depth bound; running a monitor automaton alongside that BFS turns
   *"the invariant holds for every plan of length ≤ d"* into *"this temporal
   property holds for every plan of length ≤ d."* The README already calls a
   BMC pass a verification claim rather than a sampling result — this is what
   makes that claim worth the words.

4. **Falsification yields a minimal trace**, shrunk by the machinery that
   already exists: the step spans are already there for exactly this.

## §3 — Scope

**In scope.** The `Trace` type; migrating the five checkers onto it; the
monitor algebra; BMC over monitors; trace-shaped counterexample rendering.

**Out of scope.** Full LTL with nested until/release, CTL path quantifiers,
and any temporal *model checking* beyond the existing depth bound. The
operator set should be the small one that covers real bugs, not the complete
one that impresses.

## §4 — Open questions for the design phase

- **How much of LTL?** `always`/`eventually`/`never`/`leadsTo` + weak fairness
  covers the motivating bug classes. Adding `until` and nesting is a large
  jump in both implementation and user-facing complexity. Where is the line?
- **Fairness under bounded traces.** `eventually p` over a finite trace is
  only ever "not yet violated." Does a bounded run report `eventually` as
  inconclusive, or does BMC's exhaustiveness let it be a real verdict up to
  depth d? These are different claims and the report must not conflate them —
  the same over/under-approximation discipline RFC-0005 is building for symex
  applies here, in a different engine.
- **Trace size.** A long stateful run holds every intermediate state. Does
  `Trace` retain states, or replay to reconstruct them on demand?
- **Does `LinEvent` survive** as its own type, or become a `Trace` with
  real-time stamps? The concurrent case has genuinely more structure
  (overlapping intervals, not a sequence) — this may be a place where
  unification is wrong, and the design should say so explicitly rather than
  force it.

## §5 — First slice

`Trace[S, Cmd]` on the stateful report, with the existing per-step invariant
re-expressed as `always p` over it — same verdicts, same tests green, one
representation. That proves the type carries what the checkers need before any
operator is built on it.

## §6 — Why this one is cheap and high-leverage

It is the smallest of the four structural items, and it upgrades three
existing subsystems (stateful, bmc, bisim) rather than adding a fourth. It is
also a hard prerequisite for RFC-0009 (deterministic simulation), which needs
a trace representation and temporal operators as its oracle — building 0009
first would mean inventing a sixth private history and then reworking it.
