# RFC — deterministic simulation: the choice sequence as the scheduler

- **Status:** seed — composed 2026-09-03 from the post-0005 architecture
  survey. The largest item on the board; expect its own multi-round build.
  Not yet designed.
- Category: core
- Size: L
- Value: high
- **Depends on:**
  - RFC-0007 (trace-properties) — hard. Simulation needs a trace
    representation and temporal operators as its oracle. Building this first
    means inventing a sixth private history type and then reworking it.

## §0 — Thesis

nelli's founding claim is that **all nondeterminism is recorded choices, and
therefore shrinking is free**. That claim currently covers input values and
nothing else.

Scheduling is nondeterminism. Time is nondeterminism. I/O failure is
nondeterminism. nelli does not own any of them — so for concurrent code it
falls back to the same thing everyone else does, and inherits the same
irreproducibility.

`parallel.nim:242-266` spawns real OS threads and perturbs them with jitter
values drawn from the choice sequence. That is a genuinely clever half-measure
— the jitter *is* shrinkable (`parallel.nim:338-340`) — but the survey
confirms what is absent: no cooperative or deterministic scheduler, no
systematic interleaving enumeration, no partial-order reduction, no PCT, no
fault injection, no virtual clock. A racy failure reports `otFlaky`. That is
the honest diagnosis and a dead end for the user.

## §1 — What owning it buys

Make every yield point a draw, `now()` virtual, and each fault injector a
choice, and four things fall out of machinery that already exists:

- **Reproducibility.** A concurrency bug becomes a seed. Today it becomes
  `otFlaky`.
- **Shrunk schedules.** The shrinker minimizes the *interleaving* down to the
  smallest pattern that still exposes the race — which is the entire
  difference between a concurrency bug you can fix and one you can only stare
  at. No new shrinker work; schedules are choices.
- **Bug-depth guarantees.** PCT gives a probabilistic lower bound on finding
  any bug of depth ≤ d. A guarantee, not a hope.
- **Exhaustiveness where it is affordable.** DPOR makes small state spaces
  complete rather than sampled — the same upgrade `bmcCheck` gives to stateful
  models, applied to concurrency.

And the existing `isLinearisable` becomes the oracle over a *reproducible*
history rather than a real-time-stamped one, which is a strictly stronger
checker for free.

## §2 — Scope

**In scope.** A cooperative task abstraction with explicit yield points; a
scheduler that draws its decisions from the `DataSource`; a virtual clock;
pluggable fault injectors (message drop / reorder / duplication, partition,
disk error, clock skew, process pause); PCT and DPOR as scheduler policies;
`isLinearisable` and RFC-0007's monitors as oracles over the resulting trace.

**Out of scope, and this must be stated plainly in the RFC.** This does not
hijack Nim's threads, `async`, or the GC. It is a simulation runtime for code
*written against it*, the way FoundationDB, TigerBeetle, and AWS Shuttle work
— you get determinism because your code runs on the simulator's primitives,
not because the simulator subdues the real ones. Promising otherwise is how
this project would fail.

## §3 — Open questions for the design phase

- **What is a task?** Nim has threads, `async`/`Future` (which nelli does not
  currently touch anywhere — the survey found zero `Future` usage outside
  Windows process handles), and closures. A simulator needs a resumable
  computation. Which primitive, and what does user code have to look like?
  **This is the fork the whole RFC turns on** and it is a genuine one — the
  answer determines whether adoption costs a rewrite or an import.
- **Adoption path.** If user code must be written against simulator
  primitives, what is the on-ramp for code that is not? Is there a useful
  middle tier — model-level protocol testing, where the "system" is already a
  state machine and there is no real I/O to virtualize? That tier is reachable
  much sooner and may be where the first slice lives.
- **DPOR scope.** Full DPOR needs a happens-before relation over all shared
  state, which needs the simulator to own memory access. Restricting it to
  message-passing between tasks is far cheaper and covers the protocol cases.
  Which?
- **Relationship to `parallelCheck`.** Does the real-thread runner survive
  alongside the simulator (they answer different questions — real threads
  catch real memory-model bugs), or is it superseded?

## §4 — First slice

The load-bearing property is **a schedule that reproduces from a seed**. Not
the scheduler, not fault injection, not DPOR — a two-task simulation whose
interleaving is drawn from the `DataSource`, replays identically from its
seed, and shrinks to a minimal interleaving. Everything else in §2 is a policy
over that one mechanism, and none of it is worth building until that one runs
end to end.

## §5 — Why this is worth the size

Deterministic simulation testing is the most consequential idea in systems
testing of the last decade, and it has never been unified with a
property-based testing engine — because no PBT engine already owns its
nondeterminism as a shrinkable artifact. nelli does. The distance from here to
there is smaller for nelli than for anyone else, and the result is a category
no competitor occupies.

It is also the one item on the post-0005 board that is a *quarter*, not a
sprint. It should not be started while 0006/0007/0008 are open.
