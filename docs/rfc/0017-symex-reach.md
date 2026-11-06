+++
type    = "rfc"
id      = "0017"
title   = "RFC — symex reach: the walker gets past loops, call depth and branch fan-out on real code"
state   = "seed"
wiring  = "unproven"
review  = "unreviewed"
profile = "rfc-flow@6"
blocked_by = ["0016"]
size = "xl"
value = "high"

[[item]]
id       = "order"
title    = "Measure before building, or start with the expected winner?"
question = "Should the capability tracks wait on M1's census and benchmark to set their order, or should C1 (parametric summaries) start in parallel with M1 on the expectation that call depth dominates?"
state    = "open"
owner    = "corey"
kind     = "design"
reversible = "reversible"
recommendation = "order.A"
lean     = "No one has measured which limit costs the most on real code; every track is weeks of work with soundness risk, and M1 is days. Picking first by expectation is how the frontier default was set, reverted and left stale (§2.3)."

[[option]]
id    = "order.A"
of    = "order"
title = "M1 first; its census orders L, C, P and E"
cost  = "A few days before any capability work starts."

[[option]]
id    = "order.B"
of    = "order"
title = "M1 and C1 in parallel"
cost  = "If M1 shows loops or fan-out dominate, C1's weeks bought the smaller gain first."

[[item]]
id       = "loop-strategy"
title    = "How far past k-unrolling should loops go?"
question = "Is concolic trip-count concretization (L1) plus more idiom lifts (L2) enough, or should the RFC also commit to general loop summaries through Z3's CHC engine or k-induction (L3)?"
state    = "open"
owner    = "corey"
kind     = "design"
reversible = "reversible"
recommendation = "loop-strategy.A"
lean     = "In the prong role the fuzzer and PBT already supply concrete inputs, so L1 covers the common case cheaply. L3 is research-sized and its soundness story is the hardest in this RFC; commit to it only if M1 shows loops dominate after L1."

[[option]]
id    = "loop-strategy.A"
of    = "loop-strategy"
title = "L1 and L2 now; L3 only if M1, re-run after L1, still shows loop declines dominating"
cost  = "A loop whose interesting trip count no generated input reaches stays Unknown."

[[option]]
id    = "loop-strategy.B"
of    = "loop-strategy"
title = "Commit to L3 from the start"
cost  = "Weeks to months; Spacer has upstream defects nelli already works around (RFC-0016 §5.6), and every summary is a new soundness surface."

[[item]]
id       = "cross-module"
title    = "How should the walker see private callees in other modules?"
question = "A non-exported callee in another module has no body through `getImpl` and declines. Should the patched compiler expose those bodies, should users mark them, or should they stay declined?"
state    = "open"
owner    = "corey"
kind     = "design"
reversible = "one-way"
recommendation = "cross-module.A"
lean     = "nelli already ships a patched Nim, so a compiler hook adds one patch, not a new dependency, and needs nothing from users. Decide only after M1 counts how often this decline fires; if it is rare, C stands."

[[option]]
id    = "cross-module.A"
of    = "cross-module"
title = "A compiler patch that makes `getImpl` return private routine bodies to the symex macros"
cost  = "One more patch carried on every Nim bump; the toolchain diverges further from upstream."

[[option]]
id    = "cross-module.B"
of    = "cross-module"
title = "A user pragma (for example `{.symexVisible.}`) on the routines symex may read"
cost  = "Every consumer annotates its own code; anything it forgets still declines."

[[option]]
id    = "cross-module.C"
of    = "cross-module"
title = "Leave it declined"
cost  = "A helper-heavy module stays mostly Unknown."

[[slice]]
id    = "M1"
title = "Decline census and value benchmark on a pinned corpus (§3)"
state = "pending"

[[slice]]
id    = "L1"
title = "Concolic trip-count concretization: the generated input fixes the loop count, the solver works on the branch past it (§4.1)"
state = "pending"

[[slice]]
id    = "L2"
title = "More loop idiom lifts, chosen by M1's census (§4.1)"
state = "pending"

[[slice]]
id    = "L3"
title = "General loop summaries through CHC or k-induction, if item loop-strategy says so (§4.1)"
state = "pending"

[[slice]]
id    = "C1"
title = "Parametric call summaries: a callee walked once over fresh formals, instantiated by substitution (§4.2)"
state = "pending"

[[slice]]
id    = "P1"
title = "Path merging at if and case joins, generalizing S8w's short-circuit join (§4.3)"
state = "pending"

[[slice]]
id    = "P2"
title = "A measured default for maxFrontierSize, so fan-out declines instead of grinding (§4.3)"
state = "pending"

[[slice]]
id    = "E1"
title = "Private cross-module callees, per item cross-module (§4.4)"
state = "pending"
+++

# RFC — symex reach: the walker gets past loops, call depth and branch fan-out on real code

- **Status:** seed — composed 2026-11-05 after the 0.9.1 release, from a
  review of the walker's structural limits. The limits in §2 are read from the
  code at 1a02b496. Nothing past the slice sketch in §4 is designed, and the
  order of the tracks is an open fork (item `order`), **awaiting Corey**, as
  are `loop-strategy` and `cross-module`.
- Category: symex
- Size: XL
- Value: high
- **Depends on:**
  - RFC-0016 (native-parity-hardening) — hard for L3, C1 and P1, which add
    new verdict-producing models and so need its differential fuzzer (slice
    D1) to check them. Soft for M1, L1, L2, P2 and E1. Every slice here
    follows 0016's §2 rules: fail-closed allowlists, native pins on the same
    build, and walker version discipline.

**Path convention.** As in RFC-0016: bare `runtime.nim`, `types.nim`,
`canonicalize.nim` and `dsl_parser.nim` mean `src/nelli/smt/…`.

## §0 — Motivation

nelli has three prongs that feed one another: property-based testing, the
fuzzer, and symex. Symex seeds the PBT loop with witnesses (`symexForAll`,
`symex.nim:737`), flips branches the fuzzer is stuck on (`nelli/concolic`),
and checks coverage claims (`assertCoveredBy`). In that role a wrong symex
answer mostly costs efficiency, not correctness. A false `sxSat` witness runs
natively and misses. A false `sxUnsat` withholds a seed that random generation
or the fuzzer may still find. RFC-0016 owns the cases where a verdict is
trusted without a native run.

What the prong role does punish is reach. A decline is `sxUnknown`, and an
Unknown contributes nothing the other two prongs would not have found anyway.
RFC-0016 lifts declines one shape at a time. This RFC is about the structural
limits that decline whole classes of real code, whatever the shapes inside
them: loop trip counts, call depth, branch fan-out, and what the walker can
see.

## §1 — Scope

In scope: the four limits in §2, measured first (§3) and then raised (§4).

Out of scope:

- soundness parity and per-shape precision, which belong to RFC-0016;
- concurrency (threads, channels, async);
- I/O effects, which RFC-0011 (effect-annotations) covers;
- solver nondeterminism across threads, which is RFC-0016 PRC-32. It does
  matter here, because it adds noise to M1's benchmark, which §3 handles by
  repetition.

## §2 — The limits as they stand (read at 1a02b496)

### §2.1 Loops

`maxLoopUnwind` defaults to 5 (`types.nim:3400`). A loop is unrolled 5 times,
and a path that needs more iterations declines. Two kinds of idiom get past
the bound: bounded scans become a closed-form `indexOf` (ADR-0025), and
accumulating scans become closed forms (ADR-0028). Nothing else does. There
is no loop summary and no invariant inference, which SYMEX_PLAN still lists
as out of scope for v1. Any branch that needs a 6-iteration loop to reach it,
such as a parser over a 6-byte input, is `sxUnknown`.

### §2.2 Calls

`maxCallDepth` defaults to 3. Past it, `maxRecursionDepth` (24) keeps
inlining only while the frontier is not growing (RFC-0005 S8ax). Past both,
the call declines (`beBudgetExhaustedUnmodelled`). A native-stack check
declines earlier on small stacks (RFC-0005 S8ca).

There is a call cache (`CallCacheEntry`, `runtime.nim:16544`), and its doc
calls it a function summary. It is memoization, not a summary. A hit needs the
same actuals handle for handle (`cacheArgsSame`), and the same outer
globals and captures (`cacheOuterSame`, S8be). So a callee reached with
different symbolic actuals, which is what a call inside a loop or a recursion
produces, is walked again every time. Cost multiplies along the call graph,
and a five-deep helper chain is already past the default.

### §2.3 Branch fan-out

The walker forks one path per branch. It merges paths at exactly one kind of
join: the guard of a lowered short-circuit chain (`mergeJoinPaths`,
`runtime.nim:20534`, RFC-0005 S8w). Even there it merges only paths that
differ in scalars; a chain operand that writes a string, seq, heap cell or ref
still forks 2^m (RFC-0005's S8w remainder row). An ordinary `if` or `case`
join never merges.

There is also no default cap on the frontier. #163 set `maxFrontierSize`'s
default to 256 in 991b0ff1, and 90caaa18 reverted it to 0, which means
unlimited. The doc comment at `canonicalize.nim:2033` still says 256, and that
needs correcting. So code with many independent branches does not decline: it
grinds until the solver or wall budget runs out.

### §2.4 What the walker can see

The walker reads a routine through `getImpl` on a typed symbol. A callee
`getImpl` cannot resolve declines, and that includes a private routine in
another module (`dsl_parser.nim:20953`). Generic instantiations are capped at
64 per routine (`maxInstantiationsPerProc`, `types.nim:3443`, which raises
`geInstantiationCapped`). `method` calls are dispatched over the method
registry for the receiver's dynamic type (RFC-0005 S8bn), so they are not a
gap.

## §3 — Measurement first (slice M1)

No one has measured which of these limits costs the most on real code. M1
measures it before any capability track starts.

- **Corpus.** Pure functions from nelli's own `src/`, chapulin and amoxtli,
  copied into a benchmark tree and pinned at a sha. This reads consumer code
  as a workload. It is not building for a consumer: nothing here waits on a
  consumer's work, and nothing ships for one.
- **Census.** Run `symexFindAllWitnesses` over every function in the corpus
  and count verdicts per target: `sxSat` confirmed by replay, `sxSat`
  unconfirmed, `sxUnsat`, `sxRaised` and `sxUnknown`. Break the Unknowns down
  by the decline kind on their path (`SymexErrorKind`), grouped by the limit
  in §2 it belongs to. The census decides the order of §4's tracks.
- **Value benchmark.** On the same corpus, measure branch coverage against
  CPU time for PBT plus the fuzzer, with and without symex (`symexForAll`
  seeds and concolic assist). Run each configuration at least 5 times, because
  of PRC-32's spend noise. This is the number that says whether symex earns
  its place, and it becomes the before-and-after measure for every slice here.
- **Output.** A committed report, `docs/rfc/0017-symex-reach.m1.md`, with the
  corpus sha, the nelli sha and the build. It is re-run after each track
  lands.

## §4 — Capability tracks

Each track is a family of slices. M1 decides the order (item `order`). Every
slice states its soundness argument, adds its shapes to RFC-0016's
differential-fuzzer generator, and lands with native pins (RFC-0016 §2.2).

### §4.1 Loops (L1, L2, L3)

- **L1, concolic trip-count concretization.** When symex runs under the
  fuzzer or PBT, the generated input fixes how many times the loop runs. Walk
  that many iterations exactly, ask the solver only about the branch past
  them, and treat the trip count as an assumption on the witness, not a
  modelled fact. Replay confirms the witness, so the assumption costs
  completeness only. This has to work through `nelli/concolic`'s existing
  flip machinery. Its loop handling has not been read for this draft, and
  doing so is L1's first step.
- **L2, more idiom lifts.** Closed forms in the style of ADR-0025 and
  ADR-0028 for whichever loop shapes M1's census shows declining most.
- **L3, general loop summaries.** A loop becomes constrained Horn clauses
  solved by Z3's CHC engine (Spacer), or is proved by k-induction. This is
  research-sized, and it is the hardest soundness argument in this RFC. It is
  gated by item `loop-strategy`.

### §4.2 Calls (C1)

- **C1, parametric summaries.** Walk a callee once over fresh symbolic
  formals. Store each exit as a relation between the formals, the return
  value and the effects. At a call site, instantiate it by substituting the
  actuals. This replaces `CallCacheEntry`'s exact-actuals memoization for
  callees that qualify. It keeps the existing soundness conditions: no exit
  writes outer state (S8be), and the prune facts still hold (`pruneFactsHold`).
  It adds two of its own:
  - a summary is admitted only for callees on an allowlist of effect shapes
    (RFC-0016 §2.1);
  - a callee that declines anywhere inside it taints its summary, so the
    decline reaches every call site that uses the summary.

  User-written contracts are not in C1. They would add a trust boundary that
  the native-pin rule cannot check.

### §4.3 Paths (P1, P2)

- **P1, merge at `if` and `case` joins.** Generalize S8w's join: at the end
  of an `if` or `case`, merge surviving paths into one with an
  `ite`-selected environment, starting with arms that write scalars only.
  Then extend to S8w's remainder (strings, seqs, heap cells, refs), each
  extension being one allowlist entry with its pins.
- **P2, a measured frontier default.** Set `maxFrontierSize`'s default from
  M1's data, not a guess, so that fan-out declines with
  `beBudgetExhaustedPrune` instead of grinding. Record why #163's 256 was
  reverted (90caaa18) before choosing the new value, and fix the stale doc
  at `canonicalize.nim:2033`. This is a walker version bump.

### §4.4 Visibility (E1)

- **E1, private cross-module callees.** Implemented as item `cross-module`
  decides. Then measure the generic instantiation cap against M1's corpus,
  and raise it only if the census shows `geInstantiationCapped`.

## §5 — Exit

The RFC closes when each track has either landed or been recorded as not
worth its cost, with the M1 numbers behind that call. It also needs M1's
benchmark re-run on the final head, showing the change in the Unknown rate
and in coverage per CPU second against the M1 baseline. No target number is
set before M1 exists.

## §6 — Open forks

Items `order`, `loop-strategy` and `cross-module` in the front matter,
**awaiting Corey**.
