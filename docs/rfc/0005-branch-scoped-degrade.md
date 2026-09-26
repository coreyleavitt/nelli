+++
type    = "rfc"
id      = "0005"
title   = "RFC — soundness channels: separating over- from under-approximation"
state   = "draft"
wiring   = "unproven"
stage   = "rfc"
profile = "rfc-flow@3"
blocked_by = ["0001"]
size = "l"
value = "high"

[[item]]
id    = "i1"
title = "Round-2 cost: keep full scope (SAT replay half) in one RFC? Conditional on S0b's measured payoff"
state = "resolved"
owner = "corey"
lean  = "keep-one-rfc"
reason = "Corey 2026-09-25: /tdd rfc-0005 til done, do not defer anything -- full scope in one RFC, replay half included"

[[item]]
id    = "i2"
title = "Soften blocked_by 0001 to a builds-on edge (every 0001 dependency is landed)"
state = "open"
owner = "corey"

[[item]]
id    = "i3"
title = "feTransparentResultUsed/feTransparentArgNotInert: demote to sevWarning, or add a companion-anchored DeclineScope"
state = "resolved"
owner = "corey"
reason = "Corey 2026-09-26: neither -- they are not declines; moved to a separate verdict-neutral annotation-violation channel (AnnotationViolation on RawResult/SymexResult), enum members tombstoned; landed in S8 (§13.3)"

[[slice]]
id    = "S0"
title = "Exhibit: over-taint-only UNSAT + veto companion, green characterization pins"
state = "done"

[[slice]]
id    = "S0b"
title = "Measure the over-taint-only payoff before building (throwaway spike)"
state = "done"

[[slice]]
id    = "S1"
title = "Lattice + DegradeClass + classOf (conservative dcNoAnswer default) + carrier + degrade() funnel"
state = "done"

[[slice]]
id    = "S1b"
title = "Mint the missing kinds + runTaint/errors correspondence pin"
state = "done"

[[slice]]
id    = "S1c"
title = "Verdict rule: ordered procedure, candidate pool, isTargetLabel solve"
state = "done"

[[slice]]
id    = "S2"
title = "Replay substrate: ReplayOutcome, target-shaped replayWitness, stackable capture"
state = "done"

[[slice]]
id    = "S3"
title = "Taint-monotonicity harness: withPoisonedArm + battery"
state = "done"

[[slice]]
id    = "S4"
title = "Classify allocDegrade funnel; S0 exhibit flips to sxUnsat"
state = "done"

[[slice]]
id    = "S5"
title = "Classify degradeStrArm + R1 placeholder funnel"
state = "done"

[[slice]]
id    = "S6"
title = "Classify heap/halt sites + beBudgetExhausted/feUnsupportedOp splits"
state = "done"

[[slice]]
id    = "S7"
title = "Cross-path sinks + closure/HOF decline path taint"
state = "done"

[[slice]]
id    = "S8"
title = "DeclineScope carrier + Class-A/B unification + totality pin (vetoes retained)"
state = "done"

[[slice]]
id    = "S9"
title = "Delete both blanket vetoes"
state = "pending"

[[slice]]
id    = "S10"
title = "SAT relaxation: replay wired into verdict across both runSymex consumers"
state = "done"

[[slice]]
id    = "S11"
title = "Public surface: Soundness, gaps(), SymexFinding/render, cache schema, bound echo"
state = "pending"
+++

# RFC — soundness channels: separating over- from under-approximation

- **Status:** draft — **repurposed 2026-09-01; round 1 reviewed 2026-09-20;
  round 2 reviewed 2026-09-20.**
  This RFC was opened to carry RFC-0001's BLOCKER B7-2 ("case/else-raise
  sibling poisoning") on the premise that it needed a branch-scoped
  classified-degrade architecture. **That premise was wrong and B7-2 is fixed**
  (`cac15e6`, walker v124) — see §1. What survives is the genuinely valuable
  half, which B7-2 was never an instance of: the engine conflates two
  structurally opposite kinds of imprecision and throws away answers it has
  already earned. **Round 1 inverted the direction of the payoff** (§0.3) and
  raised Size M → L. **Round 2 found four unsound-as-specified mechanisms**
  (§2.3's missing candidate protocol, §2.5's closure-veto argument, §2.2's
  classification premise, and the S7/S8 slice boundary) and restructured the
  slice plan so a verdict flip lands at slice 6 instead of slice 10.
  **Round-1 forks are resolved in §12; round-2 forks are open in §13.**
- Category: symex
- Size: L
- Value: high
- **Depends on:**
  - RFC-0001 (chapulin-hardening) — the SND-1 taint machinery, the three-way
    carrier taxonomy, and the N36/N37/N39/N40 raise-to-in-band migration are
    all prior art this builds directly on. **Every item §1 names is landed;
    §13.2 asks whether the `blocked_by` edge should therefore become soft.**

**Path convention.** Bare `runtime.nim`, `types.nim`, `canonicalize.nim`,
`dsl_parser.nim`, `runtime_heap.nim`, `runtime_strings.nim` mean
`src/nelli/smt/…`; `markers.nim` means `src/nelli/engine/markers.nim`. This
matters for blast radius: **`runtime_heap.nim`, `runtime_strings.nim`,
`runtime_floats.nim`, `runtime_exceptions.nim` and `runtime_closures.nim` are
`include`d into `runtime.nim`** (`runtime.nim:892-898`, `:4902-5021`) — they
are one ~17.6k-line compile unit, not five modules. A slice touching two of
them touches one unit; a slice touching `runtime.nim` at all inherits the whole
unit as context.

## §0 — Thesis

### §0.1 The distinction

There are two ways the walker can be wrong about a program, and it currently
reports both as one undifferentiated `sxUnknown`:

| | mechanism | modelled behaviour set |
|---|---|---|
| **Over-approximation** | fresh unconstrained symbol | ⊇ real — *adds* behaviours |
| **Under-approximation** | path drop, prune, halt | ⊆ real — *removes* behaviours |
| **Incomparable** | forced concrete value, stale env, fabricated continuation | neither — *substitutes* behaviours |

Their soundness consequences are **dual**:

- **SAT is trustworthy if the path carries no over-approximation.** An
  under-approximation cannot invent a model — a witness found on a path that
  was merely *selected* from a smaller set is a real witness.
- **UNSAT is trustworthy if no path anywhere carried an under-approximation.**
  An over-approximation cannot hide a model — if the enlarged program has no
  solution, neither does the real one.

Both are **one-directional**: they license trust, they do not characterise it.
A witness on an over-tainted path may still be real, and §4.2's replay is
precisely the instrument that recovers those cases. The original draft stated
these as "iff"; that was wrong in the forward direction and is corrected here.

**The UNSAT rule quantifies over paths the engine actually solved.** A path
that reaches the target and is *skipped unsolved* is itself an omission — it
removes a behaviour from the searched set — so it contributes `scIncomplete`
regardless of why it was skipped. This is not a footnote: `isTargetLabel`
(`runtime.nim:11159-11168`) skips `trySolve` on every tainted path today, so
relaxing the verdict rule **without** also relaxing that skip mints a false
`sxUnsat`. §2.3 states the rule so this cannot be sliced apart, and §5 keeps
the two in one slice.

Note the asymmetry: **over-taint scopes to a path; under-taint is global.** A
sibling branch's garbage cannot invalidate a witness found and replayed on a
clean path, but an UNSAT claim is a statement about *all* paths, so one
under-approximated path anywhere voids it. §2.4 records the places taint
escapes a path into global solver state, where this asymmetry needs care.

### §0.2 The third class is not a corner case

The original draft's table had two rows. Round 1 established that the
**majority of current degrade arms belong to neither**. A site that
substitutes a *forced concrete value* — `defaultZero` (`runtime.nim:3532`),
the typed-zero dummy behind `mkUnsupported` in expression position
(`canonicalize.nim:2911-2915`), or the stale `env` left by a dropped
unmodelled statement (`runtime.nim:11326-11334`) — produces a behaviour set
that is neither ⊇ nor ⊆ the real one. It is *wrong*, not merely *coarse*.

Classifying such a site "under" mints a false `sxSat` (the S1 failure class,
inverted); classifying it "over" mints a false `sxUnsat` (the S1 failure class
itself — a placeholder whose `.len` silently read 0 produced a false `sxUnsat`
one line from a committed pin). Both are unsound. The only correct treatment
is **both channels at once**, which distrusts the path for SAT and the run for
UNSAT. This is why the carrier is a `set` (§2.1) and not a two-valued tag, and
it is the affirmative answer to the original draft's open question 2.

**Classification therefore keys on substitution semantics, not on the
mechanism's name.** §3 restates the rule and applies it.

### §0.3 Where the recovered capability actually is — *corrected*

The original draft claimed the payoff was on the SAT side and cited RFC-0001's
handoff for the opOack whole-proc search. **Round 1 found that citation
misread.** The handoff entry (`0001-chapulin-hardening.handoff.md`, B7 THIRD
PASS) reads:

> the whole-proc unconstrained **no-defect search** stays sxUnknown because
> the region-membership NON-member fallback still k-unrolls (maxLoopUnwind=5)

A no-defect search carries **no witness** and wants `sxUnsat`. K-unrolling is
under-approximating, and this RFC's own rule voids UNSAT under under-taint —
so that case stays `sxUnknown` after this change, correctly. It is not
discarded capability; it is an honest report of an unproven bound.

The draft's SAT-side framing also contradicted its own §1.3, which concedes
that a found witness already beats the global flag. Both are now corrected.
The real ledger:

**The SAT side is nearly closed already.** Paths that exit a loop within
budget are untainted (`runtime.nim:9509` forks the exit path with `not cond`
conjoined and *no* taint) and already reach `trySolve` and report `sxSat`. The
only paths the relaxed SAT rule newly admits are the **exhausted survivors**
(`runtime.nim:9555`: `survivors.add forkPathTainted(p, p.pc, p.env)` — `pc`
still carries `cond = true` from iteration k, `env` frozen there, and no exit
constraint is ever conjoined). Post-loop code then executes on a trajectory
the real program never takes, because the real program is still looping. That
is a **fabricated continuation** — the §0.2 incomparable class — so it is
distrusted for SAT by construction, and the k-unroll payoff is *empty* unless
a witness found there is replay-confirmed against the real function (§4.2).

**So state it plainly: the SAT half's entire live payoff is two mechanisms** —
the blanket-veto deletion of §2.5 and the raise-routing recovery of §2.6 — and
both are now pinned in §6. Round 2 added this sentence because §6 previously
pinned only the replay-gated cases, i.e. the half this section calls empty; a
reader could discharge every SAT DoD item without the SAT half ever changing
an observable verdict.

**The UNSAT side is where the capability is, and it is measurable.** Today
*any* degrade sets `w.sawUnknown` (52 write sites in `src/`), and `sxUnsat` is
reported only when it never fired (`runtime.nim:13576-13595`). So a run whose
only imprecision is over-approximating — a fresh unconstrained placeholder, an
`mkUnsupported` on an untaken arm — proves the target unreachable and is told
to report `sxUnknown` anyway. Under the channel rule that is a sound
`sxUnsat`. The population is **272 `== sxUnknown` assertions across 110 test
files** at HEAD; the subset whose runs are over-taint-only is the measured
payoff. **Round 2 moved the count to the front of the plan** (slice S0b, §5):
the original plan counted it at slice 8, which is eight slices spent before
learning whether the payoff is non-empty. §0.2's own finding — that the
*majority* of degrade arms are `⊤`, which never flips — makes a near-zero
count a live possibility, and §13.1 makes that outcome a scheduled fork rather
than a late surprise.

This reframing does not shrink the RFC's value — it relocates it, and
relocates it onto the half RFC-0011 is blocked on (§8.2).

### §0.4 Why the distinction unifies past work

It unifies findings RFC-0001 fixed one at a time. **S1** — the placeholder seq
whose `.len` silently read 0, producing a false `sxUnsat` — was an
*incomparable* site treated as sound. **Bug #2**'s field poisoning was an
over-approximation applied globally instead of per-read. **N20**'s k-unroll is
under-approximating, which is precisely why its own note that "verdict stays
correct either way" holds. Three separate slices, one missing distinction.
These are history, not pending flips; they motivate the taxonomy, they do not
quantify the payoff. §0.3 quantifies the payoff.

## §1 — What is already true (do not re-derive)

Read the source before designing against it. Five things that are **not** what
RFC-0001's escalation implies:

1. **B7-2 was a parser gap, not an architecture gap. FIXED `cac15e6`.**
   `case` as a statement was always modelled; `case` as an *expression* had no
   `parseExpr` arm and declined `feUnsupportedExprKind`. The "sibling
   poisoning" was downstream: the declining proc is a callee, parsed whole-proc
   at registration **before any path exists**, so the decline had no path to
   scope to. Fixed by the A-normalisation M5 already applied to `nnkIfExpr` at
   walker v50. No architecture was required.

2. **The raise-to-in-band migration already happened for `allocDegrade`'s
   arms** — N36/N37/N39/N40, walker v101–v104, in the 0.5.1 fix loop.
   `allocDegrade`'s own comment records that those arms "previously `raise`d."
   RFC-0005's original framing described this as the large unstarted refactor.
   It is substantially done — but **not complete**: `runtime.nim:64-213`
   documents a residual class still "Caught at the `runSymex` boundary →
   sxUnknown". Those whole-walk aborts discard already-found winners and can
   carry no path-scoped channel at all. §3.3 rules on them.

3. **A witness beats `sawUnknown` — but not the two blanket vetoes.** The
   verdict is `if w.found.len > 0 and not capForcedUnknown and not
   closureForcedUnknown:` (`runtime.nim:13536`). `capForcedUnknown`
   (`13497-13510`) fires on **any** `sevError` in `prog.parseErrors`,
   deliberately including constructs guarded behind an unreachable branch that
   no walked path ever touched (`13492-13495`); `closureForcedUnknown`
   (`13519-13523`) fires on any `sevError` closure-call error. So the SAT half
   is path-scoped for exactly one of three unknown-forcing channels. The
   original draft's claim 3 named only the first. §2.5 decides the other two.
   **Round 2 correction:** the closure veto is not redundant machinery — it is
   today the *only* soundness barrier for a set of value-substituting closure
   sites that set `sawUnknown` and record a `closureCallErrors` entry but
   **never taint any path** (§2.5, verified list). Deleting it before those
   sites carry path taint is unsound.

4. **Per-path taint exists and is well built — with two escape hatches.**
   `Path.uncertain` (`runtime.nim:479`), `forkPathTainted` (24 live call
   sites — regenerate the inventory in the slice; round 1's "25" is off by
   one), and an internal template deliberately shaped so that "drop the taint"
   is unspellable. But `runtime_heap.nim:337` and `runtime_heap.nim:990` mutate
   `p.uncertain = true` / `child.uncertain = true` **directly**, bypassing that
   discipline; §2.2 closes both — with a *mutation-shaped* primitive, because
   neither site is fork-shaped. The Invariant-7 mechanism is a drain-time
   **backstop that stamps** `weInternalWalkerFault` on an empty-errors
   `sxUnknown` (`runtime.nim:13577-13589`) — it detects the class after the
   fact, it does not prevent it. The original draft called it an assertion.

5. **Exceptions may not be caught below the top frame on this toolchain.**
   RFC-0001's B7r2 prototype established that wrapping even ONE non-top-level
   `seq[Path]`-returning recursive call in `try`/`except` causes the
   classified-degrade exception to **never be raised at all** (Nim
   2.2.10-patched, C backend, ORC, `--exceptions:goto`, `--threads:on`;
   bisection-isolated, fully reverted). This constraint lived only in the 0001
   handoff. It is binding here: channels ride fields and in-band returns, as
   `uncertain` does now. No design in this RFC may introduce a non-top-level
   catch.

So the remaining work is **narrower in mechanism and wider in surface** than
the original seed claimed: classify each existing degrade by substitution
semantics, carry two channels on the taint, and make the verdict rule consume
them.

## §2 — Design

### §2.1 The lattice

```nim
SoundnessChannel* = enum
  scSpurious    ## over-approximating: modelled ⊇ real. A witness on such a
                ## path may be spurious. Blocks sxSat for THIS path.
  scIncomplete  ## under-approximating: modelled ⊆ real. A proof over such a
                ## run may have missed behaviours. Blocks sxUnsat RUN-WIDE.

Taint* = set[SoundnessChannel]
```

`Taint` is the powerset lattice on two elements: `⊥ = {}` (clean, the identity
of join), `⊤ = {scSpurious, scIncomplete}` (incomparable — §0.2), join is set
union. The existing return-merge `p.uncertain or cp.uncertain`
(`runtime.nim:11083`) becomes `p.taint + cp.taint`; union replaces OR with no
special case.

**The join does not swap channels under negation.** *(Round 2 replaced the
original argument, which was not a proof.)* The original text argued from
images — "if S ⊇ R then f(S) ⊇ f(R), including f = boolean negation". Branching
does not apply a function to a behaviour set; it **conjoins different
predicates** on the two sides (the model constrains a havoc symbol `h`, reality
constrains the modelled-away expression `e(x)`), and intersection preserves ⊇
only against the *same* constraint. The property that actually holds is
**per-trace simulation**:

> Let a `{scSpurious}` site introduce symbol `h` **unconstrained at the point
> of introduction**. Then for every real trace `t` there is a model trace `t′`
> agreeing with `t` on every non-degraded variable and taking the same arm at
> every branch — because `h` is free, so whichever arm `t` takes is satisfiable
> in the model. Hence each arm's modelled behaviour set contains the
> corresponding real arm's set, for **both** polarities, and equally for
> `isAssume`'s filter as for `isIf`'s fork.

The hidden premise is load-bearing and is therefore an **invariant, not an
aside**: *a `{scSpurious}` site's symbol carries no constraints at
introduction.* Sites that violate it — `defaultZero`, the typed-zero dummy,
any forced value — are exactly §0.2's incomparable class, which makes §0.2 a
corollary of this invariant rather than an independent assertion. §6 pins it.

The over/under duality appears **only at consumption** (§2.3): SAT reads the
winning path's `scSpurious` coordinate, UNSAT reads the run-global
`scIncomplete` coordinate. This holds *because* the taint is path-level. A
value-level channel would need negation-swap join rules; §9.3 dismisses that
design for exactly this reason.

**Only two of the four coordinates are consumed by the verdict** —
`path.scSpurious` and `run.scIncomplete`. `run.scSpurious` is diagnostics-only
(it drives §8.1's actionability) and `path.scIncomplete` is inert. That is
deliberate: uniformity is worth two idle bits, and stating it here is the
answer to "why does a pure-omission site put `{}` on the path?", which every
future classifier-author would otherwise re-derive.

**Naming.** Members are named for the failure mode, not the direction, so the
verdict rule reads self-evidently: `if scSpurious notin winnerTaint: sxSat`,
`if scIncomplete notin runTaint: sxUnsat`. "Over-/under-approximation" stays
in doc comments as the literature cross-reference. May/must is rejected — it
renames the confusion rather than removing it.

### §2.2 Where the channel lives — path-level, derived from a named class

**Carrier.** `Path.uncertain: bool` → `Path.taint: Taint`
(`runtime.nim:479`); `w.sawUnknown: bool` → `w.runTaint: Taint`, with
`sawUnknown ≡ runTaint != {}`. The existing value-level placeholder pattern
(`isUnsupportedFieldPlaceholder` / `seqUnsupportedFieldReason` /
`seqUnsupportedFieldKind`, `runtime.nim:340-364`) is **retained unchanged** as
the deferred-taint mechanism: it stays inert until a read converts it to path
taint via `placeholderReadDeclineKind` (`runtime.nim:3671`), which now supplies
the channel for free. That pattern already delivers the per-read precision
Bug #2 needed without threading a join through every combinator.

#### The classification is a named class, not a pair of set literals

Round 1 specified `func channels(k): tuple[path, run: Taint]` with four arms
returning set-literal pairs. **Round 2 rejects that encoding**, on evidence
from the RFC itself: the k-unroll exhausted survivor — which round 1 called
"the motivating case" for returning a pair — needs
`({scSpurious, scIncomplete}, {scIncomplete})`, and **no arm of round 1's own
sketch produced it**; §3.1 patched it with a parenthetical footnote on one
table row. A four-coordinate product of 2-element sets has 16 states, five of
which are meaningful, and the author of the sketch silently got the flagship
row wrong. Name the five classes and derive the coordinates:

```nim
type DegradeClass* = enum
  dcFreshSymbol   ## substitutes a fresh unconstrained symbol: modelled ⊇ real
  dcSubstituted   ## forced value / stale env: modelled neither ⊇ nor ⊆ real
  dcFabricated    ## the survivor path is fiction, but the omission is real:
                  ## ⊤ on the path, {scIncomplete} on the run (k-unroll survivor)
  dcOmitted       ## path drop / halt / prune: modelled ⊆ real
  dcNoAnswer      ## Z3 unknown / walker fault: no modelled program exists

func classOf*(k: SymexErrorKind): DegradeClass
  ## THE exhaustive case — one word per kind. The compiler rejects a new
  ## unclassified kind. This is §3.4's deliverable, in code.

func pathTaint*(c: DegradeClass): Taint =
  case c
  of dcFreshSymbol:                            {scSpurious}
  of dcSubstituted, dcFabricated, dcNoAnswer:  {scSpurious, scIncomplete}
  of dcOmitted:                                {}

func runTaint*(c: DegradeClass): Taint =
  case c
  of dcFreshSymbol:                            {scSpurious}
  of dcSubstituted, dcNoAnswer:                {scSpurious, scIncomplete}
  of dcFabricated, dcOmitted:                  {scIncomplete}

func channels*(k: SymexErrorKind): tuple[path, run: Taint] =   ## convenience
  (pathTaint(classOf(k)), runTaint(classOf(k)))
```

The taint algebra is now written once in ten lines. A `classOf` row is a
reviewable **judgment** — "`beBudgetExhaustedKUnroll` is `dcFabricated`" —
checkable against §3.1's rule by reading one word, instead of a coordinate pair
whose correctness requires re-deriving the semantics per row. The eleven
meaningless states become unconstructible, the fifth class gets a name instead
of a footnote, and `DegradeClass` turns out to be exactly the user-facing lever
taxonomy §8.1 needs.

#### The premise "every taint site has a kind in hand" is false — enumerate the exceptions

Round 1 asserted that "every taint-introducing site already has a classified
`SymexErrorKind` in hand at the moment it taints" and that the 24 call sites
make the migration mechanical. **Verified false at these sites**, each of which
is a slice obligation, not a detail:

| site | what is missing |
|---|---|
| `isUnsupported` walk arm (`runtime.nim:11322-11338`) | `forkPathTainted` with **no `SymexErrorInfo` in the arm at all**. The IR node carries only free text (`mkUnsupported(reason)` → `IRStmt(kind: isUnsupported, reason)`, `types.nim:3398`). Requires `mkUnsupported(kind, reason)` across ~40 emitting sites in `dsl_parser.nim` + `canonicalize.nim`. **This is §0.2's flagship incomparable example.** |
| recursion cycle-break (`runtime.nim:10855-10864`) | fresh `_cyc` retSym + `forkPathTainted`; **no kind exists for this degrade** — mint one |
| over-cap missing-callee (`runtime.nim:10700-10722`) | `forkPathTainted`; kind lives only in `prog.parseErrors`, not at the site |
| `trySolve` returning `zsUnknown` (`runtime.nim:7524-7525`), consumed at `:11167` and `:11491` | bare `w.sawUnknown = true`; **no error minted**. The `ekZ3*` kinds §3.1 cites are minted only from *raised* Z3 exceptions (`:12860-12863`), never from an unknown *result*. Consequence today: a run whose only degrade is a solver resource-out reaches the Invariant-7 backstop with empty errors and is stamped `weInternalWalkerFault` — "walker classification gap" — for routine solver exhaustion |
| handler-stack re-raise (`:11226`), diverged closure body (`:11866`), break/continue outside loop (`:9564`, `:9574`), `isTargetLabel`'s two writes (`:11162`, `:11167`) | bare `sawUnknown`, no kind |

Minting the missing kinds is slice S1b and is a **precondition** for the
derivation rule below.

#### The run coordinate is derived, not written

Round 1 would have migrated ~52 `sawUnknown = true` writes into ~52
hand-written `w.runTaint = w.runTaint + …` joins, each free to disagree with
the kind recorded one line above it — and `forkPathTainted` cannot absorb the
run join, because the template (`runtime.nim:669`) has no `w` in scope. That is
a second source of truth, which §10 row 5 already forbids for `forcedBy`.

**Decision: `w.runTaint` is derived at drain time** as the union of
`runTaint(classOf(e.kind))` over every drained `sevError` in the existing error
seqs (`walkDegradeErrors`, `parseErrors`, `closureErrs`,
`loweringDegradeErrors`, heap sinks). The empty-error `sxUnknown` case is the
existing Invariant-7 backstop → `⊤`, which is §2.5's bucket 3 verbatim. Two
consequences to hold:

- It requires **error-pairing totality** — every degrade records an error.
  That is exactly what S1b's kind-minting delivers, and
  `tests/tsymex_r6_degrade_pairing_audit.nim` already pins part of it.
- It requires a **severity rule**. `sevWarning` kinds must not taint by
  default — but §3.1 now has a row for the one that should
  (`eeUnknownExnType`, which substitutes behaviour; see §3.1).

**Path taint stays written**, because `errors` carries no path association —
nothing can re-derive *which* entries were on the winning path. §10 row 5 is
corrected accordingly: the derivation principle is true of the run coordinate
only.

#### One funnel performs all three acts

A degrade site today performs three acts (`runtime.nim:9516-9556` is the
canonical shape): set `sawUnknown`, add a `SymexErrorInfo`, fork a tainted
survivor. Round 1 disciplined only the third. Discipline all three from one
kind mention:

```nim
proc degrade(w: var WalkCtx; kind: SymexErrorKind; msg: string): Degrade =
  ## The ONLY way to obtain a `Degrade` token. Records the SymexErrorInfo, so
  ## the drain-time derivation of `w.runTaint` sees it. Recording and
  ## classification cannot disagree: there is one kind mention.
  w.walkDegradeErrors.add SymexErrorInfo(kind: kind, severity: sevError, msg: msg)
  Degrade(path: pathTaint(classOf(kind)))

template forkPathTainted(parent: Path; pcExpr: seq[Z3Bool]; envExpr: Env;
                         d: Degrade): Path =
  forkPathWithTaint(parent, pcExpr, envExpr, parent.taint + d.path)

proc taintInPlace(p: Path; d: Degrade) =   ## the runtime_heap.nim:990 shape
  p.taint = p.taint + d.path
```

The token handles the one-error-many-survivors shape for free (`let d =
w.degrade(…)` once, then `forkPathTainted(p, p.pc, p.env, d)` per survivor —
exactly the `:9555` loop). Halt sites (`heapDepthExhausted`, `isUnsafeCast`)
call `discard w.degrade(…)` and return: **no path act at all**, matching the
rule that a halted path needs no carrier. `runtime_heap.nim:337` is a halt and
therefore loses its mutation entirely; `:990` uses `taintInPlace`. Round 1's
"route both through the same helper" was shape-wrong for both.

**Scope the totality claim honestly.** Compile-time totality is real at
`classOf`'s exhaustive `case` and at `forkPathTainted`'s required `Degrade`.
It is *not* achievable for direct field writes: `runtime_heap.nim` and
`runtime_strings.nim` are `include`d into `runtime.nim`, so there is no module
boundary to hide `Path.taint` behind. Close that class the way this codebase
already closes such classes — a structural pin (the `.drift` / marker-scope
idiom): a test that `command grep`s `src/` for writers of `.taint` / `.runTaint`
outside the sanctioned primitives and asserts the list is exactly the expected
set. The remaining spellable mistake — reusing an **existing** kind at a site
whose substitution class diverges — no mechanism can check; §3.2 makes it a
stated rule.

Minimum ceremony for next year's engine author: append the enum member, add
one `classOf` arm (the compiler forces it), call `w.degrade(kind, msg)`.

`loweringDidDegrade: bool` (`runtime.nim:1400-1403`) becomes
`loweringPendingTaint: Taint`, subsumed at the drain (`runtime.nim:8812-8816`).
That drain's documented attribution slop (`runtime.nim:1352-1355`) is
conservative-safe under union *for misattribution* — but `runtime_heap.nim:838-862`
records empirically that the pending flag can be **lost entirely**, and a lost
`{scSpurious}` leaves a havoc value on a clean path → an unreplayed `sxSat`.
S1 therefore pins `loweringPendingTaint == {}` at walk end, extending the
Invariant-7 backstop to pending-taint leaks.

This answers the original draft's open question 3 — the channel **rides the
existing sinks**; no fourth taxonomy column on `SymexErrorInfo` for the
*channel*. (§2.5's decline **scope** is different data and does need a carrier;
see there.) And it answers open question 1's heap-depth case: a halted path
needs no surviving carrier, because its contribution is run-global by
construction.

### §2.3 The verdict rule — an ordered decision procedure

Round 1 stated the rule as four bullets. Round 2 found four states they leave
unresolved, two of which mint the failure classes this RFC exists to prevent,
and one of which turns the relaxation into a **regression** against today's
engine. The rule is therefore restated as an ordered procedure with disjoint
guards, against the real code (`runtime.nim:13524-13595`, `shouldStop` at
`:8212-8221`, `isTargetLabel` at `:11156-11168`).

**Candidate lifecycle.** `isTargetLabel` must solve `scSpurious`-tainted paths
(today it skips `trySolve` outright, `:11162-11167`) and a SAT result becomes a
**candidate**. Candidates are held in `w.candidates: seq[RawResult]`, a
separate pool — *not* in `w.found`. This is structural, not a filter predicate,
for one reason: `shouldStop` (`:8212-8221`) halts the entire walk on the first
`sxSat` in `w.found`. If a candidate entered `w.found` it would halt
exploration before a clean witness on a sibling path was ever solved; if replay
then refuted it, the verdict would be `sxUnknown` **where today's engine
reports `sxSat`**. The relaxation must not be able to lose a verdict the engine
already earns.

**Ordered procedure** (first matching rule wins):

1. a clean `sxSat` in `w.found` (`scSpurious notin path.taint`) → **`sxSat`**
2. a clean `sxRaised` winner → **`sxRaised`** (a reachable raise is an
   existence claim, so it obeys the SAT rules verbatim; the *absence* of a
   raise is a universal claim and falls under rule 5)
3. a candidate whose replay returns `roConfirmed` (§4.2) → **`sxSat`** /
   **`sxRaised`**, carrying `replay = rsConfirmed`
4. **any solved SAT on any path — candidate included, replay outcome
   irrelevant — terminally blocks `sxUnsat`.** A candidate that fails replay
   falls to `sxUnknown`, never to `sxUnsat`: the enlarged program *does* reach
   the target, and only reality is unknown. Round 1's bullets permitted reading
   "no witness" as "no *confirmed* witness", which mints a false `sxUnsat`.
5. no solved SAT anywhere and `scIncomplete notin runTaint` → **`sxUnsat`**
   (§0.3's recovered capability)
6. otherwise → **`sxUnknown`**, carrying `runTaint`

Rules 1–2 before 3 fixes the scan-order hazard: today the winner scan takes the
first `sxSat` in **discovery order** (`:13537`), so without an explicit order a
tainted-but-confirmed candidate could shadow a clean witness found later, and
the public result would carry `pathTaint != {}` when a taint-free answer
existed. A refuted candidate must likewise never shadow a live clean
`sxRaised`, and must not leak into the non-winning-raise diagnostics protocol
(`:13555-13566`).

**The unsolved-skip is itself an omission.** Any path that reaches the target
and is not solved contributes `{scIncomplete}` to `runTaint` — this is §0.1's
corollary and it is what makes rule 5 sound. It also means rule 5 and the
`isTargetLabel` solve **cannot be sliced apart**: shipping rule 5 while
`isTargetLabel` still skips tainted paths mints exactly the false `sxUnsat`
this RFC exists to prevent. §5 keeps them in one slice.

`w.found` and `w.candidates` entries gain `pathTaint: Taint` recorded at
target-hit time (`RawResult`, `runtime.nim:538-570`), because the winning path's
taint is not otherwise available at verdict time. Because replay must run in
macro-generated code (§4.2), `RawResult` must also carry candidacy across the
`runSymex` boundary in a form that **cannot be mistaken for a plain `sxSat`** —
see §4.2's plumbing note.

### §2.4 Cross-path sinks

"Over-taint scopes to a path" is true of forks, and *not* true of the places
taint escapes a path into global solver state. Each needs a per-channel
admission rule, because an under-tainted sub-path baked into a global axiom
can hide models run-wide, and an over-tainted one can fabricate them run-wide:

| sink | site | rule |
|---|---|---|
| closure ground axioms | `runtime.nim:8302-8316`, `:11762-11785` | mint only from `taint == {}` sub-paths (today: skips `uncertain`) |
| callee summary cache | `runtime.nim:11041-11053` | admit only `taint == {}` (today: gated on `not uncertain`) |
| fresh-`Path` constructions | `runtime.nim:11729-11730` (`descentBase`, the actual hardcoded `uncertain: false`), `:13346` and `:14214` (roots), `:690`/`:704` (H1 test hooks) | audit each against the new type |
| `parseIntGateConstraintsLive()` | drained into every check, `runtime.nim:7481-7496` | per-channel disposition; minted per-occurrence during string lowering |
| `currentClosureCallAxioms` | same drain | per-channel disposition |
| `stripDecompConds` | same drain; minted on a live path at `runtime_strings.nim:760` | per-channel disposition |
| `defectSurvivorPc` | same drain | per-channel disposition |

**Round 2 corrected row 3's citation** — `runtime_heap.nim:843-858` contains no
`Path(` construction and no `uncertain: false`; it is the deref-drain comment.
**Round 2 added the last four rows**: `trySolve` asserts these pools into every
subsequent check, each carries only a local definitional-soundness comment, and
the idiom is named and copied (`runtime.nim:3017`) so the list grows silently.
The audited set must be pinned against the actual drain list, or this table is
stale the moment someone adds a pool.

Slice S1 pins "**any** channel ⇒ no summary cache" — sound, less reuse. A
channel-aware `CallCacheEntry` is a later optimisation, out of scope here.
**Producer:** these admission rules are S7 (§5), not "somewhere in S1" — round
1 left them assigned to no slice at all.

### §2.5 The two blanket vetoes — delete both; make reachability representable

`capForcedUnknown` and `closureForcedUnknown` (§1.3) veto the winner scan
before it runs, on any `sevError` anywhere. The code's own rationale for the
blanket is explicit (`runtime.nim:13492-13495`):

> The walker's missing-callee arm already sets `w.sawUnknown` when the capped
> call is reached, but we force it here so a cap discovered on a NON-walked
> path (the over-cap callee is parsed but, e.g., guarded behind an unreachable
> branch) still cannot yield an unsound sat/unsat.

**A construct on a never-walked path contributed nothing to any verdict.**
Forcing `sxUnknown` for it does not protect soundness in the unreachable case;
it insures against the possibility that the reach-taint mechanism has a gap.
The blanket is a backstop for a *coverage* defect, wearing the costume of a
soundness rule — and it is the same shape as the Invariant-7 backstop, which
this codebase already knows how to express honestly.

So the right design is neither "trust the reach mechanism and fold the blanket
in" nor "keep the blanket". Both argue about how much to trust a backstop. The
defect is that **the representation cannot answer the only question that
matters: was this decline site reached?** Make it answerable:

1. **Every site-anchored decline mints a marker node.** Today the two classes
   are split by accident of history: Class-A sites record a `sevError` in
   `prog.parseErrors` (→ caught by the blanket), Class-B bare `mkUnsupported`
   sites mint a dummy node and rely on the walker's `isUnsupported` arm to
   taint the reaching path (`runtime.nim:13502-13505`). That is two mechanisms
   for one thing. Unify: a site-anchored decline mints the marker **and**
   records the error. Reach-taint then decides the verdict — exactly the
   per-path scoping this RFC exists to provide — and the `parseErrors` entry
   becomes purely diagnostic. (Note the dependency: §2.2 requires
   `mkUnsupported` to carry a kind, and a marker that carries no kind cannot
   feed `classOf`. S1b lands the kind; this slice consumes it.)
2. **Signature-scoped declines stay run-wide, via the class table, not a
   veto.** `feUnsupportedParamType`/`feUnsupportedWitnessType` and their kin
   have no site to attach to because the unmodellable thing *is* the
   signature. They classify `dcNoAnswer`, which forces `sxUnknown` in both
   directions by construction. No separate switch.
3. **Unregistered-callee declines are anchored by the callee key.** *(Round 2
   added this third class; without it the invariant below is not total.)*
   `geInstantiationCapped` (`dsl_parser.nim:9290`), unresolvable-`getImpl`
   `feUnsupportedOp` (`:9219`), `geDistinctBarrier` (`:9247`) and
   `geConceptViolation` (`:9390`) are `sevError` with **no marker node and no
   signature scope**: the callee is never registered, so reach detection is the
   walker's missing-callee arm firing on the `mkCall` key. This is precisely
   the "cap behind an unreachable branch" case the blanket's own comment
   describes. Under a two-class invariant they would all land in bucket 4 and
   be stamped `⊤` on **every** run — louder than the blanket and no better
   scoped. The `sevError` must therefore carry the callee key so the verdict
   can associate reach-taint.
4. **What still cannot be placed is a walker-completeness defect, and says
   so.** A `sevError` carrying none of the three anchors means the engine
   cannot tell whether it was reached. That is a defect in the mechanism, not a
   property of the SUT. It stamps `⊤` and a `weInternalWalkerFault`-class
   diagnostic, exactly as the Invariant-7 backstop does today
   (`runtime.nim:13577-13589`) — conservative in the verdict, loud in the
   diagnostics, and *visible* rather than silently absorbed into every run's
   answer.

**Where the scope lives.** Round 1 specified the invariant without specifying
its representation, so the totality pin §6 demands was unwritable —
`SymexErrorInfo` is `(kind, severity, msg)` (`types.nim:1786-1792`) and carries
nothing that can name a marker or a callee. **Decision: add a `scope` field to
`SymexErrorInfo`**:

```nim
DeclineScope* = object
  case kind*: DeclineScopeKind
  of dskSiteAnchored:   markerId*: int
  of dskSignature:      discard        ## the signature itself is unmodellable
  of dskCalleeKey:      calleeKey*: string
  of dskUnplaced:       discard        ## bucket 4 — a walker-completeness defect
```

Round 1's "no fourth column on `SymexErrorInfo`" ruling was about the
**channel**, which stays derived from `kind`. A *scope* is genuinely new
information that no existing field carries, and putting it on the record makes
the invariant a total function of the record — checkable by construction rather
than by a join against a side table. The alternative (a side
`prog.declineSites: Table[errorIndex, markerId]`) is index-coupled and is
rejected in §9.8.

The invariant that keeps this honest is structural and pinnable: **every
`sevError` carries a `DeclineScope` other than `dskUnplaced`.** That is a
totality pin of the same kind as `classOf`'s exhaustive `case` — bucket 4 is a
measurable, shrinking defect class instead of an invisible policy knob. Two
kinds were expected to need reclassification rather than anchoring:
`feTransparentResultUsed` (`dsl_parser.nim:4324`) and `feTransparentArgNotInert`
(`:8486`) are diagnostic *companions* to a walk-time mechanism that already
taints via `feOpaqueCallUnmodelled`. **Resolved (§13.3, Corey 2026-09-26):
neither `sevWarning` nor a companion scope — they are not declines at all.**
They left `SymexErrorKind`'s live set (tombstoned, never emitted) for a
separate, verdict-neutral annotation-violation channel, so the invariant is
total without them and no scope kind exists for two members.

**As landed (S8, walker 148).** Deviations from and additions to the sketch
above, each forced by making the totality pin *real* rather than approximate:

- **A fifth scope kind, `dskWalkSite`.** The sketch scoped only the parse-time
  records the vetoes read. The run coordinate (`taintsRun`) also admits every
  record the *walker* makes — `degrade`, `lowerDegrade`, `closureDegrade`,
  `allocDegrade`, the extraction sink, and a `runSymex` boundary abort raised
  mid-walk. Such a record exists only because a path reached its site, so its
  reach is the record itself; it needs no join. Left unscoped it would have
  been bucket 4 on every run. The two walk arms that reach a *parse* anchor
  record that anchor instead (`isUnsupported`/`isUnsafeCast` →
  `dskSiteAnchored(marker)`, the missing-callee arm → `dskCalleeKey(key)`), so
  a reached parse decline carries two records under one anchor and an
  unreached one carries only the parse record — the join S9 reads.
- **Signature scope is the param-entry boundary.** A carrier raised by
  `raiseParamAllocIssue` (before any walk state exists) is recorded
  `dskSignature` at the `runSymex` boundary; every other boundary abort is
  `dskWalkSite`.
- **One funnel per record.** `ctx.parseErrors` is written only by
  `declineAtSite` (Class A: record + `isUnsupported` marker in one act),
  `declineUnsafeCast` (the `isUnsafeCast` sibling) and `declineCallee` (record
  + never-registered key); Class B mints its marker through `declineMarker`
  and records nothing at parse time (a parse record would trip the retained
  veto — a verdict change S8 may not make). Grep-pinned.
- **`isUnsafeCast` now records its reach.** The halt previously relied on the
  parse record alone; that says the cast *exists*, not that a path reached it.
- **`geConceptViolation` is decided before registration.** It ran inside
  `parseCalleeImpl`, i.e. after the callee was already being registered — the
  "never registered" premise of point 3 was false for it. The check is
  hoisted into `ensureProcRegistered` (`conceptViolationMsg`), so the key is
  genuinely never registered and the missing-callee arm is its reach.
- **A placement check, not a trust.** `parseProc` scans the *emitted* program
  (`placeDeclineScopes`) for every marker literal and never-registered key; a
  parse record whose anchor did not survive into the IR the walker walks is
  rescoped `dskUnplaced` — so a dropped marker is caught, not assumed away.
- **Bucket 4 today: empty for every run, with one construction `dskUnplaced` by
  design** — the Invariant-7 backstop, which fires only when nothing at all was
  recorded (there is no site to name). It is enumerated by name in the pin.

**`closureForcedUnknown` needs more than a propagation fix — round 2
correction.** Round 1 argued the closure veto is redundant "once the descent's
taint joins the calling path". Verified: **most `closureCallErrors` emitters
are not descents.**

- `lowerHofCall`'s filter/map/fold declines (`runtime.nim:12505-12586`) return
  a **fresh unconstrained value** (`allocateSym(…, "__hofFilterUnsupported"` /
  `"__hofMapUnsupported"` / `"__hofFoldOpaque"`) into expression position, and
  write only `currentClosureCallErrors` + a ptr-cast `sawUnknown`. They do
  **not** set `loweringDidDegrade`, so `drainPendingLowerEffects` never taints
  the consuming path.
- `ceInlineBudgetExceeded` (`runtime.nim:11683-11691`) does `w.sawUnknown =
  true; return funcApp` — same shape, no path taint.
- The closure zero-default failure (`runtime.nim:11815-11823`) likewise.

Delete the veto without converting these, and a witness flowing through
`__hofFilterUnsupported` is reported `sxSat` on a clean path with no replay
gate — the S1 failure class, reintroduced by the slice that was supposed to be
a simplification. **Precondition:** enumerate every
`closureCallErrors`/`currentClosureCallErrors` emitter and route each
value-substituting one through `w.degrade` + path taint (or the lowering sink).
That is slice S7, and veto deletion (S9) is gated on it.

Net effect: three parallel unknown-forcing mechanisms (`sawUnknown`,
`capForcedUnknown`, `closureForcedUnknown`) collapse into **one lattice plus
one structural invariant**. This is a strict simplification of the verdict
rule, not an addition to it — but it is reached in three slices, not one.

### §2.6 The raise-routing recovery — *corrected*

`routeRaise` (`runtime.nim:11380-11384`) kills any tainted path
unconditionally and sets `sawUnknown`, **including for handler-caught
raises**, with the comment "bailed-call retSyms are unconstrained".

Round 1 described the recovered case as an `scIncomplete`-only path. **That set
is empty by construction.** The `pathTaint` function of §2.2 only ever yields
`{}`, `{scSpurious}` or `⊤`, and the set is closed under the union join
(`runtime.nim:11083`) — a path whose taint is `{scIncomplete}` alone cannot
exist. Round 1's DoD pin for this case was therefore unsatisfiable.

The real recovery is the **`scSpurious`-tainted raise**, and it is the same
shape as everything else in §2.3: `routeRaise` must stop killing tainted paths,
route the raise, and let a resulting `sxRaised` enter the candidate pool to be
replay-gated. A `dcOmitted`-only path (path taint `{}`) is already clean and
needs no rule. This aligns §2.6 with §2.3 and makes the DoD pin writable
(§6.2).

## §3 — Classification

### §3.1 The rule

Classify by **what the site substitutes**, never by the mechanism's name:

| substitution | class | examples |
|---|---|---|
| fresh unconstrained symbol | `dcFreshSymbol` | `allocDegrade` arms, R1 placeholder funnel, `degradeStrArm`, `mkUnsupported` in a position that yields a free symbol, the HOF declines of §2.5 |
| forced concrete value / stale env | `dcSubstituted` | `defaultZero`, typed-zero dummy, dropped-statement stale `env`, `maxCallDepth` bail, `feOpaqueCallUnmodelled` |
| fabricated continuation | `dcFabricated` | k-unroll exhausted survivor |
| pure path drop / halt / prune | `dcOmitted` | heap-depth halt, `maxFrontierSize` prune, unsafe-cast halt |
| no answer exists | `dcNoAnswer` | Z3 `unknown` result *and* `ekZ3*` exceptions, `weInternalWalkerFault`, parse-time whole-run declines, signature-scoped declines |

Round-2 corrections to round 1's table:

- **"break-budget bails" is struck from the drop row.** It was a three-way
  conflation (see §3.2).
- **`feOpaqueCallUnmodelled` moves from `dcFreshSymbol` to `dcSubstituted`.**
  `runtime.nim:10682-10698` havocs the return **and drops the callee's
  mutations** — a stale env, not a free symbol. §8.2 previously asserted the
  `dcFreshSymbol` classification; the two give different `sxUnsat` outcomes for
  any SUT that calls `echo`.
- **A solver-undef row is required.** `trySolve`'s `zsUnknown` result
  (§2.2's table) is reachable via timeout and via the deterministic
  `queryRLimit` truncation (`:7458`, `:14354`), and mints no kind today. Mint
  one (`beSolverUndef`, tail-appended), class `dcNoAnswer`. It is also the
  natural carrier for the rlimit provenance §8.2 owes 0011/0008.
- **`eeUnknownExnType` is a behaviour substitution recorded at `sevWarning`**
  (`runtime.nim:11385-11396`): an unknown raised type is matched only against a
  bare `except:`, never a named handler, so where reality's subtype match would
  catch, the walker fabricates an escaped raise *and* drops the handler
  continuation. That is `dcSubstituted` by this table's own rule. Either it
  taints (and the §2.2 severity rule carves an exception for it) or the
  reachability argument for leaving it inert is written down. §6 requires one
  of the two.

`dcNoAnswer` deserves a note: a Z3 resource-out or a walker bug is not an
approximation in either direction — no enlarged or shrunk program exists. It is
nonetheless *represented* as `⊤` on both coordinates, because that forces
`sxUnknown` in both directions by construction, which is exactly the required
behaviour. A separate "fatal" lattice element would be a distinct encoding of
an identical observable; it is rejected in §9.4. What must **not** happen is
laundering a walker fault into a sound verdict by giving it a single channel.

### §3.2 Kind-splitting policy

`classOf` is well-defined only if every site sharing a kind shares a
substitution class. Where the §5 audit finds a kind whose sites diverge,
**split the enum member**, tail-appended for ordinal stability (the enum's own
established convention, `types.nim:1287-1298`). Do **not** add a per-site class
parameter: that re-smears classification across call sites and forfeits the
single-table property. Splitting also improves diagnostics.

**Mandatory splits identified in round 2** (round 1 named only
`feUnsupportedOp`, as "the known candidate"):

- **`beBudgetExhausted` — a ≥3-way split, and the most dangerous row in the
  RFC.** One kind, three classes, merged deliberately
  (`runtime.nim:10759-10769`: "this call-inlining depth cap is a sibling of the
  SAME budget family, so it reuses the kind"): the `maxLoopUnwind` exhaustion
  (`:9550`) is `dcFabricated`; the `maxCallDepth` bail (`:10771-10786`)
  continues with a **fresh havoc `retSym` and the callee's var-param/heap
  effects dropped** — `dcSubstituted`; the `maxFrontierSize` prune (`:9317`) is
  a genuine `dcOmitted`. Six emission sites total (`:9277`, `:9317`, `:9551`,
  `:10246`, `:10284`, `:10771`). Classifying the merged kind `dcOmitted` — which
  is what round 1's §3.1 row implied — gives it `pathTaint = {}` and therefore
  **removes** the taint the `maxCallDepth` site sets today, turning a witness
  through the havoc retSym into an unreplayed `sxSat`.
- **`feUnsupportedOp` — 12 emission sites in `runtime.nim` alone**, spanning at
  least three classes (free retSym, stale-env statement drop, no-zero-default
  fallthrough). Budget for several tail-appended kinds, not one.

**Split discipline.** A split appends **one sibling for the minority funnel**
and keeps the original member for the majority funnel — never retire-and-append-two.
The enum already carries six "retained for ordinal stability, never emitted"
tombstones (`feConvDomainExcluded`, `seByteIndexUnsupported`, `seParseIntPreE`,
`geUnresolvedGeneric`, `ceUnsupportedCapture`, `geVtableDispatch`); each
undisciplined split adds another at permanent cost to every consumer `case`.

**Standing rule, uncheckable by any mechanism:** *reusing an existing kind at a
new site asserts that your site shares that kind's substitution class.* Say it
in the enum's doc comment, because `classOf`'s exhaustiveness cannot catch it.

### §3.3 The residual boundary-abort class

The whole-walk aborts of §1.2 (`runtime.nim:64-213`) can carry no path-scoped
channel until they are migrated in-band, and the §1.5 toolchain constraint
forbids catching them lower. They classify `dcNoAnswer` — always `sxUnknown`,
both channels — and their in-band migration is explicitly **out of scope**
(§11). **Producer: S1** — under the conservative-`⊤` default (§5) these kinds
need no special handling, because the default already gives them `⊤`; the
obligation is only that S6's totality sweep must not "promote" them out of it.
Round 1 stated the classification in the passive voice with no producer at all.

### §3.4 Deliverable

The classification table is a **deliverable of this RFC, not an open
question** — one row per live `SymexErrorKind` (41 members at HEAD, ~6 retired
or never-emitted, plus the kinds minted in S1b), each row naming its class and
citing its emitting funnel. The table **is** `classOf`; there is no separate
document to go stale.

The funnels that concentrate the work: `allocDegrade` (`runtime.nim:1295`),
`degradeStrArm` (`:4904`), the R1 placeholder funnel, the closure/HOF funnel
(§2.5), and the Class-A/Class-B split across the `mkUnsupported` sites in
`dsl_parser.nim`. **The audit checklist is not "the 52 `sawUnknown` write
sites"** — round 1's checklist would structurally miss every
behaviour-substituting site that records no taint at all (§2.2's table,
`eeUnknownExnType`). The checklist is: the 52 write sites, **plus** the
enumerated kindless sites of §2.2, **plus** the `sevWarning`
behaviour-substituting sites of §3.1.

## §4 — Verification strategy

### §4.1 Taint monotonicity — scoped

The draft's property was: *adding an unreachable tainted branch to a green SUT
must never change its verdict*, mechanically generable by grafting a poisoned
disjoint arm onto any existing passing test.

**As stated it contradicts §0.1 and would go red against this RFC's own
design.** The walker forks both arms with no feasibility check
(`runtime.nim:9472-9474`), so a grafted arm *is* walked and *does* taint;
graft a `dcOmitted` arm onto a green `sxUnsat` test and the verdict correctly
becomes `sxUnknown`. It is also weaker than advertised where it does hold: it
exercises taint *scoping* only — swap every channel label and it still passes.

The property this RFC can actually carry, in two families:

1. **Witness monotonicity.** Grafting a disjoint tainted arm onto a SUT with a
   clean witness path must not change an `sxSat`/`sxRaised` verdict. This is
   the honest form of the draft's property and it does encode the path-scoping
   half. **It is also the pin that catches the `shouldStop` regression of
   §2.3** when the tainted arm is discovered *before* the clean witness path —
   make that ordering explicit in the battery.
2. **Classification pins.** A `dcSubstituted` site on the witness path must
   never yield `sxSat` without replay; an over-taint-only run that proves the
   target unreachable must yield `sxUnsat`. These are what test the *labels*,
   which family 1 cannot.

"Graft onto any existing passing test" is not mechanizable — SUTs are procs
defined inside 496 individual test files, not an importable registry. The
buildable form is a test-support macro (`withPoisonedArm`) over a curated SUT
battery in one new file (slice S3, §5).

### §4.2 Witness replay — the execution contract

Any `sxSat`/`sxRaised` this RFC newly permits on a `scSpurious`-tainted path
must have its witness replayed against the real function. Round 1 established
the substrate; round 2 establishes the contract, because replay is the one
mechanism here that **executes user code inside the verdict**.

**Substrate (round 1, verified).** "B7's differential oracle" is not in this
repository — it is chapulin's `t_symex_decode.nim`, and per the standing
consumers-report-don't-drive rule it cannot be this RFC's oracle or its
definition of done. The in-repo substrate exists: `symexTarget` records hits
into a threadvar capture (`markers.nim:63-74`) and `assertCoveredBy`
(`symex.nim:1418`, codegen at `:1560-1643`) already proves a concrete call
reaches a label.

**Interface.** A `bool` conflates *refuted* with *could not run*, which are
different facts with different downstream reporting, and a `label` parameter
cannot serve the raise-flavoured targets §2.3 puts in scope (`SymexTarget` has
six kinds, `types.nim:1203-1216`):

```nim
type ReplayOutcome* = enum
  roConfirmed     ## the real fn reached the target on this witness
  roRefuted       ## the real fn ran to completion; target not reached —
                  ## the witness is proven spurious (a confirmed model gap:
                  ## surface it as its own classified diagnostic kind)
  roInconclusive  ## not faithfully executable, or replay declined —
                  ## the candidate stays sxUnknown

replayWitness(fn, witness, target: SymexTarget): ReplayOutcome
```

**Eligibility gate.** Replay is attempted only for candidates whose path taint
derives entirely from `dcFreshSymbol` sites. A `dcFabricated` candidate is
`roInconclusive` by construction — and that costs nothing, because §0.3 already
argues the k-unroll SAT payoff is empty. This is the gate that bounds the
non-termination hazard below, and `DegradeClass` makes it one line rather than
a site list.

**Hazards, each of which must be addressed in the slice, not discovered in it:**

- **Non-termination.** A fabricated-continuation witness is by §0.3's own
  analysis an input on which the real program may still be looping. The
  eligibility gate excludes exactly that class; what remains is the ordinary
  risk any PBT library takes when it calls a user proc — which nelli already
  takes in `forAll`/`fuzz`. State it; do not build a watchdog (Invariant 3 is
  preserved by the gate, and an in-process watchdog is not safely buildable
  under §1.5's constraint).
- **Side effects.** A path is `scSpurious`-tainted precisely when it ran
  through an unmodelled call — often an *effectful* one (the #137
  `echo`/`writeFile` shape). Replay performs those effects for real, at verdict
  time, in the user's process.
- **Contract change.** `symexFind` (`symex.nim:1220ff`) has never executed
  `fn`. After this RFC it does, on solver-chosen inputs. This is
  consumer-visible and belongs in §8.1 and the migration note — it is arguably
  the most surprising thing in the whole RFC.
- **Defect-flavoured targets.** `stkNilAccess` and friends expect a Defect; a
  raw-pointer nil deref is a SIGSEGV, not catchable. State replay scope per
  target kind, and default to `roInconclusive` outside it.
- **Un-replayable witnesses.** Witness rendering has a restricted fragment
  (`emitTyAndReader`, `symex.nim:575-649`: closures → nil placeholder,
  `__unsupported:` → dummy `int`), and a spurious path's model includes havoc
  symbols the witness does not pin. Both are `roInconclusive` → `sxUnknown`,
  permanently. Say so.
- **Capture reentrancy.** `symexCaptureBegin` *clears* the hit-set
  (`markers.nim:50-54`), so engine-internal replay during a user's active
  `assertCoveredBy` capture clobbers it. The capture context must become
  stackable — that is part of the substrate slice.
- **Naming collision.** `sfReplayMiss` already exists on `SymexFindingStatus`
  (`engine/types.nim:29-35`) as replay vocabulary from Phase 14 B5. Reuse it or
  distinguish it explicitly.
- **Tainted-solve cost (found in S1c).** Rule 3 needs a model, so S1c solves
  every target-hit path, tainted or not -- queries no engine before it ever
  issued. A tainted path's pc carries whatever a degraded lowering left behind,
  and the N36 `iekStrInOptionRegion` BV-bound decline's residue spins Z3's
  `check` without end under the default `queryRLimit = 0`: an unbounded solve
  there would be a NEW non-termination, not a pre-existing one. S1c bounds it
  (`taintedSolveRLimit`: the caller's explicit `queryRLimit`, else
  `defaultConcreteBranchRLimit` = 20M) and the bound's `zsUnknown` is the
  honest `beSolverUndef`. The bound is finite but not cheap: on
  `tsymex_rfc0005_s1c_verdict`'s N36 shape six tainted queries each run to the
  full 20M, which is ~230 s of wall time under default settings (measured at
  S10 with `-d:symexQueryStats`), well past `dt-bounded.sh`'s 180 s default
  (the sweep's 900 s covers it). A caller's explicit `queryRLimit` shrinks it
  (1M: ~12 s, same verdict). Replay adds nothing here -- the candidates it
  receives are already solved -- but a tighter default tainted budget is a
  live tuning question, not a closed one.

**Plumbing — replay cannot live in `runSymex`.** Invoking the SUT requires
splatting a typed witness into its parameter list with `var`-param wrapping;
that is macro codegen (the existing template is `assertCoveredBy`'s splat
block, `symex.nim:1481-1490`, `:1555-1643`). `runSymex` is runtime code and has
no `fn`. Therefore **replay runs in macro-generated code after `runSymex`
returns**, and `RawResult` must carry candidacy across that boundary in a form
that cannot be mistaken for a plain `sxSat` — a distinct raw status
(`sxSatCandidate`) or a field every `SymexResult` construction must explicitly
discharge, so an entry macro that forgets to replay **fails to compile** rather
than mis-reporting. There are exactly two `runSymex` callers — `symexFind`
(`symex.nim:1272`) and the `symexFindAllWitnesses` codegen (`:2061-2063`, also
reached by `symexForAll` via `toFindingStatus`, `:408`) — and **both** must
discharge it. A `symexFind`-only implementation leaves `symexForAll` either
unsound or dark, and round 1's DoD wording ("replay confirmed in the reporting
path", singular) did not force the second.

**As landed (S10).** Candidacy crosses the boundary as `SatCandidate`
(`smt/runtime.nim`), a type with no `witness`/`raisedWitness` branch whose
model is a PRIVATE field. It is readable only by `symex.nim`'s private
`candidateInput`, and a verdict can be made from it only by the private
`settleCandidate`, and only on `roConfirmed`. Both are reached solely through
`bindSym` in `emitRunSymexReplayed`, which is the ONE `runSymex` call site
behind both entry macros. An entry macro that skipped the settle could not
mis-report: it would see `sxUnknown` and a pool it cannot render. The
compile-time and structural pins live in `tsymex_rfc0005_s10_replay_verdict`.
Each hazard above is contained as follows:

- **Non-termination.** The eligibility gate (`replayEligible`: path taint
  `<=` `{scSpurious}`) is unchanged, and there is no watchdog.
- **Side effects.** These are run for real, once per replayed candidate, in
  discovery order, stopping at the first confirmation. An ineligible or clean
  result runs nothing, and the tests pin that with an effect counter.
- **Defects.** Under `--panics:on` every target is declined, not just Defect
  targets, because a candidate's real run may hit a Defect the model never
  forked. `tNilAccess` is always declined.
- **Un-replayable witnesses.** A `feExtractionFailed` model is lossy: it
  confirms on a hit and never refutes.
- **Naming.** A refutation is the new `feReplayRefuted` hint on a `sxUnknown`
  result, not `sfReplayMiss`, which stays Phase 14 B5's per-seed diagnostic.
- **Raises (§2.6).** `routeRaise`'s spurious raises reach the same pool, and
  an `sxRaised` claim replays against `tRaisedExn(<its type>)`.
- **parseInt.** The raise predicate is split so that Nim's `+`/`_` syntax
  (which `str.to_int` rejects) raises only on a `seParseIntLaxSyntax`
  (`dcFreshSymbol`) candidate. Before this, it was a clean `sxRaised` that
  could be false (`"+5"`).
- **Cache.** Replay precedes persist, structurally: the cache writers run on
  the settled result.
- **Link/load contract (found by S10's sweep; decided: stated contract with
  an opt-out).** Replay needs a real call to `fn` in the generated code. So
  with replay on, `fn` and everything it calls are compiled, LINKED and LOADED
  into the calling binary, whether or not any candidate is ever replayed.
  Before S10, `fn` was only read at macro time.
  - An `importc` with no definition now fails the link. This was
    `tsymex_phase15_g5_distinct_borrow`'s deliberately unlinkable stub.
  - A `dynlib` the host lacks now fails at start-up. `std/re` loads PCRE1:
    `libpcre.so.1` on Linux, `pcre64.dll` on x64 Windows.

  No runtime gate can contain either failure, because both happen before any
  replay decision runs.

  The opt-out is `SymexSettings.replay = false`. It is static at every entry
  macro, so no reference to `fn` is emitted and every candidate stays
  `sxUnknown` as before S10. It enters the cache key as `;rp=off`, and only
  when off, so default keys are unchanged. g5 opts out. The regex suites keep
  full coverage instead:
  - the dev image builds PCRE 8.45 from hash-pinned source, since Tumbleweed
    ships only PCRE2;
  - `symex-mingw`'s corpus job puts the hash-pinned `pcre64.dll` from Nim's
    official `dlls.zip` on PATH.

  The S11 migration note leads with both contract changes: `fn` is EXECUTED,
  and `fn` must LINK and LOAD.

Replay is therefore a **verdict mechanism**, not a test oracle, and it is the
single largest piece of genuinely new machinery in the RFC.

### §4.3 The `sxUnknown` pin audit

272 `== sxUnknown` assertions across 110 test files pin today's conflated
verdict. Every over-taint-only run among them that proves UNSAT flips to
`sxUnsat` under §2.3. Candidates include the honest-decline pins at
`tests/tsymex_r6_n21_pairloop_member.nim:171,213,242` and the SND-3 family at
`tests/tsymex_snd3_loopdegrade.nim:109-127`. **Each flip must be individually
re-justified** in the slice that causes it — some of those pins exist
specifically to assert that the engine declines honestly, and a flip there is
either the payoff or a soundness bug, with no way to tell them apart in
aggregate.

**Round 2 made this tractable in two ways.** Round 1 scheduled the whole audit
as one slice (S6) positioned *before* any verdict-changing slice — where
**zero pins can flip**, making the audit an empirical no-op and the
"individually justified" requirement unsatisfiable in the same breath.

1. **The audit attaches to each verdict-changing slice**, covering only the
   pins that slice flips. Under §5's per-funnel sequencing, that is a handful
   of pins per slice, and a misclassification is caught by its own slice's
   flipped pins instead of by one big-bang landing.
2. **Justification is a checked line, not prose.** Export a helper
   (`SymexResult.errors` is already public, `types.nim:1906`):

   ```nim
   checkUnsatOverTaintOnly(r)
     ## asserts r.status == sxUnsat AND every drained error maps through
     ## classOf() to a class with scIncomplete notin runTaint(class)
   ```

   The flip list itself is generated by `sweep-diff` against the sha-pinned
   baseline, so the audit is *find the diff, rewrite each line through the
   helper, justify anything the helper cannot express*.

The converse risk raised at round-1 kick-off does **not** exist: no k-unrolled
run reports `sxUnsat` today (any degrade sets `sawUnknown`, which already voids
it), so the 283 `== sxUnsat` assertions across 130 files are taint-free runs by
construction and cannot regress. The change is a relaxation on both sides.

### §4.4 Process gates

- Every slice lands on an **`rfc-0005-*` branch** — `rfc-*` naming is what
  triggers the three Windows legs (`fuzzer-msvc.yaml:66`,
  `fuzzer-mingw.yaml:43`, `symex-mingw.yaml:118`).
- `tests/tsymex_r6_b7r2_pathscope.nim` — the opOack-faithful path-scoped-taint
  composite, i.e. the single most relevant pin suite for this work — is one of
  the six Linux/podman hangers skipped by name (`scripts/sweep.sh:91-96`).
  **The exact area under change is verifiable only on Windows CI**, and the SAT
  slice (S10) has *no local gate at all*. Local gating elsewhere is
  `sweep-diff` against a sha-pinned baseline over the remaining suites.
- **Price the Windows gate.** `symex-mingw` runs the derived corpus (parsed
  from `nelli.nimble`'s test task) in 60-min-capped shards plus 90-min-capped
  per-suite scan-tail jobs: roughly **1–1.5h wall per push**, and the plan has
  13 slices. Windows CI is a required gate on every **semantics-bearing** slice;
  batch the non-semantic ones (S1's carrier pieces; the classification slices
  under their shared bump) into one gated push each.
- New test files must be registered in `nelli.nimble`'s `test` task or they
  land in `.drift` and run in **no** CI leg. That applies to every new file this
  RFC creates.
- Existing suites to extend rather than duplicate:
  `tests/tsymex_163rev_degrade_classification.nim`,
  `tests/tsymex_r6_degrade_pairing_audit.nim`,
  `tests/tsymex_r6_n40_alloc_totality.nim`.

## §5 — Slice plan

Each slice is a vertical RED-GREEN-REFACTOR unit with a named failing test.
Blast radius is listed because a single implementing agent inherits it as
context; anything spanning more than ~2–3 modules is a round, not a slice.
Remember the path convention: the five `runtime_*.nim` files are **`include`d
into `runtime.nim`** — "the runtime unit" below means all six, ~17.6k lines.

**The two sequencing decisions round 2 changed, and why.**

1. **`classOf` is total from S1 with a conservative `⊤` default.** Every kind
   is mapped on day one; unaudited kinds map to `dcNoAnswer`. All-`⊤`
   reproduces today's behaviour bit-for-bit (any taint blocks both verdicts),
   so the verdict rule can land *early* as a behaviour-preserving refactor and
   each classification slice then flips only its own funnel's pins. Round 1
   built a lattice, a replay engine and a harness across eight slices during
   which **no observable verdict changed**, then turned everything on at once
   at S7 — which is how an RFC ships green-but-inert, and which made its own
   top risk (a single under-as-over misclassification) undetectable until the
   big bang.
2. **The `isTargetLabel` tainted-path solve moves into the UNSAT slice.** Round
   1 put the verdict rule in S7 and the solve in S8. That boundary mints a
   false `sxUnsat` (§0.1, §2.3): a tainted path that reaches the target and is
   never solved is an omission, so rule 5 cannot be shipped without it.

| # | slice | blast radius | RED |
|---|---|---|---|
| **S0** | **Exhibit the discarded capability.** A SUT run through `symexFind` — the real entry point — that is over-taint-only and proves its target unreachable, pinned **green** today as `sxUnknown` **plus its expected drained error-kind set** (`SymexResult.errors` is already public, so the over-taint-only status is *asserted*, not assumed). Add the §2.5 veto companion: a clean-path witness plus a `sevError` decline behind an unreachable branch, pinned `sxUnknown` today. Flipping these is S6's and S9's RED. | 1 new test file + `nelli.nimble` | characterization pin (green) |
| **S0b** | **Measure the payoff before building it.** Throwaway `-d:`-gated dump of drained error-kind sets at the verdict site (~5-line diff, reverted), one podman sweep over the 110 pin files, classify observed kind-sets against §3.1. Output: the count of over-taint-only `sxUnknown` runs. **Gate: if the count is near zero, §13.1 re-opens scope before any product code is written.** | throwaway instrumentation; no product code | n/a (spike) |
| S1 | **Lattice + carrier.** `SoundnessChannel`/`Taint`/`DegradeClass`; `classOf` **total with `dcNoAnswer` default**; `pathTaint`/`runTaint`/`channels`; `Path.uncertain` → `Path.taint` (79 refs); `w.runTaint` **derived at drain** from the error seqs; the `degrade()` funnel + `Degrade` token + `taintInPlace`; `forkPathTainted` takes a `Degrade`; `loweringDidDegrade` → `loweringPendingTaint` + its leak pin; `RawResult.pathTaint`; the `.taint`/`.runTaint` writer grep-pin. No verdict change. | runtime unit + `types.nim` | the H1-style compile-time hook (`runtime.nim:686-699` — `Path` is private, tests cannot name it directly) |
| S1b | **Mint the missing kinds** (§2.2's table): `mkUnsupported(kind, reason)` across ~40 `dsl_parser.nim`/`canonicalize.nim` sites; new kinds for cycle-break, handler re-raise, diverged body, break/continue, `beSolverUndef`; over-cap missing-callee carries its kind at the site. Land the **correspondence pin**: `runTaint` equals the union over drained errors, mismatch → `weInternalWalkerFault`. Still all-`⊤`, so still no verdict change. | `dsl_parser.nim`, `canonicalize.nim`, runtime unit, `types.nim` | correspondence pin on a SUT whose degrade records no error today |
| S1c | **The verdict rule** (§2.3): ordered procedure, `w.candidates` pool, `shouldStop` excludes candidates, `isTargetLabel` solves `scSpurious`-tainted paths, unsolved-skip contributes `scIncomplete`, `routeRaise` stops killing tainted paths. Behaviour-preserving under all-`⊤`. **The consumer now exists — the RFC runs end-to-end from slice 5.** | runtime unit | S0's exhibit still `sxUnknown`, *and* a witness-monotonicity pin with the tainted arm discovered first |
| S2 | **Replay substrate** (§4.2): `ReplayOutcome`, target-shaped `replayWitness` macro, eligibility gate, stackable capture context. Not yet wired to the verdict. | `markers.nim`, `symex.nim`, 1 test file | direct replay test: confirmed / refuted / inconclusive |
| S3 | **Taint-monotonicity harness**: `withPoisonedArm` + curated battery (§4.1). | 1 new test file + support macro | the battery |
| **S4** | **Classify the `allocDegrade` funnel** (`runtime.nim:1295`) — **and this is where S0's exhibit flips**, because S0's SUT is chosen to route through this funnel. First observable payoff: slice 6 of 13. Carries its own flip audit (§4.3). | runtime unit | S0 exhibit flips `sxUnknown` → `sxUnsat` |
| S5 | Classify `degradeStrArm` + the R1 placeholder funnel; own flip audit. | runtime unit | that funnel's flipped pins |
| S6 | Classify heap/halt sites + the `beBudgetExhausted` and `feUnsupportedOp` splits (§3.2); own flip audit. | runtime unit, `types.nim` | that funnel's flipped pins |
| S7 | **Cross-path sinks + closure taint** (§2.4, §2.5): admission rules on all seven sinks pinned against the live drain list; closure-descent taint joins the calling path; **every value-substituting closure/HOF decline routed through `w.degrade` + path taint** (the precondition for S9). | runtime unit | a witness through `__hofFilterUnsupported` must not report clean `sxSat` |
| S8 | **Decline-scope representation**: `DeclineScope` on `SymexErrorInfo`; Class-A/Class-B unification so every site-anchored decline mints a marker; callee-key anchoring; the structural totality pin + the bucket-4 count. **Vetoes retained — no verdict change.** | `dsl_parser.nim` (39 `parseErrors.add` sites), `types.nim`, runtime unit, 1 test file | the totality pin, initially red with an enumerated bucket-4 list |
| S9 | **Delete both blanket vetoes.** Verdict-changing; own bump; own flip audit. | runtime unit | S0's veto companion flips to `sxSat` |
| S10 | **SAT relaxation**: replay wired into the verdict across **both** `runSymex` consumers, candidacy made unspellable-as-sat, `routeRaise`'s spurious raises replay-gated (§2.6). Windows-only verifiable. | runtime unit, `types.nim`, `symex.nim` (both entry macros + cache helpers) | DoD §6.2's trio |
| S11 | **Public surface** (§8.1): the `Soundness` object, `gaps()`, `SymexFinding` + render layer, cache value schema, docs. | `types.nim`, `symex.nim`, `engine/types.nim`, `engine/render.nim`, examples | a `forcedBy`-shape assertion through `symexFind` |

**Totality of the totality claim.** The audit sweep round 1 scheduled as "S6"
is gone as a separate slice: under the conservative default, every kind is
already classified, so there is no sweep to do — only per-funnel
reclassification with per-funnel flip audits. What remains of S6's other half
(the Invariant-7 extension) lands in S1b's correspondence pin.

## §6 — Definition of done

Not "the suite passes". The RFC is done when:

1. The **S0 exhibit** — a named in-repo SUT, run through `symexFind`, the real
   entry point — flips from a recorded `sxUnknown` to `sxUnsat` at S4, with
   its over-taint-only status asserted from the public `errors` seq, not
   assumed.
2. **The SAT half's live payoff is pinned, both halves of it** (§0.3):
   - S0's **veto companion** — a clean-path witness plus a `sevError` decline
     behind an unreachable branch — flips `sxUnknown` → `sxSat` at S9, through
     `symexFind`; plus a closure-veto companion.
   - A named SUT whose witness lies on a `dcFreshSymbol`-tainted path is
     reported `sxSat` **with `replay == rsConfirmed` in the reporting path**,
     a companion whose witness is refuted stays `sxUnknown`, and a third pins
     §2.6: a **`scSpurious`-tainted** raise is routed and replay-gated rather
     than killed. *(Round 1's third pin named an `scIncomplete`-only path,
     which §2.6 shows is unconstructible.)*
   - Both pins run through **`symexFind` and `symexForAll`/`symexFindAllWitnesses`** —
     the two `runSymex` consumers (§4.2).
3. Every pin the plan flips is individually justified **in the slice that
   flipped it**, via `checkUnsatOverTaintOnly` where the helper can express it
   (§4.3).
4. The must-NOT-flip guards hold: `tests/tsymex_r6_n20_boundedloop.nim:126,144`
   stay `sxUnknown` (no witness + under-taint voids unsat);
   `tests/tsymex_r6_b7r2_pathscope.nim:381` stays `sxUnknown` (over-decline on
   the witness path).
5. `classOf` is total over `SymexErrorKind`, pinned by a totality test; the
   §2.1 **introduction invariant** ("a `dcFreshSymbol` site's symbol carries no
   constraints at introduction") is pinned for every `dcFreshSymbol` kind; the
   §2.2 **correspondence pin** (`runTaint` = union over drained errors) is
   green; the `.taint`/`.runTaint` writer grep-pin is green; and
   `eeUnknownExnType` is either classified-and-tainting or has its
   leave-inert argument written down (§3.1).
6. Both blanket vetoes deleted, the `DeclineScope` totality pin green, and the
   count of `dskUnplaced` declines (§2.5 bucket 4) **recorded in the slice's
   own test** — the target is zero, and a non-zero count must be an
   enumerated, named list rather than a tolerance. *(S8: the pin covers every
   `sevError` construction, walker records included — see §2.5 "As landed";
   the two `feTransparent*` kinds are not in it because §13.3 moved them off
   the decline lattice, not because they were demoted or companion-scoped.
   Recorded count: 0, in `tests/tsymex_rfc0005_s8_scope.nim`; the Invariant-7
   backstop is the one construction `dskUnplaced` by design, named there.)*
7. §7's version and cache discipline discharged **including the cache value
   schema**; the `docs/migration/<version>.md` entry written (§8.2); Windows CI
   green on all three legs; `sweep-diff` against a sha-pinned baseline shows
   `regressed=0`.

## §7 — Version-pin, cache and process discipline

Walker semantics change here, so per the standing rule each semantics-bearing
slice bumps `symexWalkerVersion` (`canonicalize.nim:187`, `"140"` at HEAD),
updates the **brittle `==` pin** in `tests/tsymex_phase15_CR2_cachekey.nim`
(which has shipped red before for exactly this omission), and adds a `>=` floor
pin in the round's own test file (pattern:
`tests/tsymex_163rev_concolic_diagnostics.nim:517`).

**The semantics-bearing slices are S4, S5, S6, S7, S9 and S10 — six bumps, not
two.** Round 1 scheduled bumps for "S7, S8 and any classification slice", with
one shared bump across S3–S6; under the new sequencing each classification
slice changes observable verdicts, so each needs its own bump and its own CR2
pin update. S9 in particular was previously unscheduled entirely and is
verdict-changing.

**Cache key.** The cross-run verdict cache (`symex.nim:259-331`) persists
`sfUnsat`/`sfUnknown` sentinels keyed on the walker version, so a bump
invalidates it and the taint need not enter the cache key. Pre-bump entries
orphan unread rather than being evicted — harmless, worth one sentence in the
migration note.

**Cache value schema — round 2 addition.** The key is handled; the *value* is
not. The stored verdict sentinel is an **empty `seq[ChoiceNode]`**
(`saveSymexVerdictImpl`, `symex.nim:259-297`), and `loadSymexRaisedImpl`
(`:389-410`) reconstructs `RawResult(status: sxRaised, raisedTypeId)` and
nothing else. So on every cache hit:

- an `sxUnknown` cannot carry `forcedBy != {}`, breaking §8.1's Invariant-7
  extension, and the actionability payoff never reaches the consumer that
  needed it most (the repeat run);
- an `sxSat`/`sxRaised` cannot carry `pathTaint`/`replay`, so a served result
  cannot state whether it was replay-confirmed.

**Decision: widen the sentinel to carry `Soundness`** (§8.1). The walker-version
key already invalidates the format for free, so the schema change costs
nothing, and it keeps cross-run reuse rather than trading it away. Two ordering
rules ride with it: **replay precedes persist** — a tainted `sxSat`/`sxRaised`
is never written to the cache before `roConfirmed` — and a served result carries
its stored `Soundness` unchanged. (The alternative, restricting what may be
cached, is recorded in §9.9.)

Any new `SymexErrorKind` member is tail-appended (`types.nim:1287`). The in-run
summary cache is handled at §2.4.

## §8 — Consumer surface and migration

### §8.1 What consumers see

Do **not** grow `SymexStatusKind` — `sxUnknownOver`/`sxUnknownUnder` would
conflate two axes in one enum and break every `case` for no gain.

**One common field, not three variant-branch fields.** Round 1 proposed
`forcedBy` on the `sxUnknown` branch and `satPathTaint`/`replayVerified` on the
`sxSat` branch. That is internally inconsistent — §2.3 makes `sxRaised` obey
the SAT rules verbatim, and §6.2 pins a replay-gated raise, but round 1 gave
`sxRaised` no taint fields at all, making the pinned case unauditable on the
public surface. It also forces every generic consumer (the verdict cache,
`toFindingStatus` wrappers, logging) to `case`-split merely to *read* the taint.
`SymexResult` (`types.nim:1888-1933`) already keeps cross-status facts in its
**common** section — `errors`, and `heapSnapshot`, which is documented as
"EMPTY for a SUT with no ref/ptr params". Follow that precedent:

```nim
type
  ReplayStatus* = enum
    rsNotNeeded    ## clean path — replay was not required
    rsConfirmed    ## roConfirmed (refuted/inconclusive never ship on a winner)

  Soundness* = object
    pathTaint*: Taint  ## winning path's taint (sxSat/sxRaised); {} otherwise
    runTaint*:  Taint  ## run-global taint; on sxUnknown this is round 1's
                       ## `forcedBy`, with the Invariant-7 extension != {}
    replay*:    ReplayStatus

  # RawResult / SymexResult common section gains:  soundness*: Soundness
```

and the single predicate the whole RFC exists to license:

```nim
func trusted*[T](r: SymexResult[T]): bool =
  case r.status
  of sxSat, sxRaised: scSpurious notin r.soundness.pathTaint or
                      r.soundness.replay == rsConfirmed
  of sxUnsat:         scIncomplete notin r.soundness.runTaint
  of sxUnknown:       false
```

**Actionability is per-cause, not the aggregate.** Round 1 claimed `forcedBy`
tells the caller which lever to pull. It does not, and the reason is structural:
`runTaint` is the **join** over every degrade in the run, so a SUT with one
`echo` and one deep loop reads `⊤` — "model gap" *and* "budget problem" at once
— when the right moves (mark the `echo` transparent, raise `maxLoopUnwind`) are
both recoverable from the classified error list. With 52 degrade sites, `⊤` will
be the *common* value on real SUTs. `soundness.runTaint` is the O(1) **verdict**
input; the actionable surface is the per-cause view, and `DegradeClass` is
exactly the lever taxonomy:

```nim
func gaps*[T](r: SymexResult[T]): seq[tuple[class: DegradeClass, e: SymexErrorInfo]]
  ## dcOmitted      → raise the named budget (maxLoopUnwind / maxCallDepth /
  ##                  heap depth / maxClosureInlineCount) — the caller can fix it
  ## dcFreshSymbol,
  ## dcSubstituted  → a model gap: engine work, or mark the call transparent
  ## dcFabricated   → the bound was hit and the continuation is fiction
  ## dcNoAnswer     → solver resource-out or a walker defect
```

**Known consumers to update** — round 1's list was short by four:
`toFindingStatus` (`symex.nim:408-412`), the `SymexResult` codegen arms
(`symex.nim:1288-1319`, `:1559-1610`), `symexFindAllWitnesses`' verdict arms and
cache path (`:2038-2089`), the seed filter (`:537`), the verdict cache (§7),
**`SymexFinding` (`engine/types.nim:37-70`) and the render layer
(`engine/render.nim:21`, `:135`)** — the Z3-free record that reaches the
terminal report and the ofJson/ofJunit/ofGithubAnnotation renderers, which
round 1 never mentioned and without which the payoff never reaches anyone
reading a report — plus `examples/symex_loops.nim` and
`examples/symex_stdlib_model.nim`, and the `symexOpaque` doc comments
(`symex.nim:1096-1134`) which promise "costs precision (an extra sxUnknown)".

**One caveat on the example.** `examples/symex_loops.nim` records in its own
header (lines 60-63) that it **stopped compiling for a full release cycle with
nobody noticing, because `examples/` is built by neither CI nor `nimble test`**.
Putting the worked "read `gaps()`, pull the right lever" walkthrough there and
nowhere else deposits this RFC's user-facing payoff in dead code. S11 puts the
walkthrough in a **registered test file** and lets the example mirror it.

### §8.2 Downstream RFCs

**RFC-0011 (effect-annotations) is blocked on this RFC, and round 1's
provenance answer does not work.** 0011's `checkRaises` rests entirely on
`sxUnsat` claims — the half §0.3 identifies as the real payoff, which makes
0011 the motivating application the original draft lacked. 0011 §3 asks *which
bound* an `sxUnsat` held under ("a proof under `maxLoopUnwind = 8` is not a
proof"), and RFC-0008 (assurance-record) wants the same.

Round 1 answered: ship the bit, carry provenance in the `errors` seq. **That is
structurally impossible for the case 0011 needs.** An `sxUnsat` under §2.3 has
`scIncomplete notin runTaint` — so **no under-channel error entries exist on
precisely the runs whose bounds 0011 wants to record**. "Which bound did this
proof hold under" is a property of the *settings*, not of an error that by
construction was never minted. (`SymexErrorInfo` is also `kind + severity +
msg` — free text, no structured budget field.)

**Decision: bound provenance is a settings echo on the result**, not an error —
one additive field carrying the budget values the run actually used, shipped in
S11. It is small, it is correct for the `sxUnsat` case, and it gives 0011 and
0008 a single carrier. The claim that `errors` carries it is struck.

**RFC-0007 (trace-properties)** is a third downstream: it states at
`docs/rfc/0007-trace-properties.md:123` that "the same over/under-approximation
discipline RFC-0005 is building for symex applies here, in a different engine",
while declaring `Depends on: none` at `:38`. Per `docs/rfc/README.md` that soft
edge belongs in 0007's own Depends-on block. It also pins a type-placement
constraint worth stating: `SoundnessChannel`/`Taint`/`DegradeClass` go in
`smt/types.nim`, which imports no z3 — that is what lets 0007's trace engine
share the lattice.

**Coverage interplay — round 1's paragraph is factually wrong at HEAD.** It
claimed `{.cover.}`'s injected `recordEdge` calls are opaque and force whole-run
`sxUnknown`, and advised marking them `{.symexTransparent.}`. Issue #163 already
did exactly that (`src/nelli/coverage.nim:100-140`, which documents the change
as the G3fix follow-up): the parser **drops** the calls, so a `{.cover.}`'d SUT
taints nothing and the advice instructs users to add a pragma the procs already
carry. The live interaction is **user `{.symexOpaque.}` procs and the #137
opaque-call arm** (`canonicalize.nim:568`, `:586`) — now a named `dcSubstituted`
row in §3.1, because it havocs the return *and* drops the callee's mutations.

**Migration note.** Verdict changes are consumer-visible, so the release
carrying the first flipping slice needs a `docs/migration/<version>.md` entry
per `docs/rfc/README.md`. **It must lead with the contract change, not the
verdicts**: after this RFC, `symexFind` may *execute the SUT* at verdict time on
solver-chosen inputs (§4.2). No per-RFC downstream-audit document — that format
is retired.

## §9 — Alternatives considered

1. **May/must framing.** This is the standard abstract-interpretation
   vocabulary for the same duality (over ≈ may-analysis, under ≈
   must-analysis), and incorrectness logic's under-approximate triples are the
   same idea on the proof side. *Adopted as the conceptual grounding, rejected
   as the naming* (§2.1).
2. **A single `Taint` return from `channels()`** rather than a `(path, run)`
   pair. Rejected: it cannot express the `dcFabricated` class, whose survivor
   path and run-wide omission differ (§2.2).
3. **Value-level taint** — a channel on `SymVal`, joined through every
   arithmetic/comparison combinator. Rejected: it requires negation-swap join
   rules (§2.1), there is no way to make "forgot the join" unspellable in a new
   combinator, and the codebase already solved the one case that needed
   per-value precision with the deferred placeholder pattern (§2.2). It would
   also be XL on its own, touching every `lower()` arm.
4. **A distinct "fatal/no-answer" lattice element** for Z3 errors and walker
   faults. Rejected as a distinct encoding of an observable identical to `⊤`
   (§3.1) — `dcNoAnswer` names the class without adding a lattice point.
5. **Reason-set carrying** — thread `seq[SymexErrorKind]` per path and classify
   at verdict time. Partly adopted: the run coordinate **is** derived this way
   (§2.2). The path coordinate cannot be, because `errors` carries no path
   association.
6. **Keeping the blanket vetoes, or folding them in blind.** Round 1 posed
   these as a fork (keep / fold / fold-plus-audit). All three are rejected as
   policy knobs on a representational gap — §2.5 removes the gap instead.
7. **Discharge instead of taint.** `beBudgetExhaustedAssumedBound`
   (`types.nim:1539`) and `ObligationDisposition`
   (`odDischargedStatic`/`odLive`, `types.nim:1245-1255`) show the codebase
   already has a pattern where a bound is proven rather than labelled. Some
   under-sites could be *eliminated* rather than classified — genuinely better
   where it applies, and out of scope here (§11).
8. **A side table for decline scope** (`prog.declineSites: Table[errorIndex,
   markerId]`) instead of a `DeclineScope` field. Rejected: index-coupled
   parallel structure, and the invariant stops being a total function of the
   record (§2.5).
9. **Restricting what may be cached** instead of widening the sentinel — cache
   only clean `sxUnsat`, stop caching `sxUnknown` and tainted `sxRaised`.
   Rejected: it trades away cross-run reuse on exactly the slow runs, to avoid a
   schema change the walker-version key already makes free (§7).
10. **A watchdog around replay** rather than the `dcFabricated` eligibility
    gate. Rejected: an in-process watchdog is not safely buildable under §1.5's
    no-non-top-level-catch constraint, and the gate excludes precisely the class
    §0.3 already argues is worthless (§4.2).
11. **Bare `notin` at consumption sites** versus named predicates
    (`blocksSat`/`blocksUnsat`/`clean`) over `Taint`. Kept bare in §2.3 because
    the verdict rule reads self-evidently, and `trusted()` (§8.1) gives
    consumers the one predicate they need; revisit if a third channel appears.

## §10 — Risks

| risk | mitigation |
|---|---|
| One site misclassified under-as-over mints a false `sxUnsat` — the S1 failure class | Per-funnel flips (§5): each classification slice flips only its own pins, so a misclassification surfaces in that slice's audit instead of in one big-bang landing; `classOf` starts conservative-`⊤` so an unaudited kind is never wrong in the unsound direction |
| Shipping the UNSAT rule without the `isTargetLabel` solve mints a false `sxUnsat` | They are one slice (S1c), and §0.1/§2.3 state why they cannot be separated |
| Deleting the closure veto before the HOF/budget declines carry path taint reintroduces the S1 class | S9 is gated on S7 (§2.5) |
| A tainted candidate halts the walk and loses a verdict the engine earns today | Candidates live in `w.candidates`, never `w.found`; `shouldStop` untouched; pinned by §4.1 family 1 with the tainted arm discovered first |
| Replay executes user code at verdict time — effects, divergence, Defects | `dcFabricated` eligibility gate + per-target-kind scope + `roInconclusive` default; contract change leads the migration note (§4.2, §8.2) |
| The measured payoff turns out to be ~0 after the build | S0b measures it **before** S1; §13.1 is the scheduled fork |
| The classification table goes stale as kinds are added | `classOf` is an exhaustive `case`; a new kind is a compile error |
| `soundness.runTaint` becomes a second source of truth beside `errors` | The **run** coordinate is derived from `errors` via `classOf()`, never written, and the correspondence is pinned (§2.2). **The path coordinate is genuinely independent data** — `errors` carries no path association, so nothing can re-derive it. Round 1's blanket "derived, never set independently" was half false and would have blessed a refactor that silently destroyed the path coordinate |
| A cache hit serves a result that cannot state its own soundness | Sentinel widened to carry `Soundness`; replay precedes persist (§7) |

## §11 — Non-goals

- Widening the modelled fragment. This changes how gaps are *reported*, not
  how many there are.
- In-band migration of the residual boundary-abort class (§3.3).
- Channel-aware call-summary caching (§2.4) — soundness first, reuse later.
- Eliminating under-sites by discharging their bounds (§9.7).
- Unifying `hoistCaseExpr` with M5's `nnkIfExpr` arm — same idiom, worth
  sharing, but it is a refactor-under-green and belongs in its own slice.

## §12 — Round-1 forks — **resolved 2026-09-20**

### §12.1 Does the RFC keep the SAT side? — **YES, full scope (Corey)**

The question was whether to drop the SAT half now that §0.3 shows its payoff
is near-empty and that what remains of it (the k-unroll exhausted survivor) is
a fabricated continuation, unsound to trust without in-engine witness replay —
against a UNSAT-only scope of roughly M that delivers the entire *measured*
payoff.

**Resolved: full scope.** Both halves ship. The replay substrate and the SAT
relaxation stay in the plan, the SAT rule is symmetric with the UNSAT one, and
§2.6's raise-routing recovery is in scope. The consequence to hold onto: replay
is a *verdict mechanism* (§4.2), so the engine gains a new execution step.

*Round 2 note: this resolution is re-opened by §13.1, not because the decision
was wrong, but because round 2 changed the facts it was made on.*

### §12.2 The two blanket vetoes — **resolved by redesign, not by choosing**

The fork as posed offered fold / keep / fold-plus-pin. Corey rejected the
framing and asked for the best-in-class design instead. All three options
argue about *how much to trust a backstop*; §2.5 records the answer, which is
that the backstop is standing in for a representational gap.

**Resolved:** delete both vetoes; unify Class-A and Class-B so every
site-anchored decline mints a marker node and is scoped by reach-taint;
classify signature-scoped declines through the ordinary class table; and make
an unplaceable `sevError` a loud walker-completeness defect under a structural
totality pin. Three parallel unknown-forcing mechanisms collapse to one lattice
plus one invariant.

*Round 2 amended the **implementation**, not the decision: a third anchor class
is required for totality, the scope needs a carrier on `SymexErrorInfo`, the
closure veto has a hard precondition, and the whole thing is three slices
(S7/S8/S9), not one.*

## §13 — Round-2 forks — **open**

### §13.1 Does §12.1 still stand, given round 2's cost? — **for Corey**

§12.1 chose full scope on the understanding that the SAT half cost a replay
substrate. Round 2 changed three facts underneath that decision:

- the SAT half's **entire live payoff** is the veto deletion and the
  raise-routing recovery (§0.3) — the replay-gated cases are the near-empty
  half;
- replay **executes the SUT at verdict time**, a contract change to `symexFind`
  with effects, divergence and Defect hazards (§4.2), and it must be discharged
  by both `runSymex` consumers;
- the plan is now **13 slices with six walker bumps** and six Windows CI gates
  at ~1–1.5h each.

The RFC as written keeps full scope. The question is whether to keep carrying
it as one RFC, or to land S0–S9 (the UNSAT channel plus veto deletion — which
delivers *both* measured payoffs) and spin S2/S10's replay machinery into a
successor RFC. **My read: keep it as one RFC.** The SAT and UNSAT rules are one
design and splitting them leaves `isTargetLabel` half-migrated across a release
boundary; and the replay slices are genuinely separable *within* the plan, so a
mid-flight decision to defer them costs nothing. But the size is now honestly
**L+ bordering XL**, and whether that fits a single RFC in your release cadence
is your call, not a design question.

**This fork is also conditional on S0b.** If the measured over-taint-only
population comes back near zero, the UNSAT half's value becomes purely
prospective (RFC-0011's), and the scope question should be re-answered with the
number in hand. S0b runs before any product code for exactly that reason.

### §13.2 Should `blocked_by = ["0001"]` become a soft edge? — **for Corey**

§1 documents every 0001 dependency as **landed** (B7-2 at `cac15e6`, the SND-1
machinery, the N36–N40 migration), and the Depends-on prose calls 0001 prior
art rather than pending work. The tracker derives readiness from this edge, and
RFC-0011 inherits the delay transitively through 0005. Either the edge should
drop to a soft "builds on", or the specific still-pending 0001 item that blocks
S0 should be named. I have **not** changed the frontmatter — 0001 round 6 is
live, and the tracker graph is yours to move.

### §13.3 `feTransparentResultUsed` / `feTransparentArgNotInert` — warning or companion-anchored? — **resolved 2026-09-26 (Corey): neither — a separate channel; landed in S8**

**Resolution.** Both options assumed the two are declines that need a place in
the decline lattice. They are not: nothing is approximated *because of* them —
the call's opaque fallback, whose walk-time `feOpaqueCallUnmodelled` taints
every path through it, is the whole soundness story. What they report is that
the *user's* annotation makes a promise the code does not keep. So they left
`SymexErrorKind`'s live set: the two members are tombstoned ("retained for
ordinal stability, never emitted"), and the report rides a separate
`AnnotationViolation` channel (`pragma`, `kind` = `avResultUsed` /
`avArgNotInert`, `callee`, `site` = `file:line:col`, `msg`) on
`SymexProgram` → `RawResult` → `SymexResult` (and `ConcolicCollectResult`),
populated on every verdict branch. It is error-severity in spirit and stays
loud, but it is **verdict-neutral by construction**: no `classOf`, no
`DeclineScope`, no taint, and it cannot trip the cap veto. Why this beats both
options: `sevWarning` would have made a wrong promise *quieter* than a real
decline; `dskCompanionAnchored` would have added a scope kind for two members
and still left a non-decline in the decline lattice, where it vetoed runs the
annotation did not affect.

**The verdict consequence (S8).** Before S8 the parse-time `sevError` tripped
`capForcedUnknown` for the whole run. Now a hit on a path that never passes
the over-claimed call is a clean `sxSat` (rule 1; pinned in
`tests/tsymex_rfc0005_s8_scope.nim` (d)); a hit *through* it stays a
`dcSubstituted` candidate (replay-ineligible), and a dead target behind it
stays `sxUnknown` (the walk record's run coordinate carries `scIncomplete`).

The original framing, kept for the record:


These two are `sevError` diagnostics *companion* to a walk-time mechanism that
already taints reaching paths via `feOpaqueCallUnmodelled` (§2.5). Under the
`DeclineScope` invariant they have no anchor of their own, so they land in
bucket 4 — a "walker-completeness defect" they are not. Demoting them to
`sevWarning` makes the invariant total and costs a little loudness on
over-claimed `{.symexTransparent.}` pragmas; adding a fourth
`dskCompanionAnchored` scope keeps them loud at the cost of a scope kind that
exists for two members. The trade is *how loudly you want an over-claimed
pragma surfaced*, which is a product judgment rather than a design one — I have
no basis to prefer either.
