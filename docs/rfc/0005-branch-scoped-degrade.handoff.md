# RFC-0005 branch-scoped-degrade (soundness channels) — handoff

- **Stage:** 2 (design review). **Round 1 done** 2026-09-20; **round 2 done**
  2026-09-20, on `fable`, same five lenses (depth, breadth, design &
  ergonomics, implementation feasibility, load-bearing liveness).
- **Status:** draft (unchanged). Size **L**, now honestly L+ bordering XL —
  see §13.1. `wiring = unproven` remains accurate — nothing is built.
- **Blocked on:** **three round-2 forks await Corey (§13)**, none of which
  block starting S0/S0b.
- **Resume:** go to `/tdd` on §5's **S0** (a green characterization pin — safe
  first) then **S0b** (the measurement spike, no product code). Do not start S1
  until S0b's number is in hand — §13.1 is conditional on it.
- **Branch:** must be named `rfc-0005-*` or the three Windows legs never
  trigger. This matters more here than usual — see the Linux-hang note.

## What round 2 changed

Round 1 built the spec. Round 2 found that **four of its mechanisms were
unsound or unbuildable as specified**, that the slice plan would have shipped
green-but-inert for eight slices, and that two of its own flagship examples
contradicted the machinery meant to express them. The taxonomy, the naming, the
path-level decision and the veto redesign all survived.

### Corrections verified against the source (not taken on report)

| Round-1 claim | Reality | Where |
|---|---|---|
| Verdict rule: solve tainted paths in S8, flip UNSAT in S7 | **Mints a false `sxUnsat`.** `isTargetLabel` skips `trySolve` entirely on a tainted path, so a path that reaches the target unsolved is an *omission*. Shipping the UNSAT rule without the solve is exactly the failure the "S7 last" ordering existed to prevent. They are now one slice. | `runtime.nim:11159-11168`; §0.1, §2.3, S1c |
| Deleting `closureForcedUnknown` is safe once descent taint joins the caller | **Most closure emitters are not descents.** The HOF filter/map/fold declines mint `allocateSym("__hofFilterUnsupported")` into expression position and write only `closureCallErrors` + `sawUnknown` — **no path taint, and no `loweringDidDegrade`**, so the drain never taints the consumer. Same for `ceInlineBudgetExceeded` (`return funcApp`). Delete the veto first and a witness through the havoc value reports clean `sxSat`. | `runtime.nim:12505-12586`, `:11683-11691`, `:11815-11823`; §2.5, S7→S9 gate |
| "Every taint site has a `SymexErrorKind` in hand; the migration is mechanical" | **False at ≥9 sites.** The `isUnsupported` arm — §0.2's *flagship* example — forks tainted with **no error record at all**; `mkUnsupported` carries free text, not a kind. Also: cycle-break (no kind exists), over-cap missing-callee, `trySolve`'s `zsUnknown` result (both consumers, no kind — so a routine solver resource-out gets stamped `weInternalWalkerFault` today), handler re-raise, diverged closure body, break/continue, `isTargetLabel`'s own two writes. | `runtime.nim:11322-11338`, `:10855-10864`, `:7524-7525`/`:11167`/`:11491`, `:11226`, `:11866`, `:9564`, `:9574`; §2.2, S1b |
| `channels(k): tuple[path, run: Taint]` | **Cannot express its own motivating case.** The k-unroll survivor needs `(⊤, {scIncomplete})` and *no arm of round 1's sketch produced it* — §3.1 patched it with a footnote. Replaced by a named `DegradeClass` (5 members) with the coordinates derived once; 16 states → 5 named points. | §2.2 |
| `feUnsupportedOp` is "the known" split candidate | **`beBudgetExhausted` is the dangerous one** — one kind, three classes, merged deliberately, six emission sites. Round 1's §3.1 put "break-budget bails" under pure-drop, which gives `pathTaint = {}` and **removes** the taint the `maxCallDepth` site sets today → unreplayed `sxSat`. `feUnsupportedOp` itself has 12 sites in `runtime.nim` alone spanning ≥3 classes. | `runtime.nim:10759-10786`, `:9317`, `:9550`; §3.2 |
| §2.6 recovers raises on `scIncomplete`-only paths | **That set is empty by construction** — `pathTaint` only yields `{}`, `{scSpurious}` or `⊤`, closed under union. Round 1's DoD pin for it was unsatisfiable. The real recovery is the `scSpurious`-tainted raise, replay-gated. | §2.6, §6.2 |
| §2.1's negation proof ("inclusion preserved under arbitrary image") | **Not a proof.** Branching conjoins *different* predicates on the two sides; intersection preserves ⊇ only against the same constraint. Restated as per-trace simulation, with its hidden premise ("a `dcFreshSymbol` site's symbol is unconstrained at introduction") promoted to a pinned invariant — which makes §0.2 a corollary. | §2.1, DoD 5 |
| §8.2: carry 0011's bound provenance in the `errors` seq | **Structurally impossible for the case 0011 needs.** An `sxUnsat` has `scIncomplete notin runTaint`, so *no under-channel errors exist on exactly those runs*. Bound provenance is a settings echo, not an error. | §8.2 |
| §8.2's coverage paragraph | **Factually wrong at HEAD.** #163 already made `recordEdge`/`logCmp` `{.symexTransparent.}`; the parser drops them, `{.cover.}` taints nothing, and the advice tells users to add a pragma the procs already carry. The live interaction is user `{.symexOpaque.}` + the #137 opaque-call arm — which also had to move from `dcFreshSymbol` to `dcSubstituted` (it drops the callee's mutations). | `coverage.nim:100-140`, `canonicalize.nim:568,586`; §8.2, §3.1 |
| §2.4 row 3 cites `runtime_heap.nim:843-858` | No `Path(` construction there — it's the deref-drain comment. The real `uncertain: false` is `descentBase`, `runtime.nim:11730`. Four more cross-path sinks were missing entirely (`parseIntGateConstraintsLive`, `currentClosureCallAxioms`, `stripDecompConds`, `defectSurvivorPc` — all drained into *every* `trySolve`). | `runtime.nim:7481-7496`, `:11729`; §2.4 |
| §8.1: `forcedBy` on sxUnknown, `satPathTaint`/`replayVerified` on sxSat | `sxRaised` got **no taint fields**, yet §2.3 makes it obey the SAT rules verbatim and §6 pins a replay-gated raise — unauditable as drafted. Replaced by one common `Soundness` object (the `heapSnapshot` precedent) + `trusted()`. And `forcedBy` **is not the actionable surface**: it's a join, so it saturates to `⊤` on any multi-cause run; `gaps()` over `DegradeClass` is. | `types.nim:1888-1933`; §8.1 |
| §7 handles the cache | Key yes, **value no**. The verdict sentinel is an empty `seq[ChoiceNode]`, so every cache hit breaks the `forcedBy != {}` invariant and cannot say whether a served SAT was replay-confirmed. Sentinel widened; replay-precedes-persist added. | `symex.nim:259-297`, `:389-410`; §7 |
| Replay: `replayWitness(fn, witness, label): bool` | Wrong shape three ways — label-only (can't serve the raise-flavoured targets §2.3 puts in scope), `bool` conflates *refuted* with *couldn't run*, and it **cannot be a proc**: splatting a typed witness is macro codegen, so replay runs *after* `runSymex` returns and candidacy must cross `RawResult` unspellable-as-sat. **Both** `runSymex` consumers must discharge it; round 1's DoD wording forced only one. | `symex.nim:1481-1490`, `:1272`, `:2061`; §4.2 |
| Slice plan: S0 makes it "run end-to-end from slice 1" | It does not — S0 *records* today's behaviour. The first observable flip was **slice 9**; eight slices of lattice, replay and reclassification changed nothing a test could see, and the plan's own top risk (one under-as-over misclassification) stayed undetectable until S7's big bang. Also: S6 scheduled the 272-pin flip audit *before* any slice that can flip a pin. | §5 |
| S1/S6/S6a/S7/S8 are slices | **All rounds.** S6a alone: 39 `parseErrors.add` sites in a 9.7k-line `dsl_parser.nim` + the verdict block + closure descent + an unspecified type change — *and* it changes verdicts one slice before the "deliberately last" S7, with no walker bump scheduled. | §5 |

### The two structural changes

**1. `classOf` is total from S1 with a conservative `⊤` default.** All-`⊤`
reproduces today's behaviour bit-for-bit, so the verdict rule lands early
(S1c) as a behaviour-preserving refactor, and each classification slice then
flips **only its own funnel's pins** with its own audit. S0's exhibit is chosen
to route through `allocDegrade`, so the first observable payoff is **slice 6 of
13** instead of slice 10 — and a misclassification surfaces in the slice that
made it. Cost, accepted: six walker bumps instead of two, six Windows gates at
~1–1.5h each.

**2. `w.runTaint` is derived at drain time from the error seqs**, not written
at ~52 sites. This makes §10's "derived from errors, never set independently"
principle real instead of aspirational, and kills the largest mechanical
migration. It has a precondition — error-pairing totality — which is exactly
what S1b's kind-minting delivers. The **path** coordinate stays written, because
`errors` carries no path association; §10 row 5 was half false and is corrected.

### New sequencing (13 slices)

`S0` green exhibit + veto companion → **`S0b` measure the payoff before
building it** → `S1` lattice/carrier/funnel → `S1b` mint the missing kinds +
correspondence pin → `S1c` verdict rule **including the `isTargetLabel` solve**
→ `S2` replay substrate → `S3` monotonicity harness → **`S4` allocDegrade — S0's
exhibit flips here** → `S5` strings/placeholder → `S6` heap + the two mandatory
kind splits → `S7` cross-path sinks + closure/HOF taint migration → `S8`
`DeclineScope` + Class-A/B unification (vetoes retained) → `S9` delete the
vetoes → `S10` SAT relaxation → `S11` public surface.

### Measurements taken at HEAD (`6cbfe8f`)

| quantity | value |
|---|---|
| `sawUnknown = true` write sites in `src/` | 52 (**not the audit checklist** — see §3.4) |
| `forkPathTainted` call sites | **24 live** (round 1 said 25; regenerate in-slice) |
| `SymexErrorKind` members | 41 (~6 tombstoned) + the kinds S1b mints |
| `== sxUnknown` assertions in `tests/` | 272 across 110 files |
| `== sxUnsat` assertions in `tests/` | 283 across 130 files — **cannot regress** |
| `symexWalkerVersion` at HEAD | `"140"` (`canonicalize.nim:187`) |
| `runtime.nim` + its five `include`s | one ~17.6k-line compile unit |
| `dsl_parser.nim` | 9.7k lines, 39 `parseErrors.add`, 76 `mkUnsupported` refs |
| Windows CI cost | ~1–1.5h wall per gated push, ×6 semantics-bearing slices |

**Non-finding, checked and cleared:** concurrency. The fuzzer isolates workers
as processes (`fuzz.nim:160-178`) and every degrade sink is `{.threadvar.}`
(`runtime.nim:1233`), so `w.runTaint` inherits `sawUnknown`'s single-threaded
story unchanged.

### Constraints recorded in the RFC that lived nowhere findable

- **No non-top-level `try`/`except`** (round 1, §1.5) — now also the reason
  §4.2 rejects a replay watchdog in favour of the eligibility gate.
- **The most relevant pin suite cannot run on Linux.**
  `tests/tsymex_r6_b7r2_pathscope.nim` is one of the six hangers skipped in
  `scripts/sweep.sh:91-96`, so **S10 has no local gate at all**.
- **`examples/` is built by neither CI nor `nimble test`** — the file
  `examples/symex_loops.nim` records that it stopped compiling for a full
  release cycle unnoticed (its own lines 60-63). S11 puts the user-facing
  walkthrough in a registered test file instead.

## Review ledger — round 2

| lens | headline finding |
|---|---|
| depth | The closure veto is load-bearing for ≥4 value-substituting sites that carry no path taint — deleting it as specified reintroduces the S1 failure class; `beBudgetExhausted` is a mandatory 3-way split whose round-1 row would *remove* existing taint; §2.1's proof isn't one |
| breadth | Two `trySolve`-unknown sites taint with no kind (solver resource-out is stamped a walker fault today); `SymexFinding` + the render layer can't carry the new surface; §8.2's coverage paragraph is pre-#163; four undocumented cross-path sinks; RFC-0007 owes a soft edge |
| design | `channels()` can't express its own motivating case → `DegradeClass`; one `degrade()` funnel to make all three acts one kind mention; `Soundness` as a common field (sxRaised had none); `forcedBy` saturates to ⊤ and isn't the actionable surface |
| feasibility | **The S7/S8 boundary mints a false `sxUnsat`**; replay can't be a proc and its weight is on the wrong slice; S1/S6/S6a/S7/S8 are all rounds; the 272-pin audit was scheduled where zero pins can flip |
| liveness | The payoff sits behind eight inert slices; the measured payoff is counted at slice 8 and could be ~0; the SAT half's *live* payoff (veto + raise-routing) had no exhibit and no DoD pin |

Three lenses independently reached the candidate-vs-`shouldStop` regression
(a tainted candidate entering `w.found` halts the walk before a clean witness
is solved — so the "relaxation" can *lose* verdicts the engine earns today).
It was then verified directly at `runtime.nim:8212-8221` / `:11159-11168`
before being written into §2.3 as the candidate-pool rule.

## Open forks — awaiting Corey (§13)

1. **§13.1 — does §12.1's full-scope resolution still stand?** Not because it
   was wrong, but because round 2 changed the facts: the SAT half's live payoff
   is *only* veto-deletion + raise-routing; replay executes the SUT at verdict
   time (a contract change to `symexFind`); the plan is 13 slices / 6 bumps /
   6 Windows gates. My read: keep it as one RFC — the replay slices stay
   separable in-flight. **Conditional on S0b's number.**
2. **§13.2 — should `blocked_by = ["0001"]` become a soft edge?** Everything §1
   takes from 0001 is landed. The tracker derives readiness from it and 0011
   inherits the delay. Frontmatter deliberately **not** changed.
3. **§13.3 — `feTransparentResultUsed`/`feTransparentArgNotInert`:**
   `sevWarning`, or a fourth `dskCompanionAnchored` scope? The trade is how
   loudly an over-claimed `{.symexTransparent.}` should be surfaced — a product
   judgment, no design basis to prefer either.

**Lesson for future rounds:** round 1 verified its *citations* and did it well
— every line number it quoted was accurate. What it did not verify was whether
its own new machinery could express its own examples. Both of round 2's
design-level catches (`channels()` vs the k-unroll survivor, §2.6 vs the
`pathTaint` codomain) were found by *type-checking the RFC against itself*, not
against the source. Do that pass explicitly next time.
