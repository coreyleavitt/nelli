# Constrained generation & modal PBT (#TBD) build plan

> The design and phase plan for **solver-driven constrained generation**
> in nelli — a strategy combinator that produces values directly from
> the satisfying domain of an SMT formula. Modal type systems are the
> headline application; the engine generalizes to any constraint domain
> expressible in nim-z3's supported decidable theory fragments.

## Status

| | |
|---|---|
| **Plan** | drafting (2026-06-02, revised 2026-06-02 after multi-agent review) |
| **Build status** | not started; depends on Phase 7 substrate (shipped 2026-06-02) |
| **Trigger condition** | first downstream consumer — `intonaco` M-ζ Stage 2 (`~/projects/intonaco/docs/rfc-modal-verification-pipeline.md`); proceeding regardless per the SYMEX_PLAN precedent. |
| **SMT substrate** | [nim-z3](https://github.com/coreyleavitt/nim-z3) v1.0.0 |
| **Position** | third role for symex; complements `assertCoveredBy` (output verifier) + `loadSymexWitnesses` (input source, shipped) / `withSymexSeeds` (combinator, deferred). |
| **Estimated effort** | 12-18 weeks engineering + 6-8 weeks foundations (mechanized soundness proof, Phase 5a required). Phase 0 (ADRs): 1 week. Phase 1 (primitive): 1.5-2 weeks. Phase 1.5 (diversity modes): 1-1.5 weeks (conditional; subtract ~1.25 weeks if truly deferred). Phase 2 (DSL): 2-3 weeks. Phase 3 (integration): 1.5-2 weeks. Phase 4 (refinement-subtype case study): 4-6 weeks. Phase 5a (mechanized soundness proof, required): 6-8 weeks. Phase 5b (completeness + refinement extension, stretch): 8-12 weeks. Documentation: 1 week. (Phase 1.5 counted as likely-required based on case-study evidence; subtract ~1.25 weeks if truly deferred.) |
| **Research artifact target** | Foundations-and-tools paper. **ICFP submission-if-ready (artifact prioritizes intrinsic technical quality; venue submission is aspirational)**: the work earns its place there with (a) a mechanized proof of `modalSystem` compilation correctness (the central theorem), (b) two case studies (Davies-Pfenning modal calculus type system over intonaco; refinement-type system over a small Liquid-Haskell-like fragment). ISSTA / TACAS as fallback venues if the mechanized proof scope reduces. Working title: *"A Solver-Backed Compilation Framework for Type-Theoretic Constraints: Verified Generation for Modal and Refinement Systems."* |

## Research question

> **Can declarative modal type system axioms (in the Davies-Pfenning
> modal calculus tradition) be compiled to SMT constraints that serve as sound,
> budget-efficient generators for property-based test inputs, covering
> the satisfying domain of well-typed programs more effectively than
> rejection sampling or bounded-exhaustive search?**

Supporting hypotheses (testable in the planned evaluation):

- **H1 (tractability)**: SMT-based generation achieves an
  order-of-magnitude higher well-typed hit rate than rejection
  sampling at non-trivial constraint sizes on both case studies. The
  exact ratio is established by Phase 2 measurement; the qualitative
  direction is the hypothesis. *Measured empirically against three
  baselines on intonaco's CShape and the refinement-types case study:*
  (1) *rejection sampling (primary baseline);*
  (2) *Luck (POPL 2017) — DSL-based generator with custom narrowing;
  comparison measures hit-rate and generation time on CShape laws
  expressible in Luck;*
  (3) *Targeted PBT (Löscher & Sagonas, ISSTA 2017) —
  simulated-annealing navigation toward constraint-satisfying values;
  comparison measures hit-rate on sparse-domain CShape laws.*
- **H2 (Compilation correctness, mechanized).** The `modalSystem` /
  `refinementSystem` macro defines a compilation function
  `compile : SourceLaws → SMTFormula` and a decoder
  `decode : Model → SourceValue` such that: **(soundness)** for every
  well-formed source block `S` and every Z3 model `m` of `compile(S)`,
  `decode(m)` satisfies every law in `S`; **(completeness, stretch)**
  for every source value `g` satisfying every law in `S`, there exists
  a Z3 model `m'` of `compile(S)` with `decode(m') = g`. Both
  directions are mechanized in Lean 4 over a fixed decidable theory
  fragment (QF_LIA + bounded TC, per ADR-MODAL-0006). Soundness is
  required (Phase 5a); completeness is stretch (Phase 5b).
- **H3 (diversity)**: `dmDimensionRotation` covers measurably more
  shape classes than `dmBlockingClause` baseline alone, measured by
  Shannon entropy over a predefined partition of the satisfying
  domain. *Empirical evaluation in P1.5.1.* Empirical evaluation in
  P1.5.1 (Phase 1.5 is conditional; if deferred, H3 is not formally
  evaluated in the paper).
- **H4 (generality across type-theoretic constraint systems)**: the
  same engine + DSL framework, with theory-specific tactics, admits
  both Davies-Pfenning modal calculus type systems AND refinement-type systems
  with comparable hit-rate improvements over rejection sampling. *This
  is the second case study (Phase 4) and earns the "generalizes
  beyond one substrate" claim that top-tier venues require.*

## Thesis

The novel contribution of this plan is a **strategy combinator family
that produces values from the satisfying domain of an SMT formula** in
a general-purpose property-based testing library, paired with **a
declarative DSL (`modalSystem`) that compiles modal type system axioms
to SMT formulas at macro-expansion time.**

Two guarantees stand as headline claims:

- **Sound**: every drawn value satisfies the formula by construction,
  *provided* (a) the decoder is total over the constrained domain and
  queries only variables explicitly constrained by the formula, (b) the
  theory fragment is in a decidable class where Z3 is complete and
  returns no spurious models, and (c) Z3 itself has no active
  soundness defects for the theories in use. Formulas combining
  universal quantifiers with recursive predicates (e.g.
  `transitiveClosure`) are a known hazard — Z3 issue #4901 documents
  spurious SAT models in this fragment — and require explicit handling
  (see §Decidability hazards).
- **Compositional**: the resulting `Strategy[T]` composes with
  nelli's existing pipeline. `map`/`filter`/`flatMap` work as
  closures over the decoded value; shrinking maps to the
  choice-sequence regression DB via the existing `RawWitness`
  encoding; multi-role properties (`modelGenerator` +
  `assertCoveredBy` + `loadSymexWitnesses`) share the SMT runtime.

Diversity is treated per-mode in §Model diversity rather than as a
unified headline guarantee, because the three available modes
(`dmBlockingClause` / `dmDimensionRotation` / `dmSampling`) provide
qualitatively different guarantees and apply to different theory
fragments.

The `modalSystem` DSL specializes the engine for modal type systems
following Davies' λ□ / two-tier modal calculus (Davies, LICS 1996;
Davies & Pfenning, MSCS 2001).[^lambda-box] No prior PBT library
compiles modal type theory axioms to an SMT formula constant; that
combination is the central novelty for a top-tier PL-venue submission.

[^lambda-box]: We follow Davies' λ□ (LICS 1996) and its judgmental
reconstruction in Davies-Pfenning (MSCS 2001); CShape's tier system
models λ□'s necessity introduction but does not introduce a possibility
(◇) modality, so the full S4 axiomatic system is out of scope.

## Motivation

Property-based testing's classical pipeline (generate → filter →
check) degrades on sparse satisfying domains. The hit rate falls as
the constraints tighten; rejection sampling wastes generator effort
on unsatisfying candidates.

**Concrete sparsity expectation** (the intonaco case): the C-shape
modal type system with N=20 nodes has a satisfying-domain
cardinality on the order of 2^20 (tier assignment) further constrained
by coherence laws, embedded in a roughly 3^20 unconstrained graph
space. Rejection sampling's well-typed hit rate is expected to fall
below 1% at N=20 and to degrade sharply past N=10. *These numbers
will be empirically established as part of Phase 2 evaluation
(hypothesis H1); the RFC asserts the expected order of magnitude
based on the constraint density, not a measured value.*

**Other constraint domains where this matters** (motivating breadth
without committing to evaluation):

- **Refinement types** (`Pos = {x: Int | x > 0}`, `SortedList[T]`).
  A candidate second case study for ICFP-track submission.
- **Graph invariants** (acyclic DAGs, balanced trees,
  schedule-feasible resource graphs).
- **Database schema invariants** (FK closure, normalization).

The headline application is modal types because (a) the intonaco
substrate exercises them in production, (b) the Davies-Pfenning modal
calculus gives the DSL a vocabulary that mechanically compiles to
SMT, and (c) the contribution lands cleanly as "engine support for
constrained generation" (a nelli capability) AND "modal PBT" (a
novel combination not in the literature, modulo the related work
below).

## Position relative to existing roles

The Phase 7 symex shipment decomposed nelli's solver use:

| Role | Surface | Phase 7 status | This plan |
|---|---|---|---|
| Output verifier | `assertCoveredBy(fn, target)` | shipped | — |
| Input source (seed PBT) | `loadSymexWitnesses(...)` (shipped) + `withSymexSeeds` (deferred) | shipped / partial | — |
| **Constrained generator** | `modelGenerator[T](formula, decoder)` + `modalSystem` DSL | — | **proposed** |

The three roles share the SMT runtime. A single property test can
compose all three:

```nim
property "modal scheduler matches spec, with coverage":
  given g in modelGenerator(CShape_formula, decodeBindingGraph)  # role 3
  ensure leanRunner(g) ≅ nimScheduler(g)
  assertCoveredBy(nimScheduler, target = "diamond-glitch-branch")  # role 1
  # role 2: failures saved to DB via existing `loadSymexWitnesses` path
```

## Related work

The literature landscape for solver-backed PBT input generation has
four threads. This plan positions against each.

**Bounded-exhaustive generation from declarative invariants.**

- **Korat** (Boyapati, Khurshid, Marinov; ISSTA 2002, "Korat:
  Automated Testing Based on Java Predicates") — bounded-exhaustive
  generation from declarative class invariants over Java/JML. Closest
  precursor to constrained generation as a concept. Korat uses DFS
  over data structure shapes with pruning via field-access tracking.

  The novel differentiators of this plan relative to Korat:
  - **Theory generality**: nim-z3's first-order theories (arith, BV,
    arrays, datatypes, quantifiers) admit a strictly larger class of
    constraints than Korat's predicate-on-finite-shapes vocabulary.
  - **Modal type system specialization**: the `modalSystem` DSL
    compiles Davies-Pfenning modal calculus axioms to SMT; no prior
    Korat-family work targets modal type systems.

  Choice-sequence shrinking and regression-DB integration are
  acknowledged as nelli engineering infrastructure, not as research
  contributions over Korat.

**Constraint-driven PBT generators.**

- **Luck** (Lampropoulos, Gallois-Wong, Hritcu, Hughes, Pierce, Xia;
  POPL 2017, "Beginner's Luck: A Language for Property-Based
  Generators") — *the closest prior work to the `modalSystem`
  approach*, and must be distinguished carefully. Luck is a DSL where
  predicates are decorated with lightweight annotations that guide
  constrained generation at each variable instantiation; the runtime
  uses a custom narrowing engine for choice.

  Relative to Luck:
  - **Compile-time vs. runtime formula construction**: `modalSystem`
    emits an `SMTFormula` value at macro-expansion time; Luck's
    constraint resolution happens at generator-run time. Compile-time
    construction enables formula reuse, multi-role composition with
    the SMT solver, and Z3's amortized solver state.
  - **Target domain**: Luck operates over general predicate constraints;
    `modalSystem` is specialized for modal type theory axioms in the
    Davies-Pfenning modal calculus lineage.
  - **Backend**: Luck has a custom narrowing engine; `modalSystem`
    delegates to Z3 via nim-z3.

**Typed generator extraction from proof assistants.**

- **QuickChick** (Hritcu, Paraskevopoulou, Dénès, Lampropoulos, Pierce;
  ITP 2015, "Foundational Property-Based Testing"; with later work by
  Lampropoulos, Paraskevopoulou, Pierce; POPL 2018, "Generating Good
  Generators for Inductive Relations") — typed PBT generators extracted
  from Coq proofs. Dual approach to this plan: QuickChick extracts
  generators from constructive proofs of generation procedures; this
  plan compiles declarative constraints to a solver. Trade-off:
  QuickChick provides proof-grade soundness at the cost of per-type
  Coq proof effort; this plan provides solver-grade soundness with
  lighter per-application specification.

**SMT/symex test generation in deployed tools.**

- **Pex / IntelliTest** (Tillmann, de Halleux; TAP 2008, "Pex: White
  Box Test Generation for .NET") — concolic SMT-backed test generation
  for .NET, deployed in Visual Studio. *Invalidates any "first
  production PBT with SMT-backed generation" claim.* The technical
  distinction this plan must draw: Pex is **program-path-driven**
  (concolic execution explores paths and asks the solver for inputs to
  cover branches), while this plan is **specification-driven** (the
  solver generates from a user-supplied formula representing the
  desired input domain). The distinction is real but had to be made
  explicit, not left to the reader.
- **KLEE** (Cadar, Dunbar, Engler; OSDI 2008) — symbolic execution
  for test generation in C. Same path-driven framing as Pex; included
  here to establish the broader concolic-SMT-test-generation tradition
  that this plan is *not* a direct contribution to.
- **CrossHair** (Phillip Schanely) — Python contract checker via
  symbolic execution on bytecode. Architecturally distinct from
  specification-driven generation: CrossHair finds counterexamples to
  contracts; this plan generates inputs satisfying a formula. The
  Hypothesis-CrossHair integration (2021 blog post by Schanely) is a
  hybrid workflow.

**Fuzzing-integrated PBT.**

- **Crowbar** (Dolan, Preston; OCaml Workshop at ICFP 2017) —
  *coverage-guided fuzzing (AFL-based) integrated with PBT*, working
  via compile-time instrumentation of OCaml bytecode. Distinct
  architecture: no SMT solver, no specification-driven generation;
  AFL drives test input selection through coverage feedback.

**Sampling-based SMT (load-bearing for §Model diversity).**

- **UniGen** (Chakraborty, Meel, Vardi; DAC 2014, "Balancing
  Scalability and Uniformity in SAT Witness Generator") — hashing-
  based approximate-uniform sampling **for CNF Boolean formulas**.
  Provides a formal (1+ε)-approximate-uniform guarantee.
- **QuickSampler** (Dutra, Laeufer, Bachrach, Sen; ICSE 2018,
  "Efficient Sampling of SAT Solutions for Testing") — successor with
  better scaling for Boolean formulas, weaker formal guarantees.
- **MeGASampler** and **HighDiv** (Lai, Li, Luo; "SMT(LIA) Sampling
  with High Diversity," arXiv 2503.04782 / Springer LNCS
  doi:10.1007/978-3-032-22752-2_10, 2025) — state of the art for
  SMT(LIA) sampling. HighDiv integrates CDCL(T) with local search,
  achieving ~53% AST coverage vs. MeGASampler's ~34% on standard
  benchmarks. Both provide heuristic diversity without the formal
  (1+ε)-uniformity guarantees UniGen offers for the Boolean case.
  *This matters for `dmSampling` — see §Model diversity.*

**Modal type theory pedigree.**

- **Davies λ□** (R. Davies, "A temporal-logic approach to
  binding-time analysis," LICS 1996) — introduces λ□, the two-tier
  modal calculus with □-introduction for static/dynamic binding-time
  distinction. The load-bearing source for CShape's tier system; previously described as "Davies-Pfenning S4 framing" — renamed throughout this document to "Davies' λ□ / two-tier modal calculus" per Round 2 revision (CShape has □-introduction but no ◇, so the full S4 axiomatic system is out of scope).
- **Davies & Pfenning** (2001, "A Judgmental Reconstruction of Modal
  Logic," MSCS 11(4)) — the actual vocabulary that the `modalSystem`
  DSL compiles from. λ□ necessity (□) under judgmental reconstruction;
  CShape models necessity introduction but not ◇. This is the
  load-bearing modal type theory citation for the plan's `CShape`
  example.
- **Birkedal et al.** (LICS 2011, "First Steps in Synthetic Guarded
  Domain Theory") — semantic foundation for guarded recursion. Cited
  for the broader modal-types landscape, but the static/dynamic tier
  distinction this plan targets is Davies' λ□ / two-tier modal lineage,
  not guarded-recursion lineage.
- **Bahr et al.** (LICS 2017, "The Clocks Are Ticking: No More
  Delays!") — guarded recursion / clock-typed FRP. Cited for
  *temporal* modal types, which are out of scope for this plan but
  relevant context for the broader modal-types-in-PL landscape.
- **Cave & Pientka** (LFMTP 2013, "First-Class Substitutions in
  Contextual Type Theory") — contextual modal type theory.
  Relevant if the `modalSystem` DSL extends to context-sensitive
  modalities; out of scope for Phase 2.

**Counterexample generation and targeted PBT.**

- **SmartCheck** (L. Pike, "SmartCheck: automatic and efficient
  counterexample reduction and generalization," HASKELL 2014) —
  automatic shrinking and generalization of counterexamples in Haskell
  PBT. Cited as prior art for structured counterexample reporting;
  Phase 4's subtype-violation witnesses extend this direction to the
  type-theoretic domain.
- **Targeted PBT** (A. Löscher and K. Sagonas, "Targeted
  property-based testing," ISSTA 2017) — simulated-annealing
  navigation toward constraint-satisfying values; applicable to
  sparse-domain problems. Compared against in evaluation (H1 baseline
  on sparse-domain CShape laws; see §Evaluation plan).

**Refinement types (prior art; we generate, they verify).**

- **LiquidHaskell** (N. Vazou et al., "Refinement types for Haskell,"
  ICFP 2014) — the foundation of Liquid Haskell's refinement-type
  checking direction. LH can verify `{x|P} <: {x|Q}`; it does not
  generate concrete models of `P(x) ∧ ¬Q(x)`. Phase 4 occupies that
  complementary position.

**What this plan adds (the precise novelty statement, after the
literature review):** to our knowledge, nelli with this plan would
be the first PBT library to compile modal type system axioms to an SMT
formula constant for specification-driven input generation — distinct
from concolic path-coverage (Pex/IntelliTest, KLEE), contract
checking (CrossHair), coverage-guided fuzzing (Crowbar), and
predicate-decorated runtime constraint solving (Luck). Choice-sequence
shrinking for SMT-decoded models and three-role composition sharing a
single SMT runtime are supporting engineering contributions.

## Surface

### Primitive: `modelGenerator`

```nim
# nelli/smt/model_generator.nim (new)

import ./types, ./dsl, ./runtime
import ../strategy, ../choice
import z3

type
  ModelFormula* = proc(solver: Z3Solver)
    ## Caller-supplied procedure that adds assertions to a pre-scoped
    ## Z3 solver. The solver is owned by the modelGenerator's per-run
    ## state; the formula adds its assertions and returns. The decision
    ## to represent formulas as solver-mutators (rather than a separate
    ## SMTFormula type) follows nelli's existing pattern of
    ## constraints living on the solver, not in a separate AST layer.

  ModelDecoder*[T] = proc(w: RawWitness): T
    ## Decoder maps the path-keyed witness (same shape as symex
    ## extraction in smt/runtime) to T. Callers use the existing
    ## `readInt`/`readBool`/etc. reader API that `renderAsChoices` and
    ## `emitTyAndReader` target. Decoder MUST be total over the
    ## constrained domain; partial decoders break soundness.
    ##
    ## Prerequisite: `RawWitness` in `src/nelli/smt/runtime.nim` is
    ## currently module-private; it must be promoted to `RawWitness*`
    ## before Phase 1 ships. Tracked as a P0 prerequisite.

  ModelGeneratorSettings* = object
    maxDraws*:      int
    solverTimeout*: Duration
    diversity*:     DiversityMode
    onTimeout*:     TimeoutPolicy
    onUnknown*:     UnknownPolicy
    resetEvery*:    int                 ## solver-reset cadence (0 = never)

  DiversityMode* = enum
    dmBlockingClause,
    dmDimensionRotation,
    dmSampling

  ModelFinding* = object
    formulaHash*:  string
    diversityMode*: DiversityMode
    drawCount*:    int
    exhausted*:    bool
    timedOut*:     bool
    z3Version*:    string

  DomainExhausted* = object of CatchableError
  DomainTimeout*   = object of CatchableError
  DomainUnknown*   = object of CatchableError

proc modelGenerator*[T](
    formula:  ModelFormula,
    decoder:  ModelDecoder[T],
    settings: ModelGeneratorSettings = defaultModelGeneratorSettings()
): Strategy[T]
  ## Strategy whose draws come from successive SAT models of the
  ## assertions `formula` adds to the per-run solver instance.
  ##
  ## Per-run solver state lives in a threadvar sink analogous to
  ## `symexCapture` / `consumeSymexFindings` (see ADR-MODAL-0010).
  ## The strategy closure does NOT capture the solver; reuse across
  ## property runs is safe.
  ##
  ## SOUNDNESS: every returned value satisfies the formula PROVIDED
  ## (a) the decoder is total over the constrained domain, (b) the
  ## formula lies in a decidable theory fragment where Z3 returns no
  ## spurious models, (c) Z3 itself has no active soundness defects
  ## for the theory in use. Formulas combining universal quantifiers
  ## with recursive predicates (e.g. transitiveClosure) are a known
  ## hazard — see §Decidability hazards.
  ##
  ## COMPLETENESS: `dmBlockingClause` mode enumerates every
  ## syntactically distinct model (per-variable assignment equality)
  ## until `maxDraws` or UNSAT. This guarantee applies only when the
  ## satisfying domain over the constrained variables is FINITE. For
  ## integer-valued fields without explicit domain bounds, the domain
  ## is infinite; `DomainExhausted` will never be raised naturally,
  ## and the run terminates at `maxDraws` only. Add explicit bounding
  ## constraints to achieve true finite-exhaustion semantics.
  ##
  ## SHRINKING: each drawn model maps to a `seq[ChoiceNode]` via the
  ## existing `RawWitness` encoding; shrinking minimizes the choice
  ## sequence and decodes to a smaller model. Non-satisfying shrink
  ## candidates are rejected via per-step re-validation (SMT model
  ## evaluation, O(formula-size)) per ADR-MODAL-0008 (resolved).
  ##
  ## FAILURE MODES:
  ##   - UNSAT after current blocking clauses → DomainExhausted
  ##   - per-solve timeout reached → DomainTimeout (or skip per onTimeout)
  ##   - solver returned `unknown` → DomainUnknown (or skip per onUnknown)
```

### Declarative form: `modalSystem`

```nim
# nelli/modal.nim (new)

modalSystem CShape:
  ## Two-tier modal type system following Davies' λ□ / two-tier modal
  ## calculus (Davies 1996, Davies-Pfenning 2001). Compiles to:
  ##   const CShape_formula*: ModelFormula = ...
  domain Node: int                    # universe (0..N-1 with N bounded)
  field  tier:   {Static, Dynamic}    # ASCII; □/◇ accepted as aliases
  field  height: int                  # bounded explicitly via law below
  field  deps:   set[Node]

  law "height bound":
    forall n: 0 <= height(n) and height(n) <= maxHeight   # finite domain

  law "static-introduction":
    forall n: tier(n) == Static implies
      forall d in deps(n): tier(d) == Static or isBoundary(d)

  law "height composition":
    forall n: height(n) == 1 + maxOver(deps(n), height)

  law "cross-tier wall":
    forall n: tier(n) == Static implies
      not exists d in readSet(n):
        tier(d) == Dynamic and not isBoundary(d)

  law "acyclicity":
    # HAZARD: transitiveClosure + universal quantifier is in an
    # undecidable fragment and triggers known Z3 spurious-model
    # behavior (issue #4901). See ADR-MODAL-0006 for the resolution:
    # bounded-unrolling encoding with explicit depth limit derived
    # from `maxHeight`.
    forall n: not (n in transitiveClosureBounded(deps, n, maxHeight))
```

**Predicate vocabulary** (Phase 2; precise specification in
ADR-MODAL-0006):
- Logical: `forall`/`exists`/`implies`/`and`/`or`/`not`
- Equality: `==`/`!=`
- Set: `in`/`not in`/`subsetOf`
- Arithmetic: over `Int` fields, bounded
- Aggregations: `maxOver`/`minOver`/`sumOver`/`cardinality`
- Closure: `transitiveClosureBounded` (depth-limited, NOT general TC)
- Escape: `rawZ3:` block emitting nim-z3 assertions directly

`transitiveClosureBounded` is the decidable encoding; general
`transitiveClosure` is explicitly NOT in the vocabulary because of
the decidability hazard documented below.

### Decoder protocol

```nim
proc decodeBindingGraph(w: RawWitness): BindingGraph =
  ## Decoder shape — consumer reads from the path-keyed witness via
  ## the existing reader API (same one symex uses).
  ## Decoder MUST be total over the constrained domain; partial
  ## decoders break soundness.
  let nNodes = w.readInt("|Node|")
  result.nodes = newSeq[NodeId](nNodes)
  for i in 0 ..< nNodes:
    result.tiers[i]   = Tier(w.readInt("tier." & $i))
    result.heights[i] = w.readInt("height." & $i)
    # ... etc.
```

### Reporting

`Report[T]` gains a new field parallel to `symexFindings`:

```nim
type
  Report*[T] = object
    # ... existing fields ...
    symexFindings*: seq[SymexFinding]     # existing
    modelFindings*: seq[ModelFinding]     # NEW, parallel
```

`SymexFinding` is a sealed concrete type and is not extended;
`ModelFinding` is its parallel. Aggregation across both happens at the
report-rendering layer.

## Model diversity

The diversity question is where foundations risk concentrates. The
three modes provide qualitatively different guarantees and apply to
different theory fragments.

**The problem.** Z3's default model-finding returns the first SAT
model the solver constructs, which is biased toward small integer
values and the constraint formula's lexicographic origin. Naive
blocking-clause iteration produces successive models that differ
minimally from previous ones. For PBT, this means the generator
explores a thin neighborhood of the satisfying domain rather than
covering it diversely.

**Three approaches, with honest per-mode characterization**:

1. **`dmBlockingClause`** (Phase 1 baseline): assert `¬prev_model`
   after each draw. **Guarantee**: successive draws are syntactically
   distinct (per-variable assignment equality). **Diversity**:
   structurally weak — covers a thin neighborhood. Documented as
   baseline.

2. **`dmDimensionRotation`** (Phase 1 enrichment): between draws,
   rotate which integer dimension is the *minimization target*.
   **Guarantee**: syntactic distinctness (inherited from blocking
   clauses). **Diversity**: empirical / engineering heuristic; no
   formal coverage guarantee. The test in P1.5.1 measures shape-class
   entropy as evidence, not proof.

3. **`dmSampling`** (Phase 1.5; conditional on case-study evidence):
   delegate to a sampling-based SMT backend. **Guarantee depends
   strongly on backend and theory fragment**:
   - For propositional (CNF) formulas: UniGen provides
     (1+ε)-approximate-uniform sampling with formal guarantees.
   - For quantifier-free bitvector formulas: recent samplers (CMSGen,
     SMTSampler) provide weaker formal guarantees.
   - For LIA + uninterpreted functions (the actual `modalSystem`
     output): MeGASampler and HighDiv provide *heuristic diversity
     without formal uniformity proofs*. UniGen's guarantee does not
     transfer to LIA.
   This mode must select a backend matched to the actual formula's
   theory fragment; the RFC does not promise uniform sampling for
   modal-type-system formulas.

Phase 1 ships `dmBlockingClause` + `dmDimensionRotation`. Phase 1.5
adds `dmSampling` if intonaco case study shows insufficient diversity.

## Decidability hazards

This section is new in the revision and documents the foundations
risks that must be resolved by ADR before the corresponding phases
ship.

**Transitive closure + universal quantifiers.** Encoding
`transitiveClosure` as a Z3 `define-fun-rec` and combining with a
universal quantifier (`forall n: not (n in TC(deps, n))`) puts the
formula in a fragment where:

- General TC + first-order quantification is undecidable (no finitely
  axiomatizable complete theory).
- Z3 issue **#4901** documents a confirmed case where this combination
  returns SAT with a spurious model (the model is provably inconsistent
  with the formula on further query).
- The decidable fragment for TC + quantifiers requires severe
  restrictions (e.g., the ∃∀(DTC+[E]) fragment from Immerman et al.,
  CSL 2004); the `CShape` acyclicity law as originally written falls
  outside any such decidable fragment.

**Resolution (ADR-MODAL-0006, must answer before Phase 2)**: the DSL
exposes `transitiveClosureBounded(deps, n, depth)` (a bounded-unrolling
encoding with explicit depth parameter), NOT general
`transitiveClosure`. The bound is required at the DSL level and
encoded as a finite disjunction in SMT. General TC is explicitly out
of the vocabulary.

**Quantifier instantiation.** Z3's MBQI quantifier instantiation can
be slow or incomplete on universally-quantified-heavy formulas.
Modal type systems are universally-quantified-heavy. ADR-MODAL-0005
will establish whether to ship with default Z3 behavior, with explicit
tactic-pipeline configuration, or with macro-time quantifier
elimination where possible.

**Theory fragment commitment.** The vocabulary defined above sits in
QF_LIA (quantifier-free linear integer arithmetic) plus uninterpreted
functions plus bounded quantifiers. ADR-MODAL-0006 will document the
exact decidable fragment and the completeness guarantees within it.

**Shrinking soundness under non-monotone constraints.** Choice-sequence
shrinking reduces toward zero; for formulas where "smaller in
choice-sequence" doesn't correspond to "structurally simpler model
satisfying the formula," shrinking may produce intermediate
non-satisfying candidates. **ADR-MODAL-0008 (resolved as part of this
revision) adopts re-validation per shrink step**: after each shrunk
candidate `C'` is decoded to `M'`, the formula's satisfaction is
re-checked by SMT model evaluation (not re-solve). Evaluation is
O(formula-size) — cheap relative to the original solve. Candidates
that fail re-validation are rejected and shrinking tries another step.
Sound (no non-satisfying intermediates reach the property), complete
in the choice-sequence shrinking direction, and tractable. The
alternatives (monotone-dimension-only shrinking; best-effort
Hypothesis-style) were rejected: the former sacrifices completeness
for no real benefit since re-validation is cheap; the latter
sacrifices soundness which is non-negotiable for the paper's central
claim.

## Complexity

Blocking-clause iteration has a known scalability cliff: as the number
of accumulated blocking clauses grows, each solve degrades due to unit
propagation slowdown. The exact growth rate is **formula-dependent and
not characterized by a single number** in the literature. The
"10^4 cliff" heuristic some readers may have seen is from Boolean
SAT enumeration benchmarks and does not transfer cleanly to LIA + UF.
Treat per-formula empirical measurement as required for production
scaling decisions.

For consumers where the cliff matters:
- **Solver reset with re-assertion** at periodic intervals (the
  `resetEvery: int` setting): bounds the blocking-clause store.
- **All-SAT backend**: for formulas where exhaustive enumeration is
  desired and Z3's all-SAT tactic suffices. Phase 1.5 / 2 may add this.

## Failure modes

| Failure | Cause | Default policy | Configurable |
|---|---|---|---|
| `DomainExhausted` | UNSAT under blocking clauses | raise; report as non-failure | n/a |
| `DomainTimeout` | per-solve timeout | raise | `onTimeout: skip-draw` |
| `DomainUnknown` | `unknown` (theory incompleteness, MBQI fail) | raise | `onUnknown: skip-draw` / `mark-unusable` |

Reported via `Report[T].modelFindings`.

## Phase plan

### Phase 0 — ADRs

- **ADR-MODAL-0001**: SMT vs. bounded-exhaustive DFS for model
  enumeration. *Decision*: SMT.
- **ADR-MODAL-0002**: Default diversity mode. *Decision*: ship
  `dmBlockingClause` + `dmDimensionRotation` in Phase 1; defer
  `dmSampling` to Phase 1.5.
- **ADR-MODAL-0003**: Shrinking semantics. *Decision*: shrink the
  choice-sequence encoding of the model; preserve regression DB
  compatibility.
- **ADR-MODAL-0004**: DSL surface — ASCII required, unicode accepted.
- **ADR-MODAL-0005**: Quantifier instantiation policy. *Open*; must
  resolve before Phase 2 ships.
- **ADR-MODAL-0006**: Theory fragment + `transitiveClosure` encoding.
  *Open*; must resolve before Phase 2 ships. Expected resolution:
  bounded-unrolling encoding with depth parameter.
- **ADR-MODAL-0007**: Sampling vs. exhaustive crossover, all-SAT
  backend. *Open*; informs Phase 1.5.
- **ADR-MODAL-0008**: Shrinking soundness under non-monotone
  constraints. *Resolved*: re-validation per shrink step via SMT
  model evaluation (cheap; O(formula-size)). Sound + complete in the
  shrinking direction + tractable. Alternatives rejected as documented
  in §Decidability hazards.
- **ADR-MODAL-0009**: DB key derivation for model witnesses. *Decision*:
  content-addressed key from `(formula-hash, diversity-mode, z3Version)`,
  separate from `testId` and from `symexCacheKey`.
- **ADR-MODAL-0010**: Per-run solver state lifecycle. *Decision*:
  threadvar sink analogous to `symexCapture` / `consumeSymexFindings`,
  ensuring strategy closures remain reusable across property runs.

### Phase 1 — `modelGenerator` primitive (1.5-2 weeks; 8 tests)

- **P1.1** — Single-model draw with `dmBlockingClause`.
- **P1.2** — Distinct-draw iteration over a 10-model finite domain.
- **P1.3** — `DomainExhausted` on UNSAT.
- **P1.4** — `DomainTimeout` + `skip-draw` policy.
- **P1.5** — `DomainUnknown` + `mark-strategy-unusable` policy.
- **P1.6** — Strategy composition: `.map(f)` and `.filter(p)`.
- **P1.7** — Choice-sequence regression: drawn model persists, replays.
- **P1.8** — Shrinking under ADR-MODAL-0008 semantics.

### Phase 1.5 — Diversity modes (1-1.5 weeks; 3 tests, conditional)

- **P1.5.1** — `dmDimensionRotation` shape-class entropy ≥ threshold
  vs. baseline.
- **P1.5.2** — `dmSampling` backend integration; backend-specific
  diversity claim verified per theory fragment.
- **P1.5.3** — Mode selection at strategy construction; effective at
  runtime; no state leakage.

### Phase 2 — `modalSystem` DSL (2-3 weeks; 10 tests)

Gated on ADR-MODAL-0005 + ADR-MODAL-0006 resolution.

- **P2.1** — Parse `modalSystem` block.
- **P2.2** — Compile field declarations to Z3 function-symbol
  declarations.
- **P2.3** — Compile logical predicates.
- **P2.4** — Compile equality and set-membership predicates.
- **P2.5** — Compile aggregation operators.
- **P2.6** — Compile `transitiveClosureBounded` per ADR-MODAL-0006
  bounded-unrolling encoding.
- **P2.7** — Symbolic enum constants.
- **P2.8** — Cross-modality composition.
- **P2.9** — Diagnostics for mal-formed laws.
- **P2.10** — `rawZ3:` escape hatch.

### Phase 3 — Integration & multi-role composition (1.5-2 weeks; 6 tests)

- **P3.1** — Constrained generator + `assertCoveredBy`: shared SMT
  runtime via the ADR-MODAL-0010 threadvar sink.
- **P3.2** — DB integration: model witnesses persist under
  content-addressed key per ADR-MODAL-0009.
- **P3.3** — Multi-role report: `Report[T].modelFindings` parallel
  to `symexFindings`.
- **P3.4** — Diagnostic surface: constraint-over-restricted vs.
  property-violated distinction.
- **P3.5** — Solver reset (`resetEvery`) for long property runs.
- **P3.6** — End-to-end multi-role composition.

### Phase 4 — Refinement-subtype counterexample generation (case study, 8 tests, 4-6 weeks)

*Requires Phase 2 complete (and therefore ADR-MODAL-0005 + ADR-MODAL-0006 resolved).*

The second case study earns the "generalizes beyond one type-theoretic
system" claim. The pivot from "generate inhabitants" to **"generate
counterexamples to proposed refinement-subtype relations"** is the
genuinely novel framing: given a proposed subtype
`{x | P(x)} <: {x | Q(x)}`, the generator targets models of
`P(x) ∧ ¬Q(x)` and decodes them as concrete subtype-violation
witnesses. LiquidHaskell can verify subtyping; it cannot produce these
debugging witnesses.

The fragment targeted is a small Liquid-Haskell-like refinement-type
system over base types: `{x: Int | p(x)}` with predicates in QF_LIA.
Non-linear refinement predicates are **prohibited** in this first case
study (they push out of QF_LIA into undecidable territory). Bounded
list lengths must be parameters, not free fields, to avoid the
unbounded-model hazard.

- **P4.1** — Introduce sibling `refinementSystem` macro (NOT a reuse
  of `modalSystem`). Both macros compile to the same SMT backend
  through a shared, theory-agnostic compilation pipeline; the DSLs are
  theory-specific (modal vs. refinement). This dual structure makes the
  framework thesis explicit: the engine generalizes across type-theoretic
  constraint domains.
- **P4.2** — Predicate compilation for subtype-counterexample targets:
  `Pos = {x: Int | x > 0}`, `SortedList[T]`, etc. Predicates must be
  linear (QF_LIA); non-linear predicates are rejected at macro-expansion
  time.
- **P4.3** — Decoder for refinement-typed subtype-violation witnesses.
- **P4.4** — Generator pipeline end-to-end: given `{x | P} <: {x | Q}`,
  enumerate concrete models of `P(x) ∧ ¬Q(x)`.
- **P4.5** — Hit-rate comparison vs. rejection sampling at multiple
  sizes; data feeds H1 evaluation.
- **P4.6** — Composition with `assertCoveredBy` for the refinement
  predicate's coverage analysis.
- **P4.7** — Documentation of vocabulary delta between `modalSystem`
  and `refinementSystem`.
- **P4.8** — Lessons-learned report: which DSL primitives carried over
  unchanged; which needed theory-specific extension; what the
  framework gained from being tested against a second case.

## Phase 5a — Mechanized soundness proof (REQUIRED, 6-8 weeks)

**Precondition:** ADR-MODAL-0005 (theory fragment lock) and ADR-MODAL-0006 (bounded-TC encoding) must be closed. The Lean formalization target is the decidable theory fragment documented there, not "QF_LIA + UF" generically.

**Deliverable:** `nelli/proofs/consistency/` directory containing Lean 4 source (mathlib-free, sorry-free, matching the posture of intonaco/proofs/Consistency.lean), a `lakefile.lean` build manifest, and a `theorem-map.md` linking each Lean theorem to its paper-claim. CI step: `lake build` added to nelli's test matrix.

### Theorem table (6 theorems total; 4 in Phase 5a, 2 in Phase 5b)

| # | Theorem | Statement | Phase |
|---|---------|-----------|-------|
| T1 | `compileSoundness` | ∀ well-formed `S`, ∀ Z3 model `m` of `compile(S)`: `decode(m)` satisfies every law in `S`. | 5a |
| T2 | `decoderTotality` | ∀ well-formed `S`, ∀ Z3 model `m` of `compile(S)`: `decode(m)` is defined (decoder is total over the constrained domain). | 5a |
| T3 | `transitiveClosureBoundedCorrect` | `transitiveClosureBounded(deps, n, k)` holds in any Z3 model iff there is a `deps`-path of length ≤ k from `n` to itself (semantics-preserving encoding per ADR-MODAL-0006). | 5a |
| T4 | `heightCompositionPreserved` | The `height composition` law compiles to an SMT constraint whose models exactly satisfy `height(n) = 1 + maxOver(deps(n), height)` — equality, not over-approximation. | 5a |
| T5 | `compileCompleteness` | ∀ well-formed `S`, ∀ source value `g` satisfying every law in `S`: ∃ Z3 model `m` of `compile(S)` with `decode(m) = g`. | 5b |
| T6 | `refinementExtensionSound` | The same `compile` framework, instantiated for the QF_LIA refinement-subtype fragment from Phase 4, satisfies `compileSoundness` (T1 analogue) for that fragment. | 5b |

### Work items (5a)

- **P5a.1 — Source language in Lean.** Inductive Lean type family for `SourceLaws` (CShape modal fragment): `Node`, `tier ∈ {Static, Dynamic}`, `height : Node → Nat`, `deps : Node → Finset Node`, law-form ASTs. Approx 2-4 weeks for one Lean-literate engineer (the harder direction of the proof; gates everything else).
- **P5a.2 — Target SMT theory in Lean.** Formalize the decidable target fragment per ADR-MODAL-0005/0006 as a Lean structure with model-evaluation semantics.
- **P5a.3 — `compile` function in Lean.** Define `compile : SourceLaws → SMTFormula` as a total Lean function. This is the OBJECT of the proof; subsequent theorems are about THIS function, not about the Nim macro.
- **P5a.4 — Prove T1, T2, T3, T4.** Soundness, decoder totality, TC encoding correctness, height-composition exactness.
- **P5a.5 — Differential bridge (Cedar pattern).** Generate test cases by: (a) running `modalSystem` on a set of hand-written source blocks, (b) running the Lean `compile` on their Lean-formalized equivalents, (c) asserting Z3-model membership matches both ways. This is NOT a proof of Nim-macro-vs-Lean-`compile` equivalence — it is the differential testing harness that makes the trust gap empirically auditable.

## Phase 5b — Completeness + refinement extension (STRETCH, 8-12 weeks)

Promotes the artifact from "soundness only" to the full H2 claim. Likely a journal-extension scope item rather than initial-submission scope.

- **P5b.1 — Prove T5 (compileCompleteness).** The harder direction: characterize the image of `decode` over all Z3 models of `compile(S)` and show it equals the set of source-law satisfiers. Requires injectivity of `compile` on equivalence-classes of source laws.
- **P5b.2 — Prove T6 (refinementExtensionSound).** Instantiate the framework for the refinement-subtype fragment and re-prove T1 for that instance.

## Proof trust chain (explicit TCB)

The mechanized proof rests on five unverified assumptions, made explicit here (Cedar pattern):

1. **Z3 soundness on the target fragment.** Every Z3 model of a formula in QF_LIA + bounded-TC actually satisfies the formula. Empirically well-established; not formally proved (Z3 issue #4901 is the historical example of why this matters; we are out of scope for it per ADR-MODAL-0006).
2. **Lean kernel soundness.** Standard.
3. **Nim-macro faithfulness.** The Nim `modalSystem` / `refinementSystem` macros implement the same function as the Lean `compile` definition. Bridged only by differential testing (P5a.5), not proved.
4. **Decoder totality for non-standard decoders.** T2 proves totality for the decoder used in the case studies. User-supplied decoders (third parties using `modelGenerator`) remain a caller obligation per the `modelGenerator` docstring.
5. **Arithmetic consistency.** Lean's `Int` and Nim's integer arithmetic agree on the values in scope (no overflow). Relevant for the refinement-types case study.

### Phase 6 — Documentation (~1 week)

- **P6.1** — `docs/modal/tutorial.md`.
- **P6.2** — `examples/modal_cshape.nim`.
- **P6.3** — `docs/modal/extending.md`.
- **P6.4** — `docs/modal/diversity.md`.
- **P6.5** — `docs/modal/refinement-types.md` — Phase 4 walkthrough.
- **P6.6** — `docs/modal/soundness-proof.md` — pointer to Phase 5
  artifacts + informal exposition.

## Test budget summary

| Phase | Tests | Cumulative |
|---|---|---|
| 0   | 0 (ADRs) | 0 |
| 1   | 8  | 8  |
| 1.5 | 3  | 11 |
| 2   | 10 | 21 |
| 3   | 6  | 27 |
| 4   | 8  | 35 |
| 6   | 5 docs deliverables | — (docs, not counted) |

Phase 5a/5b are measured in theorems-proven, not tests (T1-T4 for 5a,
T5-T6 for 5b). Phase 5 (mechanized proof) targets 6 mechanized theorems
total (the proof artifact for the paper).

## Decision log

- **2026-06-02** (first draft) — Plan drafted.
- **2026-06-02** (revision after multi-agent adversarial review) —
  Substantial revision: citations corrected (Korat ISSTA not OOPSLA;
  Crowbar is coverage-guided fuzzing not symex; Bahr 2017 is guarded
  recursion not S4 modality; QuickChick author ordering and POPL 2018
  paper). Added Luck (POPL 2017) as primary precursor for the DSL,
  Pex/IntelliTest (TAP 2008) and KLEE (OSDI 2008) for SMT
  test-generation tradition, MeGASampler/HighDiv for LIA sampling.
  Demoted diversity from headline guarantee to per-mode characterization.
  Added explicit research question + supporting hypotheses. Added
  §Decidability hazards section addressing transitive-closure +
  quantifier soundness issue (Z3 #4901). API surface corrected:
  `ModelFormula = proc(solver: Z3Solver)` (not `SMTFormula`);
  `ModelDecoder = proc(w: RawWitness): T` matching existing extraction;
  `Report[T].modelFindings` parallel to `symexFindings` (not extending
  the sealed type); DB key content-addressed (not `testId`-tagged);
  per-run solver state via threadvar sink. Phase 7 status corrected
  (loadSymexWitnesses shipped, only withSymexSeeds deferred). Added
  ADR-MODAL-0005 through 0010.
- **2026-06-02** (second pass on review-surfaced opinion items, applied
  with PhD-CS lens) — Reframed venue target to **ICFP as primary**,
  not ISSTA. Rationale: the "modal types + SMT + verified compilation
  correctness" combination is naturally ICFP-shaped; ISSTA targeting
  would be settling. Required additions for the venue: (a) a second
  case study (refinement types) — added as Phase 4; (b) a mechanized
  compilation soundness proof — added as Phase 5. **ADR-MODAL-0008
  resolved** with re-validation per shrink step (cheap O(formula-size)
  via SMT model evaluation; ADR no longer blocks Phase 1). H1 baseline
  numerical target dropped (kept qualitative). H2 promoted from stretch
  goal to required central theorem. H4 added (generality across
  type-theoretic systems). One-paper framing affirmed (engine + DSL
  contribute together; splitting weakens both). Total effort revised
  to 14-20 weeks. Cave & Pientka venue corrected (LFMTP 2013, not
  PPDP 2013). HighDiv full citation added (Lai, Li, Luo, arXiv
  2503.04782 / Springer LNCS).
- **2026-06-02 — Round 2 review pass (4 agents: mechanized proof feasibility, ICFP novelty, case-study generality, coherence + API drift).** Reframe per user direction "this is a prestige/portfolio project, publication aspirational." Phase 5 split into 5a (soundness, required, 6-8wks) and 5b (completeness + RT extension, stretch, 8-12wks). Phase 4 pivots to subtype-counterexample generation; `refinementSystem` introduced as sibling macro to `modalSystem`. "Bijection" claim in H2 replaced with explicit soundness + completeness statement (decoder as witnessing map). S4 framing renamed to "Davies' λ□ / two-tier modal calculus" — CShape has □-introduction but no ◇, full S4 axiomatic system out of scope. Third case study (information flow types) explicitly declined per user; listed as future work. Six mechanized theorems enumerated as a table (T1-T6). Cedar-style differential testing bridge added (P5a.5). Proof trust chain section added (5 unstated axioms now explicit). Citations added: SmartCheck (Pike HASKELL 2014), Targeted PBT (Löscher & Sagonas ISSTA 2017), Davies λ□ (LICS 1996), Vazou+ LH (ICFP 2014). Evaluation baselines extended: Luck + Targeted PBT in addition to rejection sampling. Eight coherence fixes (RawWitness export prereq, stale ADR-0008 comment, test-budget table rows, H3 conditionality, Phase 4 ADR gate, effort caveat, venue framing, Phase 5 effort line). Cross-RFC: intonaco M-ζ S2.4 corollary restricted to modal-tier walker fragment; nelli's T1+T2 are the upstream theorems instantiated (not T5, which covers the completeness direction intonaco proves independently).

## Future Work

Information flow types as a third case study — security labels form a finitary lattice that fits the framework's compilation backend cleanly; complement-generation could produce policy-violating witnesses. Deferred; 1-2 weeks scope when revisited.

## Downstream consumers

- **intonaco M-ζ Stage 2** (`~/projects/intonaco/docs/rfc-modal-verification-pipeline.md`)
  — first consumer. CShape modal-system declaration + BindingGraph
  decoder live in intonaco; engine work lives here.
