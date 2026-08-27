## RFC-fuzzer-nextgen G2 — branch-flip solve + choice-sequence materialization
## + bounded optimistic fallback + typed yield metric (RFC §G-concolic steps
## 4-5, built entirely on G1b's `runConcolicCollectImpl`/`branchTrace`).
##
## Design (see the module-section comment above `runConcolicFlipImpl` in
## `smt/runtime.nim`):
##   - formula = (prefix constraints up to the target decision) AND (negated
##     observed-truth predicate at that decision); Z3 is asked for a model.
##   - UNSAT/timeout falls back to a BOUNDED optimistic relaxation: drop
##     prefix conjuncts in reverse-collection order (deterministic, linear —
##     never a 2^n subset search), one more per attempt, up to
##     `maxRelaxationAttempts`, each bounded by the same per-attempt Z3
##     timeout — guaranteeing termination regardless of formula shape.
##   - A SAT model materializes into a `seq[ChoiceNode]` by reading each
##     symbolicated draw's solved value and CLAMPING it into that draw's own
##     declared `[min, max]` before reconstructing via `integerChoice`/
##     `booleanChoice` — structurally valid by construction. The clamp is
##     also why an optimistic solve does not always cover the intended edge
##     (dropping a draw's own bound can let the model pick a value the clamp
##     then pulls back) — the intended-vs-unrelated coverage split exists
##     precisely to surface that.
import std/unittest
import nelli/symex

# R26: `settings.budget.queryRLimit` forces Z3's bounded-solve path (both
# `concreteBranchOutcome`'s G1b collection-time scratch solves, per R7, AND
# `z3CheckBounded`'s G2 flip-solve queries) to exhaust by LOGICAL STEP COUNT
# rather than wall-clock time — deterministic across machines and load for a
# fixed Z3 build, unlike `z3TimeoutMs`, whose firing time is exactly what let
# the earlier version of this test pass on Linux and fail on the
# `symex-windows` CI leg's different libz3 build.
#
# `queryRLimit` is a SINGLE shared setting, not a G2-specific knob — it also
# governs the G1b collection pass this SUT must get through before the flip
# formula is even attempted. A value tiny enough to guarantee the flip
# formula fails would ALSO starve collection's own (much cheaper, but not
# free) concrete-pinned branch checks, degrading to `cfoUnmodelable` before
# the flip is ever attempted (confirmed empirically while building this fix:
# values as large as several hundred still left collection unable to resolve
# `concolicTimeoutGate`'s single decision). So this reuses
# `defaultConcreteBranchRLimit` (`smt/runtime.nim`) verbatim: the SAME ceiling
# R7 already validated is generous enough for ordinary concrete-pinned
# collection checks (its own doc: "far simpler by construction... should
# resolve in a tiny fraction of that budget") while still being a genuine,
# finite bound — and empirically (see the paired `maxRelaxationAttempts = 0`
# note below) it is nowhere near enough for Z3 to decide the deliberately
# hard nonlinear query this SUT was built to stress. Reusing the proven
# constant, rather than picking a fresh magnitude, means its behavior on
# ordinary collection queries is already known-good, exactly the same
# argument `defaultConcreteBranchRLimit`'s own doc comment makes.
#
# `withSymexSettings` starts from `defaultSymexSettings()` so every OTHER
# setting (arith checks, inline policy, etc.) stays at its normal default;
# only the rlimit changes.
const flipRLimitSettings = withSymexSettings() do (s: var SymexSettings):
  s.budget.queryRLimit = defaultConcreteBranchRLimit

# ---- fixtures ---------------------------------------------------------------

proc magicByteGate(drawnInt: int) =
  ## The RFC's own headline example: mutation would need up to 2^32 tries to
  ## land exactly on 0xCAFEBABE; concolic flip-solve gets there in one Z3
  ## query over an unconstrained-ish wide `integers` draw.
  if drawnInt == 0xCAFEBABE:
    symexTarget("magic_hit")
  else:
    symexTarget("magic_miss")

proc coupledDisjointGate(y, z: int) =
  ## `y`/`z` are drawn from DISJOINT domains ([0,100] and [200,210]) — the
  ## exact flip formula (`y == z` under both domains) is UNSAT by
  ## construction; only relaxing (dropping) one side's domain bound admits a
  ## model. Constructed to exercise the optimistic path deliberately.
  if y == z:
    symexTarget("coupled_hit")
  else:
    symexTarget("coupled_miss")

proc concolicTimeoutGate(a, b, c, d: int) =
  ## R26: mirrors `tsymex_g1b_concolic.nim`'s R7 `concolicMultGate` — the
  ## same four-variable BV multiplication shape `tsymex_phase13_rlimit.nim`
  ## established burns far more work than a trivial budget. Reused here to
  ## force the FLIP formula itself (not `concreteBranchOutcome`'s scratch
  ## solves during collection) to exhaust its bound: 1234567 = 127 * 9721,
  ## and 9721 exceeds every draw's own [-1000, 1000] domain, so the EXACT
  ## flip query (find a,b,c,d in-domain with a*b*c*d == 1234567) is
  ## genuinely UNSAT — but proving that for a nonlinear BV product over 4
  ## wide domains is expensive for Z3, unlike `concreteBranchOutcome`'s
  ## ground-pinned check (concrete values substituted, trivial to
  ## evaluate). A generous timeout lets Z3 grind through it via the
  ## optimistic relaxation fallback (dropping a domain bound admits
  ## 1*1*127*9721); an intentionally tiny one does not.
  if a * b * c * d == 1234567:
    symexTarget("rare")

proc pathologicalGate(f: int) =
  ## `f` is drawn from the single-value domain [7, 7] — `f == 999999` is
  ## unsatisfiable no matter what else is dropped. Two extra WIDE padding
  ## draws are recorded in the trace (unbound to any property parameter) so
  ## the target decision's prefix has conjuncts an optimistic attempt CAN
  ## drop without ever reaching `f`'s own (load-bearing) bound.
  if f == 999999:
    symexTarget("hit")
  else:
    symexTarget("miss")

suite "RFC-fuzzer-nextgen G2 — concolic branch-flip solve + materialization":

  test "magic-byte gate: exact flip-solve passes 0xCAFEBABE in one invocation":
    let trace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(magicByteGate, trace, bindings, 0)
    check r.outcome == cfoSolvedExact
    check r.flipCounters.relaxationAttemptsUsed == 0
    check r.materialized.len == 1
    check $r.materialized[0] == "int(3405691582)"   # 0xCAFEBABE
    check r.coverage == ccoIntendedCovered
    check r.flipCounters.byOutcome[cfoSolvedExact] == 1
    check r.flipCounters.byCoverage[ccoIntendedCovered] == 1

  test "unmodelable: an out-of-range target branch index is reported, not crashed":
    let trace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(magicByteGate, trace, bindings, 5)
    check r.outcome == cfoUnmodelable
    check r.coverage == ccoNotApplicable
    check r.materialized.len == 0
    check r.flipCounters.byOutcome[cfoUnmodelable] == 1

  test "optimistic path: an exact-unsat/disjoint-domain case is solved by relaxation":
    let trace = @[integerChoice(5, 0, 100, 0), integerChoice(203, 200, 210, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicFlip(coupledDisjointGate, trace, bindings, 0)
    check r.outcome == cfoSolvedOptimistic
    check r.flipCounters.relaxationAttemptsUsed > 0
    check r.materialized.len == 2
    check r.flipCounters.byOutcome[cfoSolvedOptimistic] == 1
    # The winning relaxation dropped z's OWN domain bound — materialization
    # clamps the solved z back into its original [200, 210], which silently
    # undoes the flip on replay: solved, but not the intended edge.
    check r.coverage == ccoUnrelatedCoverage
    check r.flipCounters.byCoverage[ccoUnrelatedCoverage] == 1

  test "pathological fully-unsolvable case terminates within the relaxation bound":
    var trace = @[integerChoice(7, 7, 7, 0)]
    for i in 0 ..< 2:
      trace.add integerChoice(500, 0, 1000, 0)
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(pathologicalGate, trace, bindings, 0,
                         maxRelaxationAttempts = 4)
    check r.outcome == cfoUnsat
    check r.coverage == ccoNotApplicable
    check r.materialized.len == 0
    # Exactly the configured bound ran (6 droppable conjuncts exist but the
    # bound is 4) — proves the CAP terminated the search, not exhaustion.
    check r.flipCounters.relaxationAttemptsUsed == 4
    check r.flipCounters.byOutcome[cfoUnsat] == 1

  test "yield metric: intended-vs-unrelated coverage split is populated across outcomes":
    let magicTrace = @[integerChoice(1, 0, 0xFFFFFFFF, 0)]
    let magicBindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let hit = concolicFlip(magicByteGate, magicTrace, magicBindings, 0)
    check hit.coverage == ccoIntendedCovered

    let coupledTrace = @[integerChoice(9, 0, 100, 0), integerChoice(207, 200, 210, 0)]
    let coupledBindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                            ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let unrelated = concolicFlip(coupledDisjointGate, coupledTrace, coupledBindings, 0)
    check unrelated.coverage == ccoUnrelatedCoverage

    # Both taxonomy values are genuinely distinguished — a metric that
    # collapsed them would fail one of the two checks above.
    check hit.flipCounters.byCoverage[ccoIntendedCovered] == 1
    check hit.flipCounters.byCoverage[ccoUnrelatedCoverage] == 0
    check unrelated.flipCounters.byCoverage[ccoUnrelatedCoverage] == 1
    check unrelated.flipCounters.byCoverage[ccoIntendedCovered] == 0

suite "R26 — cfoTimedOut: Z3 'unknown' degrades the bridge gracefully":

  test "control: the SAME SUT/trace solves normally under a generous timeout":
    # Establishes the contrast that makes the next test meaningful: this is
    # NOT an unconditionally-unsolvable formula reported as timed-out by
    # some other bug — under `defaultZ3TimeoutMs` (2000ms) Z3 has time to
    # grind through the optimistic relaxation fallback and solve it
    # (dropping one domain bound admits 1*1*127*9721 == 1234567).
    let trace = @[integerChoice(2, -1000, 1000, 0), integerChoice(3, -1000, 1000, 0),
                  integerChoice(5, -1000, 1000, 0), integerChoice(7, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 2),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 3)]
    let r = concolicFlip(concolicTimeoutGate, trace, bindings, 0)
    check r.outcome in {cfoSolvedExact, cfoSolvedOptimistic}

  test "an exhausted queryRLimit forces cfoTimedOut on the exact query, not a hang or a wrong answer":
    # Same SUT/trace as the control above — two changes, both away from
    # wall-clock and onto the deterministic rlimit instrument:
    #
    # 1. `settings = flipRLimitSettings` bounds every Z3 check in this call by
    #    LOGICAL STEP COUNT (`defaultConcreteBranchRLimit`, see its comment
    #    above) instead of the default "unbounded" (`queryRLimit = 0`).
    #    Whether that ceiling exhausts before a decision is a property of the
    #    formula and the Z3 BUILD, never of the machine running it — unlike
    #    `z3TimeoutMs`, whose firing time is exactly what let this test pass
    #    on Linux and fail on the `symex-windows` CI leg's different libz3
    #    build.
    # 2. `maxRelaxationAttempts = 0` disables the optimistic-relaxation
    #    fallback entirely, leaving only the EXACT query (prefix AND negated
    #    target, no dropped conjuncts). This matters because the relaxed
    #    formula is a genuinely EASIER sub-problem, not just a faster wall-clock
    #    race: the control test's own comment notes dropping one domain bound
    #    admits the small witness `1*1*127*9721` — well within
    #    `defaultConcreteBranchRLimit`'s budget, so leaving relaxation enabled
    #    would let Z3 solve the query instead of exhausting on it, the same
    #    way it does in the control test. The EXACT query has no such shortcut:
    #    it must prove no in-domain (a,b,c,d) satisfies the multiplication at
    #    all, over the full bounded search space — genuinely hard nonlinear
    #    reasoning, not resolvable within this budget (confirmed empirically:
    #    it stays `zsUnknown`, never reaches `zsUnsat`, at this ceiling).
    #
    # So the only Z3 check this call makes returns `zsUnknown` — never a wrong
    # SAT/UNSAT — and the outcome can only ever fall through to `cfoTimedOut`:
    # never a hang (this test itself is also bounded by `dt-bounded.sh`
    # regardless), never a crash, and never silently treated as `cfoUnsat`
    # (which WOULD be wrong: the control test just proved a model exists once
    # relaxation is allowed to run).
    let trace = @[integerChoice(2, -1000, 1000, 0), integerChoice(3, -1000, 1000, 0),
                  integerChoice(5, -1000, 1000, 0), integerChoice(7, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 2),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 3)]
    let r = concolicFlip(concolicTimeoutGate, trace, bindings, 0, settings = flipRLimitSettings,
                         maxRelaxationAttempts = 0)
    check r.outcome == cfoTimedOut
    check r.coverage == ccoNotApplicable
    check r.materialized.len == 0
    check r.flipCounters.byOutcome[cfoTimedOut] == 1

  test "the campaign continues: the bridge is fully usable again right after a timeout":
    # Degrading to `cfoTimedOut` must not leave any lingering Z3/WalkCtx
    # state that corrupts the NEXT call — the fuzz loop falls back to
    # ordinary mutation and keeps calling the bridge on other candidates.
    let timeoutTrace = @[integerChoice(2, -1000, 1000, 0), integerChoice(3, -1000, 1000, 0),
                         integerChoice(5, -1000, 1000, 0), integerChoice(7, -1000, 1000, 0)]
    let timeoutBindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                            ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1),
                            ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 2),
                            ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 3)]
    let timedOut = concolicFlip(concolicTimeoutGate, timeoutTrace, timeoutBindings, 0,
                                settings = flipRLimitSettings, maxRelaxationAttempts = 0)
    check timedOut.outcome == cfoTimedOut

    let magicTrace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let magicBindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let followUp = concolicFlip(magicByteGate, magicTrace, magicBindings, 0)
    check followUp.outcome == cfoSolvedExact
    check followUp.coverage == ccoIntendedCovered
    check $followUp.materialized[0] == "int(3405691582)"   # 0xCAFEBABE
