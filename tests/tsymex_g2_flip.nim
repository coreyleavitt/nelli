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

  test "an intentionally tiny z3TimeoutMs forces cfoTimedOut, not a hang or a wrong answer":
    # Same SUT/trace as the control above — ONLY `z3TimeoutMs` changes, from
    # the 2000ms default down to 1ms. `z3CheckBounded`'s Z3 "timeout" param
    # is deterministic-in-practice (not `queryRLimit`-deterministic, but a
    # documented, intentional design choice for G2 — see
    # `defaultConcreteBranchRLimit`'s doc comment in `smt/runtime.nim`: a
    # flip candidate is always re-verified concretely downstream, so this
    # module doesn't need rlimit's cross-machine step-count determinism the
    # way `concreteBranchOutcome` does). At 1ms, every attempt (the exact
    # query AND every optimistic relaxation) exhausts before deciding —
    # `zsUnknown`, never a wrong SAT/UNSAT — so the outcome can only ever
    # fall through to `cfoTimedOut`: never a hang (this test itself is
    # bounded by `dt-bounded.sh` regardless, but the actual runtime here is
    # milliseconds), never a crash, and never silently treated as `cfoUnsat`
    # (which WOULD be wrong: the control test just proved a model exists).
    let trace = @[integerChoice(2, -1000, 1000, 0), integerChoice(3, -1000, 1000, 0),
                  integerChoice(5, -1000, 1000, 0), integerChoice(7, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 2),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 3)]
    let r = concolicFlip(concolicTimeoutGate, trace, bindings, 0, z3TimeoutMs = 1'u)
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
                                z3TimeoutMs = 1'u)
    check timedOut.outcome == cfoTimedOut

    let magicTrace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let magicBindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let followUp = concolicFlip(magicByteGate, magicTrace, magicBindings, 0)
    check followUp.outcome == cfoSolvedExact
    check followUp.coverage == ccoIntendedCovered
    check $followUp.materialized[0] == "int(3405691582)"   # 0xCAFEBABE
