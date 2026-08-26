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
