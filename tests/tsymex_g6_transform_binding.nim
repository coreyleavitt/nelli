## RFC-fuzzer-nextgen G6 C2 — `cbTransformLinked` runtime binding: the
## affine value (`tA*draw + tB`) plus optional extra Z3 conjuncts, the
## Z3-facing flattened twin of `smt/transparency.nim`'s composed
## `TransparencyDescriptor`. Exercises the RUNTIME mechanism directly (hand-
## built bindings, mirroring `tsymex_g2_flip.nim`'s style) — decoupled from
## `fuzzmacro.nim`'s AST classifier, which is wired in a later cycle.
import std/unittest
import nelli/symex

proc affineMapGate(mapped: int) =
  ## The RFC's own headline shape: `integers(0,1000).map(x => x*2 + 1)`
  ## then `if mapped == 501`. `mapped` is never itself a draw — it is
  ## `2*draw + 1` — so a plain `cbDrawLinked` binding could never solve
  ## this (it would bind `mapped` directly to the draw var, an unsatisfiable
  ## shape); `cbTransformLinked` is what makes the INVERSE (`draw =
  ## (501-1)/2 = 250`) reachable.
  if mapped == 501:
    symexTarget("hit")
  else:
    symexTarget("miss")

proc filteredGate50(x: int) =
  if x == 50:
    symexTarget("hit")
  else:
    symexTarget("miss")

proc filteredGate500(x: int) =
  if x == 500:
    symexTarget("hit")
  else:
    symexTarget("miss")

suite "RFC-fuzzer-nextgen G6 — cbTransformLinked (affine + conjuncts) runtime binding":

  test "affine binding lets concolic invert through map(x*2+1) — the headline gate":
    let trace = @[integerChoice(7, 0, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: 0, tA: 2, tB: 1)]
    let r = concolicFlip(affineMapGate, trace, bindings, 0)
    check r.outcome == cfoSolvedExact
    check r.flipCounters.relaxationAttemptsUsed == 0
    check r.materialized.len == 1
    check $r.materialized[0] == "int(250)"   # (501 - 1) / 2
    check r.coverage == ccoIntendedCovered

  test "identity via tA=1,tB=0 reproduces plain cbDrawLinked behavior":
    let trace = @[integerChoice(7, 0, 0xFFFFFFFF, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: 0, tA: 1, tB: 0)]
    proc magicGate(v: int) =
      if v == 0xCAFEBABE: symexTarget("hit") else: symexTarget("miss")
    let r = concolicFlip(magicGate, trace, bindings, 0)
    check r.outcome == cfoSolvedExact
    check $r.materialized[0] == "int(3405691582)"
    check r.coverage == ccoIntendedCovered

  test "extra conjunct constrains the EXACT flip attempt (filter respected, not violated)":
    # x == 50 contradicts the conjunct (x > 100) — an exact-only attempt
    # (no relaxation) must come back UNSAT, never silently violate the
    # filter it represents.
    let trace = @[integerChoice(150, 0, 1000, 0)]
    let bindings = @[ConcolicParamBinding(
      kind: cbTransformLinked, tDrawIndex: 0, tA: 1, tB: 0,
      tConjuncts: @[ConcolicConjunct(drawIndex: 0, a: 1, b: 0, op: ccoGt, lit: 100)])]
    let r = concolicFlip(filteredGate50, trace, bindings, 0, maxRelaxationAttempts = 0)
    check r.outcome == cfoUnsat
    check r.coverage == ccoNotApplicable
    check r.materialized.len == 0

  test "exact flip still solves when the target is consistent with the conjunct":
    let trace = @[integerChoice(150, 0, 1000, 0)]
    let bindings = @[ConcolicParamBinding(
      kind: cbTransformLinked, tDrawIndex: 0, tA: 1, tB: 0,
      tConjuncts: @[ConcolicConjunct(drawIndex: 0, a: 1, b: 0, op: ccoGt, lit: 100)])]
    let r = concolicFlip(filteredGate500, trace, bindings, 0, maxRelaxationAttempts = 0)
    check r.outcome == cfoSolvedExact
    check $r.materialized[0] == "int(500)"
    check r.coverage == ccoIntendedCovered

  test "out-of-range tDrawIndex degrades to concretized, not a crash":
    let trace = @[integerChoice(7, 0, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: 5, tA: 2, tB: 1)]
    let r = concolicCollect(affineMapGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.paramsConcretized == 1

  test "soundness pin holds with a satisfied conjunct present":
    let trace = @[integerChoice(150, 0, 1000, 0)]
    let bindings = @[ConcolicParamBinding(
      kind: cbTransformLinked, tDrawIndex: 0, tA: 1, tB: 0,
      tConjuncts: @[ConcolicConjunct(drawIndex: 0, a: 1, b: 0, op: ccoGt, lit: 100)])]
    let r = concolicCollect(filteredGate50, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.paramsConcretized == 0
