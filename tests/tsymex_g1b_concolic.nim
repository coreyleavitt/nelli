## RFC-fuzzer-nextgen G1b — draw-symbolication + concrete-trace constraint
## collection (concolic mechanism steps 2-3 ONLY; no branch-flipping, that's
## G2).
##
## Design confirmed before implementing (see the module-section comment
## above `runConcolicCollectImpl` in `smt/runtime.nim`):
##   (a) a recorded `seq[ChoiceNode]` maps cleanly onto the walker's existing
##       symbolic-var machinery — each node already carries its own concrete
##       value AND declared constraint, so "fresh symbolic var + declared
##       constraint" is `mkIntVar`/`mkBoolVar` + the same range-constraint
##       idiom `runSymexImpl` already uses for params.
##   (b) `Strategy.run` is a genuinely opaque runtime closure (confirmed —
##       `strategy.nim` has no retrievable AST); the walker's only door stays
##       `fn: typed`. So this mechanism does not "walk the strategy" — the
##       caller (`bindings`) says which property parameters are direct draws
##       (kept symbolic) vs. behind a combinator (concretized to the
##       observed value). No escalation needed — the RFC's own text names
##       this same resolution ("anything the walker cannot model is
##       concretized to its observed value").
##   (c) `wmFollowConcrete` fits the G1a arm-dispatch seam exactly:
##       `walkIfFollowConcrete` reuses `lowerBoolInExpr`/`forkPath` and picks
##       the one concretely-taken arm via a scratch-solver check against the
##       recorded draw values (`concreteEq`), never asserted onto the live
##       path.
import std/unittest
import nelli/symex

# ---- fixtures ---------------------------------------------------------------

proc concolicIfGate(x: int) =
  ## The RFC's own worked example: `if drawnInt > 5` over `integers(0, 10)`.
  if x > 5:
    symexTarget("g1b_hi")
  else:
    symexTarget("g1b_lo")

suite "RFC-fuzzer-nextgen G1b — concolic draw-symbolication + collection":

  test "soundness pin: collected constraints are satisfied by the original concrete draw (true arm)":
    # integers(0, 10) drew 7 -> x > 5 is concretely true.
    let trace = @[integerChoice(7, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(concolicIfGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.drawsSymbolicated == 1
    check r.counters.paramsConcretized == 0
    check r.counters.ambiguousBranches == 0
    check r.counters.tracesTruncated == 0

  test "soundness pin: collected constraints are satisfied by the original concrete draw (false arm)":
    # integers(0, 10) drew 2 -> x > 5 is concretely false; the ELSE arm's
    # negated predicate must be the one collected.
    let trace = @[integerChoice(2, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(concolicIfGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.drawsSymbolicated == 1

  test "soundness pin: boundary draw (x == 5, false arm)":
    let trace = @[integerChoice(5, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(concolicIfGate, trace, bindings)
    check r.pcSatByConcreteInputs

  test "combinator/closure boundary: an opaque-strategy binding concretizes without crashing":
    # Stands in for e.g. `integers(0, 10).map(v => v * 2)`: the recorded
    # draw is still one ckInteger node, but the PARAMETER value (14) is the
    # observed post-map value, not the draw itself — the draw/branch link is
    # severed at the combinator (RFC §G-concolic), so G1b concretizes rather
    # than guessing at the transform.
    let trace = @[integerChoice(7, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbConcretized, concreteInt: 14)]
    let r = concolicCollect(concolicIfGate, trace, bindings)
    check r.counters.paramsConcretized == 1
    check r.counters.drawsSymbolicated == 1  ## the draw itself is still
                                              ## symbolicated (it's the
                                              ## PARAMETER binding, not the
                                              ## draw, that's concretized
    check r.pcSatByConcreteInputs  ## trivially true: the env is a ground
                                    ## literal, so the collected pc has no
                                    ## free variable left to fail SAT on

  test "bounded trace length: truncates gracefully past the cap and is counted, not silently dropped":
    var trace: seq[ChoiceNode]
    for i in 0 ..< 5:
      trace.add integerChoice(i, 0, 10, 0)
    # drawIndex 4 falls past a cap of 3 -> falls back to concretizing that
    # draw's own recorded value (4) rather than crashing or hanging.
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 4)]
    let r = concolicCollect(concolicIfGate, trace, bindings, maxDraws = 3)
    check r.counters.tracesTruncated == 1
    check r.counters.drawsSymbolicated == 3
    check r.counters.paramsConcretized == 1
    check r.pcSatByConcreteInputs

  test "unsupported draw kind (float) degrades to concretization without crashing":
    let trace = @[floatChoice(3.5, 0.0, 10.0, false, 0.0)]
    # No itFloat-typed property param in this fixture; exercise the
    # unsupported-kind counter directly via a param concretized past a
    # draw index the symbolicator declined to turn into a Z3 var.
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(concolicIfGate, trace, bindings)
    check r.counters.unsupportedDrawKinds == 1
    check r.counters.paramsConcretized == 1   ## itInt param, ckFloat draw:
                                               ## kind mismatch -> concretize
    check r.pcSatByConcreteInputs
