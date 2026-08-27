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

proc whileThenIfGate(n: int) =
  ## R14: a `while` loop whose trip count is driven by a symbolic draw,
  ## followed by exactly one `if`. `walkWhileFollowConcrete` must follow
  ## ONLY the concretely-taken iteration count — no hypothetical exits at
  ## earlier iterations, no hypothetical extra iterations past the real
  ## one. Pre-fix, `wmExplore`'s fork-both-ways k-unroll ran regardless of
  ## `w.mode`, producing one bogus surviving path per unrolled iteration;
  ## the trailing `if` then recorded one `branchTrace` entry PER bogus
  ## survivor instead of the single real decision.
  var i = 0
  while i < n:
    i = i + 1
  if i > 100:
    symexTarget("big")
  else:
    symexTarget("small")

proc concolicMultGate(a, b, c, d: int) =
  ## R7: mirrors `tsymex_phase13_rlimit.nim`'s `multConstraint` — a
  ## four-variable BV multiplication comparison Z3 resolves easily at
  ## default settings but which reliably burns well past a 1-step rlimit
  ## internally. Reused here (same proven shape) to force
  ## `concreteBranchOutcome`'s own scratch solves to exhaust their bound.
  if a * b * c * d == 1234567:
    symexTarget("rare")

# R7: same tiny-rlimit-budget idiom as `tsymex_phase13_rlimit.nim`'s
# `tightSettings` — explicit literal (not `defaultSymexSettings()` mutated)
# so the `static SymexSettings` macro parameter gets a plain const value.
const tightMultSettings = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 1'u,
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 5))

# R14: a tiny `maxLoopUnwind` to force the k-unroll safety backstop without
# needing a slow, deeply-nested trace.
const tightUnwindSettings = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 0'u,
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 2))

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

  test "R1: an int64-unrepresentable integer draw degrades to concretization, not a corrupt Z3 domain":
    # Mirrors `derive.nim`'s stock `uint64`/`uint` strategy:
    # `drawInteger(toInt128(0'u64), toInt128(high(uint64)), toInt128(0))` — a
    # `ChoiceInt` (`Int128`) range whose `max` does not fit `int64`.
    # `toInt64(high(uint64))` silently wraps to `-1`; asserting that
    # unguarded as a Z3 bound would produce the inverted, unsatisfiable
    # domain `[0, -1]`, which `materializeConcolicModel` cannot construct an
    # `integerChoice` from (it raises `ValueError`, aborting the whole
    # campaign — the defect this test pins). The fix must treat this draw
    # the same way an unsupported `ChoiceKind` (ckFloat/ckBytes/ckString) is
    # treated: not symbolicated, concretized to its recorded value, counted
    # rather than silently dropped.
    let trace = @[integerChoice(0'u64, 0'u64, high(uint64), 0'u64)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(concolicIfGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.nonInt64Draws == 1
    check r.counters.drawsSymbolicated == 0
    check r.counters.paramsConcretized == 1

suite "R7 — concreteBranchOutcome is genuinely rlimit-bounded (not silently 0/unlimited)":

  test "concreteBranchRLimit: default settings get a genuine non-zero bound":
    # Pins the actual regression this finding is about: if the fix ever
    # regressed to reading `settings.budget.queryRLimit` directly (this
    # codebase's normal "0 = unbounded" convention), this would read `0`
    # under `defaultSymexSettings()` and `concreteBranchOutcome` would be
    # exactly as unbounded as it was before the fix.
    check defaultConcreteBranchRLimit > 0'u
    check concreteBranchRLimit(defaultSymexSettings()) == defaultConcreteBranchRLimit
    check concreteBranchRLimit(defaultSymexSettings()) > 0'u

  test "concreteBranchRLimit: an explicit caller budget always wins over the default":
    var bigger = defaultSymexSettings()
    bigger.budget.queryRLimit = 777'u
    check concreteBranchRLimit(bigger) == 777'u   ## caller wanting MORE wins
    var smaller = defaultSymexSettings()
    smaller.budget.queryRLimit = 1'u
    check concreteBranchRLimit(smaller) == 1'u    ## caller wanting LESS wins too

  test "an exhausted rlimit degrades the branch to ambiguous, never a wrong definite answer":
    # `tightMultSettings.budget.queryRLimit = 1` forces BOTH of
    # `concreteBranchOutcome`'s scratch solves (`cond` and `not cond` under
    # the concrete pins) to exhaust before deciding — `zsUnknown` on both,
    # which is neither the "exactly one SAT + one UNSAT" case, so the
    # result can only fall through to `none(bool)`: never a wrong
    # `some(true)`/`some(false)`. The caller (`walkIfFollowConcrete`)
    # observes this as an ambiguous branch — counted, path truncated
    # gracefully — not a hang, not a crash, not an unsound constraint.
    let trace = @[integerChoice(2, -1000, 1000, 0), integerChoice(3, -1000, 1000, 0),
                  integerChoice(5, -1000, 1000, 0), integerChoice(7, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 2),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 3)]
    let r = concolicCollect(concolicMultGate, trace, bindings, tightMultSettings)
    check r.counters.ambiguousBranches == 1
    check r.pcSatByConcreteInputs  ## degrading early asserts nothing false

suite "R14 — wmFollowConcrete extended to while (no hypothetical unrolling)":

  test "3-iteration while before one if: exactly one branchTrace entry, soundness pin holds":
    # n = 3 -> the loop guard `i < n` is concretely true at i=0,1,2 and
    # false at i=3 (three real iterations). Pre-fix, `wmExplore`'s
    # fork-both-ways k-unroll ran regardless of mode: one bogus surviving
    # path per unrolled iteration (up to `maxLoopUnwind`, default 10) each
    # reaching the trailing `if` independently and adding its OWN
    # `branchTrace` entry — this is the reviewer's measured benchmark
    # (`branchTrace.len == 6`, `pcSatByConcreteInputs == false`). The fix
    # follows only the real 3-iteration trajectory: exactly ONE surviving
    # path reaches the `if`, so exactly one `branchTrace` entry, and the
    # union of that single survivor's `pc` with `concreteEq` is consistent
    # (no bogus loop-exit paths contradicting each other).
    let trace = @[integerChoice(3, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(whileThenIfGate, trace, bindings)
    check r.counters.ambiguousBranches == 0
    check r.branchTrace.len == 1          ## only the trailing `if` — was 6 pre-fix
    check r.branchTrace[0].armTaken == -1 ## `i > 100` is false -> else/fallthrough
    check r.pcSatByConcreteInputs         ## was false pre-fix

  test "0-iteration while before one if: the guard is concretely false on entry, no fork at all":
    let trace = @[integerChoice(0, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(whileThenIfGate, trace, bindings)
    check r.counters.ambiguousBranches == 0
    check r.branchTrace.len == 1
    check r.pcSatByConcreteInputs

  test "while trip count at the maxLoopUnwind bound still degrades gracefully (not a hang, not a false answer)":
    # A concrete trace that genuinely iterates MORE than `maxLoopUnwind`
    # allows must still terminate the walk (safety backstop), marking the
    # exhausted path uncertain rather than either hanging or silently
    # fabricating a definite outcome.
    let trace = @[integerChoice(5, 0, 10, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(whileThenIfGate, trace, bindings, tightUnwindSettings)
    check r.counters.ambiguousBranches == 0
    check r.pcSatByConcreteInputs
