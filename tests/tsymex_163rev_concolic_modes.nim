## Issue #163 review finding R6 -- every mechanism this branch built (#161
## overflow obligations, #162 range base-width, R1 inert-argfork, R2 enum
## domain, R3 ref-variant arm fields, R4 Table clamp) was pinned only through
## `symexFind` (`wmExplore`). `wmFollowConcrete` -- the mode `concolicCollect`/
## `concolicFlip` drive, and the ONLY mode the fuzzer itself walks -- shares
## almost all of that code but had zero coverage of its own: `concolic`
## appeared in `tsymex_163audit_w10.nim` alone (10 refs) across all eight
## suites this branch added. This file is the remediation.
##
## `tsymex_163audit_w10.nim` is the existing idiom (`concolicCollect(fn,
## trace, bindings)`, one `ConcolicParamBinding` per property param) and
## already pins the headline W10 property (an opaque call taints a concolic
## collect; a clean SUT and a `{.cover.}`'d SUT do not) -- this file does not
## repeat that, it extends past it.
##
## Working out what is genuinely OBSERVABLE through `concolicCollect`'s
## public surface (`ConcolicCollectResult`: `pcSatByConcreteInputs`,
## `counters`, `branchTrace`, `drawVars` -- no witness, no raised-verdict
## channel at all) turned up a real structural limit, not a testing
## inconvenience:
##
##   - `ConcolicParamBinding` (`smt/runtime.nim`) has exactly three binding
##     kinds (`cbDrawLinked`/`cbConcretized`/`cbTransformLinked`), and every
##     one of them resolves to a bare `SymVal(kind: svBool, ...)` or
##     `SymVal(kind: svInt, ...)` -- there is no way to bind a `seq`, `Table`,
##     `ref`, or `object`-typed top-level property parameter at all. #162
##     slice 5's own fix (bounds live on `IRType`, inherited through
##     `allocateSym`'s recursion) and R3/R4 (ref-variant arm field, Table
##     clamp) are exercised in EVERY existing test exclusively through a
##     ref/seq/Table PARAMETER (`tsymex_163audit_range_elem.nim`,
##     `tsymex_163rev_table_elem.nim`, `tsymex_163rev_variant_armfield.nim`,
##     `tsymex_a2_refvariant_fields.nim` -- every SUT in all four takes the
##     ranged container as `p: ref ...`/`t: Table[...]`/`s: seq[...]`).
##   - A LOCALLY `new()`-allocated object pointee zero-writes every field
##     (Cluster H Step C, `runtime_heap.nim` ~969) rather than leaving it
##     free/havoc -- so even inside a concolic-walked body, there is no way
##     to construct a ranged field/element that stays genuinely
##     UNCONSTRAINED (the exact condition R3/R4/W2 exist to fix: "the model
##     was free to pick an out-of-range value"). `runtime_heap.nim`'s own
##     comment there additionally states a variant object pointee never
##     reaches `isNew` at all ("isNewCall gates never fire for them").
##
## Net: R3, R4, and W2 (seq-element range clamp) have NO reachable surface
## in `concolicCollect` today -- not a mode divergence (nothing behaves
## wrong), a scope gap in G1b's own parameter-binding surface. Named here
## rather than faked with a test that binds nothing meaningful.
##
## #161's overflow-obligation mechanism has the same fate for an adjacent
## reason: `overflowConds`/`divByZeroConds` are populated for signed BV
## operands only ("svInt (unbounded Z3Int) is skipped -- overflow is
## meaningless there", `runtime.nim` ~1108), and EVERY concolic-bound scalar
## param -- `cbDrawLinked`, `cbConcretized`, `cbTransformLinked`, all three --
## is built as a plain `mkIntVar`/`mkZ3IntLit`, i.e. `SymVal(kind: svInt,
## ...)`, regardless of the property's declared width or signedness
## (`runConcolicCollectImpl`, `runtime.nim` ~13438-13562 -- `p.ty.hasRange`/
## `p.ty.width`/`p.ty.signed` are never read there at all; only the trace's
## OWN `ChoiceNode.intC.min/max` bounds are asserted). So an overflow
## obligation an `if`/`while` might depend on simply never exists on a
## concolic-bound path -- unobservable the same way R3/R4/W2 are.
##
## That same fact -- every concolic-bound int is an idealized, non-wrapping,
## non-overflowing `Z3Int` no matter what Nim type it is declared as -- is
## NOT always merely "unobservable". Section D below is a live finding: it
## can make `walkIfFollowConcrete` INFER A BRANCH DECISION THAT DISAGREES
## WITH THE REAL CONCRETE EXECUTION THE TRACE WAS SUPPOSEDLY RECORDED FROM,
## silently, with the `pcSatByConcreteInputs` soundness pin unable to catch
## it (the pin only checks the walker's OWN model for internal self-
## consistency, which an idealized wrong model still has). See section D.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex
import nelli/coverage

# =============================================================================
# Section A -- `{.symexTransparent.}` (`{.cover.}`) branch decisions
# reconstruct CORRECTLY under concolic, not just non-degrading
# =============================================================================
#
# W10 (`tsymex_163audit_w10.nim`) already pins that a `{.cover.}`'d SUT does
# not taint a concolic collect (`walkDegradeCount == 0`). It never reads
# `branchTrace`, so it does not prove the RECONSTRUCTED DECISION is the right
# one -- only that nothing degraded. Since nelli's own coverage
# instrumentation is dropped at PARSE time (#163 slice 1 -- the call never
# reaches the IR the walker sees at all), a `{.cover.}`'d proc's walked
# program is byte-identical in both modes; this is the strongest possible
# form of cross-mode agreement; a divergence here would mean the parser drop
# depends on which walker will later run, which it structurally cannot.

proc coveredGate(x: int) {.cover.} =
  if x > 5:
    symexTarget("hi")
  else:
    symexTarget("lo")

suite "#163 review R6 -- {.cover.} branch decisions reconstruct correctly under wmFollowConcrete":

  test "oracle: coveredGate's predicate is exactly x > 5":
    doAssert (10 > 5) == true
    doAssert (5 > 5) == false
    doAssert (0 > 5) == false

  test "x = 10 (hi): concolic replay takes the SAME arm real Nim takes, and does not degrade":
    let trace = @[integerChoice(10, 0, 20, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(coveredGate, trace, bindings)
    check r.counters.walkDegradeCount == 0    ## non-regression: still transparent
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == 0      ## the `if` arm ("hi")

  test "x = 2 (lo): concolic replay takes the else arm, and does not degrade":
    let trace = @[integerChoice(2, 0, 20, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(coveredGate, trace, bindings)
    check r.counters.walkDegradeCount == 0
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == -1     ## the else arm ("lo")

  test "x = 5 (boundary, lo): the strict inequality is reconstructed correctly at the edge":
    let trace = @[integerChoice(5, 0, 20, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(coveredGate, trace, bindings)
    check r.counters.walkDegradeCount == 0
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == -1     ## 5 > 5 is false in real Nim too

# =============================================================================
# Section B -- R1: an inert opaque call's own argument-defect-fork lowering
# does not degrade a concolic collect either (cross-mode non-regression)
# =============================================================================
#
# R1 (`tsymex_163rev_inert_argfork.nim`) is about a DIFFERENT property than
# W10's opaqueGate: not whether the CALL itself taints, but whether an
# argument expression with its own inline defect-fork shape (`a div b`) still
# gets LOWERED (for its raise-obligation side effect) on the walker's inert
# fast path. Under `wmExplore` the observable proof is "the raise is FOUND as
# reachable" (`symexFind(..., tRaisedExn("DivByZeroDefect"))` -> `sxRaised`).
#
# `ConcolicCollectResult` has no raised-verdict channel at all (no `witness`,
# no `found`-equivalent field) -- `runConcolicCollectImpl` computes exactly
# the same `w.found` entry internally (`routeRaise`'s `raisedIsDefect` arm
# fires for `DivByZeroDefect` regardless of `w.target`, since a raised
# `Defect` always wants surfacing) but the driver never reads `w.found`, only
# `branchTrace`/`counters`/`pcSatByConcreteInputs`/`drawVars`. So R1's own
# headline soundness property -- "the argument's raise obligation is LIVE" --
# has NO way to show up in a `concolicCollect` result: fed `b == 0` (an input
# that DOES crash for real), the result is observationally IDENTICAL to
# `b == 5`. Empirically confirmed while building this suite (both cases:
# `walkDegradeCount == 0`, `pcSatByConcreteInputs == true`, no branchTrace
# entries -- there is no `if` in these SUTs). Not unsound for the fuzzer's
# actual operation: a worker's own process crashes on `b == 0` during ordinary
# concrete replay, well before `concolicCollect` is ever called on that
# input -- crash detection lives at the execution layer, not this API.
#
# What DOES generalize across modes, and is what this section pins: the
# fast-path lowering must not ITSELF regress into a degrade
# (`feOpaqueCallUnmodelled`) under concolic either -- the same non-regression
# `tsymex_163rev_inert_argfork.nim` pins for `wmExplore`
# ("not opaqueUnmodelled").

proc sink(x: int) {.symexOpaque.} = discard

proc withDivArgRT(a, b: int): int = a div b

proc withDivArg(a, b: int) =
  sink(a div b)
  symexTarget("reached")

proc withPlainSink(x: int) =
  sink(x)
  if x == 0x5A4D:
    raise newException(ValueError, "magic")
  symexTarget("t_reached")

suite "#163 review R6 -- R1's inert-argfork lowering does not degrade wmFollowConcrete":

  test "oracle: a div b really raises DivByZeroDefect at b == 0, and only then":
    expect DivByZeroDefect:
      discard withDivArgRT(10, 0)
    check withDivArgRT(10, 5) == 2

  test "withDivArg(10, 5) -- non-crashing input: concolic collect does not degrade":
    let trace = @[integerChoice(10, -1000, 1000, 0), integerChoice(5, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(withDivArg, trace, bindings)
    check r.counters.walkDegradeCount == 0
    check r.pcSatByConcreteInputs

  test "withDivArg(10, 0) -- a REAL crashing input: collect still does not degrade, hang, or crash":
    ## The unobservability this section's own comment describes: this result
    ## is indistinguishable from the b == 5 case above at this API surface.
    let trace = @[integerChoice(10, -1000, 1000, 0), integerChoice(0, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(withDivArg, trace, bindings)
    check r.counters.walkDegradeCount == 0
    check r.pcSatByConcreteInputs

  test "oracle: withPlainSink raises on Magic, and only then":
    expect ValueError:
      withPlainSink(0x5A4D)
    withPlainSink(0)

  test "withPlainSink -- a genuinely inert (bare-value) opaque call still does not degrade":
    let trace = @[integerChoice(3, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(withPlainSink, trace, bindings)
    check r.counters.walkDegradeCount == 0
    check r.pcSatByConcreteInputs

# =============================================================================
# Section C -- named but not tested here: range-on-container and overflow
# obligations have no reachable surface in concolicCollect (see file header)
# =============================================================================
#
# #162/R3/R4/W2 (range bounds on a seq element / Table value / ref-variant
# arm field) and #161 (overflow obligations): no test below. Both require
# either (a) a non-scalar top-level property parameter, which
# `ConcolicParamBinding` cannot bind (only `itInt`/`itBool`), or (b) a
# genuinely free/havoc value constructed some other way inside the walked
# body, which a local `new()` allocation does not provide (Cluster H Step C
# zero-writes every field). See the file header for the full reasoning and
# source citations. Writing a "test" against either would mean binding
# nothing the mechanism actually needs, or asserting a tautology -- exactly
# the vacuous-assertion failure mode this task was warned against.

# =============================================================================
# Section D -- FINDING (new, not previously tracked): concolic-bound scalar
# params are ALWAYS an idealized, non-wrapping Z3 Int, regardless of the
# property's declared width/signedness -- this can produce a branch decision
# that DISAGREES with the real concrete execution the trace claims to record
# =============================================================================
#
## This is reported as a finding, not encoded as an expected/pinned result --
## per this task's own instructions, a real mode divergence must be reported,
## not baked into a passing test. No `check` below asserts the (wrong)
## observed value; the reproduction is left as a comment so it can be re-run
## and is not lost, without the suite depending on today's buggy answer.
##
## Reproduction (verified empirically while building this suite, walker
## unchanged from this branch's HEAD):
##
##   proc addU8Gate(a, b: range[0'u8..255'u8]) =
##     if a + b < a:
##       symexTarget("wrapped")
##
##   let trace = @[integerChoice(200, 0, 255, 0), integerChoice(100, 0, 255, 0)]
##   let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
##                    ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
##   let r = concolicCollect(addU8Gate, trace, bindings)
##   # r.pcSatByConcreteInputs == true
##   # r.branchTrace.len == 1
##   # r.branchTrace[0].armTaken == -1   <-- WRONG. See below.
##
## `addU8Gate(200'u8, 100'u8)` in REAL Nim takes the `if` arm: `200 + 100`
## wraps to `44` as `uint8` (Nim's DEFINED behaviour for unsigned overflow --
## this is exactly `tsymex_162_range_base_width.nim`'s own `addU8` fixture,
## and `symexFind(addU8, tLabel("wrapped"))` correctly reports `sxSat` under
## `wmExplore`, per that file's "isOptimised agrees" test). So a trace
## recording that REAL run would legitimately claim `a=200, b=100` reached
## the "wrapped" label.
##
## Feeding that exact trace to `concolicCollect` reconstructs `armTaken ==
## -1` -- the ELSE arm -- the OPPOSITE of what really happened. Root cause:
## `runConcolicCollectImpl` binds every `cbDrawLinked`/`cbConcretized` scalar
## param as a plain `SymVal(kind: svInt, zi: mkIntVar(...))` (`runtime.nim`
## ~13438-13512), i.e. an UNBOUNDED Z3 Int -- never a bitvector, and never
## consulting the property's own declared width/signedness/range at all.
## `walkIfFollowConcrete`'s `concreteBranchOutcome` (`runtime.nim` ~8733) then
## asks Z3 whether `a + b < a` holds under `concreteEq` (a==200, b==100) --
## and under EXACT (non-wrapping) arithmetic, `300 < 200` is simply false.
## The walker infers the wrong arm from a self-consistent but wrong model of
## Nim's own arithmetic, and reports it as though it were the real trace.
##
## `pcSatByConcreteInputs` stays `true` throughout: the soundness pin only
## checks that the COLLECTED pc is satisfiable together with `concreteEq` --
## it has no way to check the collected pc against a ground-truth EXECUTION,
## only against its own (here, wrong) model of what that execution meant.
## So the one channel this mechanism exposes for "did something go wrong"
## reports "no" on exactly the input that demonstrates it did.
##
## Consequence for the fuzzer (the actual motivating consumer, per this
## branch's whole premise): ANY property with an unsigned/narrow-width
## integer parameter whose real behaviour depends on wraparound (or,
## symmetrically, overflow — see the file header's #161 paragraph) gets a
## `branchTrace` from `concolicCollect` that can name the WRONG arm at the
## WRONG index for a REAL, previously-observed execution. A `concolicFlip`
## G2 flip-solve built from that `branchTrace` (`runtime.nim`'s
## `runConcolicFlipImpl`, which indexes into `branchTrace` by
## `targetBranchIndex`) would then be solving a formula for a branch decision
## that never happened, on a trace that supposedly proves it did.
##
## This looks distinct from every closed finding in
## `docs/issue-0163-opaque-call-taint.handoff.md` (R1-R15) at the time this
## suite was written -- none of them describe concolic-mode scalar params
## losing width/signedness. Reported here rather than fixed: `src/` changes
## are out of scope for this task, and the fix (representing a `cbDrawLinked`/
## `cbConcretized` scalar param as a proper width/signedness-aware BV, the way
## `runSymexImpl`'s own `allocateSym`-based param setup already does for
## `wmExplore`) touches the same shared machinery #161/#162 just finished
## stabilizing under a different mode entirely.


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    ## One bump covers R1/R2/R3/R4/R15 -- every one a verdict change, so a
    ## cache entry written under any one of them can replay a wrong verdict
    ## under the others. Compared numerically, not lexicographically:
    ## `"1000" < "135"` as strings.
    check parseInt(symexWalkerVersion) >= 135
