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
## #161's overflow-obligation mechanism has an adjacent, still-open gap:
## `overflowConds`/`divByZeroConds` are populated for signed BV operands (and,
## after R16, a signed svInt operand needs `ziWidth`/`ziSigned` stamped, which
## R16's fix deliberately does NOT do for the params it leaves on the Z3Int
## route -- see `concolicScalarPromotesSoundly`'s own doc comment in
## `runtime.nim` for why). So an overflow obligation an `if`/`while` might
## depend on still never exists on a concolic-bound path for a signed param
## R16 leaves promoted -- unobservable the same way R3/R4/W2 are, and out of
## this file's scope; reported, not fixed.
##
## Section D below WAS a live finding at review time: every concolic-bound
## int was an idealized, non-wrapping, non-overflowing `Z3Int` no matter what
## Nim type it was declared as, regardless of the property's declared width
## or signedness (`runConcolicCollectImpl`, `runtime.nim` -- `p.ty.hasRange`/
## `p.ty.width`/`p.ty.signed` were never read there at all; only the trace's
## OWN `ChoiceNode.intC.min/max` bounds were asserted). That could make
## `walkIfFollowConcrete` INFER A BRANCH DECISION THAT DISAGREED WITH THE REAL
## CONCRETE EXECUTION THE TRACE WAS SUPPOSEDLY RECORDED FROM, silently, with
## the `pcSatByConcreteInputs` soundness pin unable to catch it (the pin only
## checks the walker's OWN model for internal self-consistency, which an
## idealized wrong model still has). Section D is now the FIX's regression
## pin: `concolicScalarPromotesSoundly` (`runtime.nim`) decides, per param,
## whether an idealized Z3Int is sound or whether the param must bind at its
## declared width/signedness (a bitvector) instead.

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
# Section D -- FIXED (was a live FINDING): concolic-bound scalar params used
# to be ALWAYS an idealized, non-wrapping Z3 Int, regardless of the
# property's declared width/signedness -- producing a branch decision that
# DISAGREED with the real concrete execution the trace claims to record
# =============================================================================
#
## Issue #163 review finding R16. This section used to leave its
## reproduction as a comment, deliberately unasserted (a real mode
## divergence, reported rather than pinned as expected behaviour). It is now
## the fix's own regression pin: `runConcolicCollectImpl` (`smt/runtime.nim`)
## binds a scalar `itInt` param as a width/signedness-faithful bitvector
## whenever `concolicScalarPromotesSoundly` cannot prove an idealized Z3Int
## agrees with the type's own (possibly wrapping/truncating) arithmetic --
## the same soundness question `promoteSound` already answers for
## `wmExplore`, applied to the mode that actually feeds the fuzzer.
##
## Every case below is checked THREE ways against the SAME concrete inputs:
## the oracle (real Nim, executed in this file), `wmExplore` (`symexFind`,
## restricted to the exact input pair via an explicit equality guard, since
## `symexFind` otherwise searches the whole domain), and `wmFollowConcrete`
## (`concolicCollect`, replaying the recorded trace). All three must agree.

# ---- D1: the headline repro -- an UNSIGNED narrow width (uint8) ------------

proc addU8Gate(a, b: range[0'u8..255'u8]) =
  if a + b < a:
    symexTarget("wrapped")

proc addU8GateAt200_100(a, b: range[0'u8..255'u8]) =
  ## `wmExplore`'s own twin of `addU8Gate`, pinned to the exact concrete pair
  ## the oracle and `wmFollowConcrete` tests below both use -- `symexFind`
  ## otherwise proves REACHABILITY over the whole domain, not "does this one
  ## input reach it", so the guard is what makes the three checks comparable.
  if a == 200'u8 and b == 100'u8 and a + b < a:
    symexTarget("wrapped_200_100")

# ---- D2: a SIGNED narrow width (int8), under UNCHECKED arithmetic ----------
#
# Under DEFAULT (checked) settings, signed overflow RAISES rather than
# silently disagreeing on a VALUE (see `tsymex_161_overflow_obligation.nim`),
# and `ConcolicCollectResult` exposes no raised-verdict channel at all (see
# this file's Section B) -- so a checked-arithmetic signed overflow is not
# the right shape to pin a VALUE-level disagreement with. Unchecked
# arithmetic (`acOverflow` excluded, matching `-d:danger`/`--overflowChecks:off`)
# is where signed overflow becomes a DEFINED wrap too, exactly like the
# unsigned case above -- `tsymex_161_overflow_obligation.nim`'s own
# `wrapProbe`/`Unchecked` idiom, reused here for the concolic mode it never
# covered.

const Unchecked163R16 = SymexSettings(integerSemantics: isOptimised,
                                      arithChecks: {acDivByZero, acRange})

proc addI8UncheckedGate(a, b: int8) =
  if a + b < a:
    symexTarget("i8_wrapped")

proc addI8UncheckedGateAt100_100(a, b: int8) =
  if a == 100'i8 and b == 100'i8 and a + b < a:
    symexTarget("i8_wrapped_100_100")

# ---- D3: the non-regression anchor -- plain `int`, default (checked) settings
#
# The common case across every OTHER concolic suite in this codebase
# (`tsymex_g1b_concolic.nim`, W10's own fixtures, G6's transform-binding
# suite): a 64-bit signed, unranged param. `concolicScalarPromotesSoundly`
# keeps this one exactly as it always was (an idealized Z3Int) -- this proves
# the fix does not disturb it, using the SAME oracle/wmExplore/wmFollowConcrete
# three-way shape as D1/D2, just with values nowhere near wrapping.

proc addIntGate(a, b: int) =
  if a + b < a:
    symexTarget("int_wrapped")

proc addIntGateAt100_100(a, b: int) =
  if a == 100 and b == 100 and a + b < a:
    symexTarget("int_wrapped_100_100")

suite "#163 review R16 -- concolic-bound scalar params bind at their declared width/signedness":

  test "D1 oracle: 200'u8 + 100'u8 wraps to 44 -- 200+100 < 200 is true":
    check 200'u8 + 100'u8 == 44'u8
    check (200'u8 + 100'u8) < 200'u8

  test "D1 wmExplore agrees the wrap is reachable at exactly a=200, b=100":
    let r = symexFind(addU8GateAt200_100, tLabel("wrapped_200_100"))
    check r.status == sxSat

  test "D1 wmFollowConcrete now agrees too (was armTaken == -1, the wrong arm, before this fix)":
    let trace = @[integerChoice(200, 0, 255, 0), integerChoice(100, 0, 255, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(addU8Gate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == 0    ## the "if" arm ("wrapped")

  test "D2 oracle: under unchecked arithmetic, 100'i8 + 100'i8 wraps to -56":
    {.push overflowChecks: off.}
    proc rt(a, b: int8): int8 = a + b
    {.pop.}
    let c = rt(100'i8, 100'i8)
    check c == -56'i8
    check c < 100'i8

  test "D2 wmExplore agrees the wrap is reachable at exactly a=100, b=100 (unchecked)":
    let r = symexFind(addI8UncheckedGateAt100_100, tLabel("i8_wrapped_100_100"),
                      Unchecked163R16)
    check r.status == sxSat

  test "D2 wmFollowConcrete now agrees too for a signed narrow width":
    let trace = @[integerChoice(100, -128, 127, 0), integerChoice(100, -128, 127, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(addI8UncheckedGate, trace, bindings, Unchecked163R16)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == 0    ## the "if" arm ("i8_wrapped")

  test "D3 oracle: 100 + 100 neither wraps nor overflows a plain int":
    check not (100 + 100 < 100)

  test "D3 wmExplore agrees at exactly a=100, b=100 (non-regression)":
    let r = symexFind(addIntGateAt100_100, tLabel("int_wrapped_100_100"))
    check r.status == sxUnsat

  test "D3 wmFollowConcrete agrees too -- an ordinary int stays Z3Int and this fix leaves it alone":
    let trace = @[integerChoice(100, -1000, 1000, 0), integerChoice(100, -1000, 1000, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(addIntGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == -1   ## the else arm; unchanged by this fix

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 136 (the review round's single bump)":
    ## One bump covers R1/R2/R3/R4/R15 -- every one a verdict change, so a
    ## cache entry written under any one of them can replay a wrong verdict
    ## under the others. Compared numerically, not lexicographically:
    ## `"1000" < "135"` as strings.
    check parseInt(symexWalkerVersion) >= 136
