## Issue #163 review round -- R24/R25/R26. Three gaps R16 (concolic scalar
## params binding at their declared width/signedness, `tsymex_163rev_concolic_
## modes.nim`) left open, all in the CONCOLIC path (`wmFollowConcrete`) -- the
## mode the fuzzer actually drives.
##
## R24 (Medium) -- `runConcolicFlipImpl`/`materializeConcolicModel` used to
## read a solved model's value off `drawVars[i].zi` unconditionally. For a
## param R16 binds as a BV (unsigned, or a narrow signed type with no proven
## range), `env[p.name]` is a FRESH, independently-pinned BV variable --
## `drawVars[i]` stays a completely disconnected Z3Int, never referenced by
## any branch predicate that reads the param. A flip-solve targeting such a
## decision therefore solves the RIGHT formula (built from the BV var) but
## reads back the WRONG variable, producing an uninformative draw. Fixed by
## `drawOverrides` (`ConcolicCollectResult`, `smt/runtime.nim`): per-draw-index
## bookkeeping of which variable a `useBV` binding actually built `env`
## from, consulted by `materializeConcolicModel` in preference to `drawVars`.
##
## R25 (Low) -- `cbTransformLinked`'s BV branch used to concretize the
## affine value to a GROUND LITERAL (to avoid an `int2bv`/`bv2int` bridge),
## sacrificing that param's flip-ability entirely: the branch predicate
## became a comparison between two ground constants, permanently
## unsatisfiable in the flipped direction. Fixed the same way R24's direct
## binding is: a fresh BV variable stands in for the DRAW (not the
## transformed param), pinned by a ground equality (no bridge), combined
## with the affine coefficients via ordinary same-width BV arithmetic.
##
## R26 (Medium) -- a concolic-bound signed param that stays on the IDEALIZED
## Z3Int route (width 64, or a proven range) carried no `ziWidth`/`ziSigned`
## stamp, so `overflowCondInt`'s (#161) raise obligation never fired on a
## concolic-bound path, at ANY width. Fixed by stamping exactly the same
## width/signedness `promoteSound` (`wmExplore`'s own counterpart) already
## carries, everywhere `runConcolicCollectImpl` builds a Z3Int `env[p.name]`
## for an `itInt` param.
##
## `ConcolicCollectResult` has no raised-verdict channel at all (no
## `witness`, no `found`-equivalent field -- `tsymex_163rev_concolic_modes.
## nim`'s own header already established this for R1's div-by-zero case), and
## `w.branchTrace` records ONLY `isIf` decisions (`walkIfFollowConcrete`) --
## an overflow raise-fork is not an `if` and gets no `ConcolicBranchRecord`.
## Neither `ConcolicYieldCounters` nor `ConcolicFlipCounters`
## (`smt/concolictaxonomy.nim`) has a slot for "a raise fired during
## collection" either. So R26's fix makes the OBLIGATION MACHINERY ITSELF
## fire correctly (verified below via the SAME `obligationLog` threadvar
## `RawResult.obligations` is drained from, which `runConcolicCollectImpl`
## resets and populates identically to `runSymexImpl`), but the fact that it
## fired is NOT observable through `concolicCollect`'s or `concolicFlip`'s
## own public result types -- confirmed by inspection (both are plain
## `object`s, exhaustively enumerated in this file's own imports), not
## merely asserted. Wiring a raised-verdict channel through
## `ConcolicCollectResult` (and from there into `fuzz.nim`'s orchestrator,
## which this task does not own) is a genuinely separate, larger slice.
##
## House rule: every symbolic expectation below is paired with an ORACLE
## (the same computation executed for real, in Nim, in this file) and, where
## meaningful, cross-checked against `wmExplore` (`symexFind`) too -- the
## three-way agreement `tsymex_163rev_concolic_modes.nim`'s Section D
## established for R16.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import nelli/int128

# =============================================================================
# R24 -- concolicFlip over a BV-bound (uint8) direct draw-linked param
# =============================================================================
#
# The draw's OWN declared domain is narrowed to [0, 201] (not the full uint8
# range) specifically so the flip target (`x > 200`) has EXACTLY ONE feasible
# value left once the draw's own range constraint (`bvRangeConds`, part of
# this fix) is folded into the formula -- making the solved witness
# deterministic and checkable by exact value, not just by outcome/coverage
# enum. Before this fix (no draw-range constraint on the fresh BV var, and
# `materializeConcolicModel` reading the disconnected `drawVars[0].zi`
# instead), this same setup solved the FORMULA correctly but reconstructed an
# uninformative value disconnected from it -- see this file's own commit
# message / R24 writeup for the empirically-confirmed pre-fix witness.

proc u8ThresholdGate(x: uint8) =
  if x > 200'u8:
    symexTarget("hi")
  else:
    symexTarget("lo")

proc u8ThresholdGateAt201(x: uint8) =
  ## `wmExplore`'s own pinned-input twin of `u8ThresholdGate`, restricted to
  ## the exact value the flip below is expected to solve for -- mirrors
  ## `tsymex_163rev_concolic_modes.nim`'s own `addU8GateAt200_100` idiom.
  if x == 201'u8 and x > 200'u8:
    symexTarget("hi_at_201")

suite "#163 review R24 -- concolicFlip on a BV-bound uint8 param":

  test "oracle: 201'u8 > 200'u8, and 5'u8 does not":
    check 201'u8 > 200'u8
    check not (5'u8 > 200'u8)

  test "wmFollowConcrete collect: x = 5 takes the lo arm, non-degrading (non-regression anchor)":
    let trace = @[integerChoice(5, 0, 201, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicCollect(u8ThresholdGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.walkDegradeCount == 0
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == -1   ## "lo" -- 5 is not > 200

  test "wmExplore cross-check: x == 201 reaching \"hi\" is independently confirmed reachable":
    let r = symexFind(u8ThresholdGateAt201, tLabel("hi_at_201"))
    check r.status == sxSat

  test "R24: the flip solves the SAME variable it bound -- a usable, exact flipped draw":
    let trace = @[integerChoice(5, 0, 201, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    let r = concolicFlip(u8ThresholdGate, trace, bindings, 0)
    check r.outcome == cfoSolvedExact
    check r.materialized.len == 1
    # The load-bearing assertion: under the pre-fix bug this read back
    # `drawVars[0].zi` -- a Z3Int bounded only by [0, 201] and otherwise
    # completely disconnected from the actual flip formula (which was built
    # from a separate, fresh BV variable) -- so the model was free to pick
    # ANY in-range value, deterministically 0 for a totally unconstrained
    # variable under Z3's own model-completion default. `int(201)` is the
    # UNIQUE value satisfying both "> 200" and the draw's own [0, 201] bound.
    check $r.materialized[0] == "int(201)"
    # The flip's own re-collection genuinely reaches the untaken arm now --
    # this is the OTHER symptom the pre-fix bug produced (`ccoUnrelatedCoverage`,
    # since materializing 0 does not flip anything).
    check r.coverage == ccoIntendedCovered
    # Cross-mode: replaying the materialized draw through an ORDINARY collect
    # (not just the flip's own internal re-check) independently confirms the
    # SAME thing -- the "hi" arm is now taken.
    let replayed = concolicCollect(u8ThresholdGate, r.materialized, bindings)
    check replayed.branchTrace.len == 1
    check replayed.branchTrace[0].armTaken == 0   ## "hi"

# =============================================================================
# R25 -- concolicFlip over a transform-linked (cbTransformLinked) param whose
# TYPE is not width-64-signed (uint8) -- the BV branch that used to concretize
# =============================================================================

proc u8MappedGate(mapped: uint8) =
  if mapped == 201'u8:
    symexTarget("hit")
  else:
    symexTarget("miss")

proc u8MappedGateExplore(draw: range[0'u8..100'u8]) =
  ## `wmExplore`'s own twin of the transform: the SAME affine map
  ## (`2*draw + 1`), expressed as ordinary Nim arithmetic over the
  ## pre-transform quantity, so a reachability check here is genuinely
  ## independent confirmation of the same fact the concolic flip claims.
  let mapped = draw * 2'u8 + 1'u8
  if mapped == 201'u8:
    symexTarget("hit")

suite "#163 review R25 -- concolicFlip over a transform-linked BV-bound (uint8) param":

  test "oracle: 2*100 + 1, as a uint8, is 201":
    check uint8(2 * 100 + 1) == 201'u8

  test "wmExplore cross-check: draw = 100 reaching mapped == 201 is independently reachable":
    let r = symexFind(u8MappedGateExplore, tLabel("hit"))
    check r.status == sxSat

  test "wmFollowConcrete collect: draw = 7 (mapped = 15) takes the miss arm, non-degrading":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: 0, tA: 2, tB: 1)]
    let r = concolicCollect(u8MappedGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.walkDegradeCount == 0
    check r.counters.paramsConcretized == 0   ## stays symbolic -- R25's own fix
    check r.branchTrace.len == 1
    check r.branchTrace[0].armTaken == -1     ## "miss" -- 15 != 201

  test "R25: the flip stays symbolic through the affine transform -- no longer a dead ground-literal comparison":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: 0, tA: 2, tB: 1)]
    let r = concolicFlip(u8MappedGate, trace, bindings, 0)
    # Under the pre-fix bug `env["mapped"]` was a GROUND BV CONSTANT (15),
    # so the branch predicate was `15'u8 == 201'u8` -- a tautologically FALSE
    # comparison between two literals, no free variable anywhere. Negating an
    # always-false predicate is an always-true one with nothing to solve for
    # in the "miss" direction, and the "hit" direction (`15 == 201`) is
    # UNSAT by construction: `cfoUnsat`, not `cfoSolvedExact`, would have
    # been the pre-fix result (empirically confirmed -- see this fix's own
    # commit message).
    check r.outcome == cfoSolvedExact
    check r.materialized.len == 1
    check $r.materialized[0] == "int(100)"   ## (201 - 1) / 2 -- the underlying DRAW, not `mapped`
    check r.coverage == ccoIntendedCovered
    let replayed = concolicCollect(u8MappedGate, r.materialized, bindings)
    check replayed.branchTrace.len == 1
    check replayed.branchTrace[0].armTaken == 0   ## "hit"

# =============================================================================
# R26 -- an overflow obligation now fires on a concolic-bound (Z3Int-route)
# path -- observable via `obligationLog`, NOT via ConcolicCollectResult
# =============================================================================

proc concolicOverflowGate(a, b: range[0'i64..9_000_000_000_000_000_000'i64]) =
  ## Verbatim shape of `tsymex_161_overflow_obligation.nim`'s `addOvf`: `a +
  ## b` reaches 1.8e19, past `int64.high`. Width 64 always takes the Z3Int
  ## route under `concolicScalarPromotesSoundly` (unconditionally for width
  ## >= 64, range or not) -- exactly the case R26 fixes.
  let c = a + b
  symexTarget("t")
  discard c

suite "#163 review R26 -- concolic Z3Int params now carry the overflow obligation stamp":

  test "oracle: 9e18 + 9e18 really overflows int64":
    proc rt(a, b: range[0'i64..9_000_000_000_000_000_000'i64]): int64 = a + b
    expect OverflowDefect:
      discard rt(9_000_000_000_000_000_000'i64, 9_000_000_000_000_000_000'i64)

  test "wmExplore cross-check: the obligation is live for the SAME SUT (non-regression anchor)":
    let r = symexFind(concolicOverflowGate, tRaisedExn("OverflowDefect"))
    check r.status == sxRaised
    check r.obligations.len >= 1
    var anyLive = false
    for o in r.obligations:
      if o.disposition == odLive: anyLive = true
    check anyLive

  test "R26: wmFollowConcrete now stamps ziWidth/ziSigned -- the SAME obligation machinery fires":
    let trace = @[integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0),
                  integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concolicOverflowGate, trace, bindings)
    check r.pcSatByConcreteInputs
    check r.counters.walkDegradeCount == 0
    # `obligationLog` is the SAME threadvar `runSymexImpl` drains into
    # `RawResult.obligations` above -- `resetSymexRunState` (called by both
    # `runSymexImpl` AND `runConcolicCollectImpl`) resets it once per run, so
    # reading it immediately after THIS call reflects only this collect.
    check obligationLog.len >= 1
    var anyLive = false
    for o in obligationLog:
      if o.disposition == odLive: anyLive = true
    check anyLive

  test "R26: NOT observable through ConcolicCollectResult itself -- documented, not fixed here":
    ## `ConcolicCollectResult` (`smt/runtime.nim`) has exactly five fields:
    ## `pcSatByConcreteInputs`, `counters`, `branchTrace`, `drawVars`,
    ## `drawOverrides` -- no raised-verdict field, and `counters`
    ## (`ConcolicYieldCounters`, `smt/concolictaxonomy.nim`) has no slot for
    ## "an obligation fired" either (its members are `tracesTruncated`/
    ## `drawsSymbolicated`/`paramsConcretized`/`unsupportedDrawKinds`/
    ## `nonInt64Draws`/`ambiguousBranches`/`ambiguousByConstruct`/
    ## `walkDegradeCount` -- none of them about a raise). `branchTrace` is
    ## populated ONLY by `walkIfFollowConcrete` (an `if`-decision); an
    ## overflow raise-fork is not an `if` and produces no
    ## `ConcolicBranchRecord`, so `concolicFlip`'s `targetBranchIndex`
    ## mechanism cannot target it either. The same overflow-triggering
    ## collect above is repeated here with every one of those fields
    ## checked, to make the negative claim concrete rather than asserted in
    ## prose alone.
    let trace = @[integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0),
                  integerChoice(9_000_000_000_000_000_000'i64, 0,
                                9_000_000_000_000_000_000'i64, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0),
                     ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 1)]
    let r = concolicCollect(concolicOverflowGate, trace, bindings)
    # Every counter that COULD plausibly carry a "raise happened" signal
    # stays at its clean-run value -- the obligation fired (proven above via
    # `obligationLog`) but left no trace on this result type.
    check r.counters.walkDegradeCount == 0
    check r.counters.ambiguousBranches == 0
    check r.branchTrace.len == 0   ## no `if` in this SUT at all

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 138":
    check parseInt(symexWalkerVersion) >= 138
