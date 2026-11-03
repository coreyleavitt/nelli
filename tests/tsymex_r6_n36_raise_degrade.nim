## N36 (round-6 fix round 4) -- closing the raw-raise-in-lower CLASS (N31's
## root cause, generalized; ADR-0023/SND-3) -- walker v101.
##
## ---- The class -------------------------------------------------------------
## N31 fixed ONE instance: `iekStrSubstr`'s CR-17 slice-bound decline raised a
## classified error carrier directly. A raw `raise` of a classified-decline
## error carrier, executed in code reached from inside nested `walkBlock`
## frames, is SILENTLY LOST by Nim's C-backend goto-exception model -- walk()
## returns as-if-complete, `w.sawUnknown` stays false, and the default-to-
## UNSAT fallback produces a wrong verdict on a reachable target. A round-4
## spot-check found 14+ further live instances of the SAME shape.
##
## ---- The fix ----------------------------------------------------------------
## STRING FAMILY (runtime_strings.nim): rather than hand-convert `lowerStrArm`'s
## ~18 individual raw-raise sites, a single CHOKEPOINT wrap at `lower`'s
## `lowerStrArm(env, e)` call site (`runtime.nim`, `degradeStrArm`) catches
## every classified carrier `lowerStrArm` can raise and converts to the SAME
## in-band degrade idiom `iekStrSubstr`'s N31 fix established. Sound because
## the unwind from ANY raise inside `lowerStrArm` to this catch crosses ONLY
## plain proc frames (never a `walkBlock`) -- see `degradeStrArm`'s own doc
## comment for the full argument.
## `isVariantReassign` (runtime.nim): the `defaultZero` call is now wrapped
## `try/except ValueError, SymexRefUnresolvedError`, matching its two
## pre-existing correctly-wrapped siblings (the `isCall`/`applyClosureGround`
## implicit-result-fallthrough zero-default binds).
## `isIndex` (runtime.nim): its two raw declines (unsupported Table value
## type; unsupported receiver kind) now degrade in-band at their own call
## site, matching the sibling `isUnsupportedFieldPlaceholder` decline already
## in the SAME arm.
##
## ---- Empirical nesting-depth finding (this slice, container-confirmed) -----
## A SINGLE nested `block:` is NOT always sufficient to reproduce the C-backend
## loss -- the split-family shape (section 2) needed a `block:` CONTAINING A
## WHILE LOOP (matching N31's own repro shape: a scan loop wrapped in a
## `block:`) before the raw raise was actually lost; a bare `block:` around a
## single non-looping statement let the raise reach `runSymex`'s specific
## handler correctly even pre-fix (confirmed by direct instrumentation this
## slice, reverted before landing -- N31 precedent). Every RED pin below uses
## the loop-in-block shape once confirmed necessary; where a lighter shape
## already reproduced the loss (section 1's pair-loop, which is a `block:`
## wrapping a `while` by construction), the lighter shape is kept.
##
## ---- RED evidence (stash method, all confirmed this slice) ------------------
## `git stash push -- src/nelli/smt/runtime.nim src/nelli/smt/runtime_strings.nim
## src/nelli/smt/canonicalize.nim`, rebuild, run, record, `git stash pop`:
##   section 1 (optregion, block):      PRE-FIX sxUnsat/0 errors (WRONG,
##                                       silently lost) -> POST-FIX sxUnknown
##                                       (honest). CONFIRMED RED->GREEN.
##   section 1 (optregion, no-block):   PRE-FIX sxUnknown (honest, reached the
##                                       specific handler) -> POST-FIX sxUnknown
##                                       (same). Already-honest, unaffected.
##   section 2 (split, loop-in-block):  PRE-FIX sxUnsat/0 errors (WRONG) ->
##                                       POST-FIX sxUnknown (honest). CONFIRMED
##                                       RED->GREEN.
##   section 2 (split, no-block):       PRE-FIX sxUnknown (honest) -> POST-FIX
##                                       sxUnknown (same). Unaffected.
##   section 3 (float reassign, via a
##   plain proc-call frame, NO explicit
##   `block:` -- see section 3's own
##   honesty note for why):             PRE-FIX sxUnknown/`weInternalWalkerFault`
##                                       (honest but GENERICALLY classified --
##                                       the catch-all caught it, meaning a
##                                       single call-frame's nesting was NOT
##                                       sufficient to reproduce the true loss
##                                       either) -> POST-FIX sxUnknown/
##                                       `feUnsupportedOp` (properly
##                                       classified). A real, demonstrable
##                                       improvement, but a CLASSIFICATION
##                                       fix for this specific shape, not a
##                                       wrong-verdict fix -- reported
##                                       honestly, not oversold.
##
## ---- A NEW pre-existing bug found (NOT part of this class, NOT fixed here) --
## Wrapping `isVariantReassign` (a discriminator reassignment, `v.kind = X`)
## itself, or a call that performs one, inside an explicit `block:` produces a
## spurious `sxUnknown`/`weInternalWalkerFault` with ZERO classified errors --
## reproduced even for a FULLY-BACKED arm (no degrade of any kind involved,
## every field is `itInt`) and confirmed identical BOTH pre- and post- this
## slice's fix (i.e. genuinely orthogonal to the raw-raise-in-lower class).
## This is why section 3's RED pin below uses a plain proc-call frame instead
## of an explicit `block:` -- the `block:` shape was tried FIRST and hit this
## unrelated confound instead of exercising the raise-loss hazard at all.
## Flagged here for a future round; NOT this slice's finding to fix or
## further root-cause (out of the raw-raise-in-lower class entirely).
##
## ---- Shapes NOT constructible from valid DSL surface this slice -----------
## `requireStr` (section 5) and `isIndex`'s two declines (section 6) -- see
## each section's own honesty note. The MECHANISM argument (identical call
## path / identical in-band idiom as the four site families empirically
## exercised above) is relied on instead, per the class description's own
## allowance.
##
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_r6_n36_raise_degrade_d`, `tsymex_r6_n36_raise_degrade_b`,
## `tsymex_r6_n36_raise_degrade_c`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 66 s).
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime

# =============================================================================
# 1. iekStrInOptionRegion (the :791 copy) -- pair-loop-idiom BV-bound shape.
#    Mirrors N31's own two-hop literal-seeded-local trick: `collectIntOffsetParams`
#    only traces a formal-parameter ROOT; a LOCAL seeded from another LOCAL
#    (not itself a literal) evades both that pass and the one-hop
#    `collectIntOffsetLiteralLocals` check, so the pair-loop's own counter `i`
#    allocates the type-driven BV64 default instead of svInt -- `iekStrInOptionRegion`
#    then sees a BV-sorted `start` operand and hits its CR-17-style decline.
#    This form is ONLY ever emitted by `tryRecognizePairLoopIdiom`'s closed-form
#    replacement (its own doc comment), never from ordinary source -- so this
#    IS the DSL-surface construction of that copy.
# =============================================================================

type ScanError = object of CatchableError

proc readCStringOptN36(s: string, offset: int): (string, int) =
  ## Byte-identical shape to N21's own `readCStringOpt` -- the B4-recognized
  ## readCString idiom `tryMatchPairLoopIdiomShape` requires as the pair
  ## loop's chained helper.
  var acc = ""
  var i = offset
  while i < s.len:
    if s[i] == '\0':
      return (acc, i + 1)
    acc.add s[i]
    i.inc
  raise newException(ScanError, "unterminated")

proc sutOptionRegionBlockAfter(s: string) =
  block:
    var localOffset = 0        ## literal-seeded LOCAL (one hop from a literal)
    var i = localOffset        ## two-hop: seeded from a local, not a literal or
                                ## a formal param directly -- defeats BOTH
                                ## int-offset tracing passes.
    var pairs: seq[(string, string)] = @[]
    while i < s.len:
      let (key, p1) = readCStringOptN36(s, i)
      if key.len == 0:
        break
      let (val, p2) = readCStringOptN36(s, p1)
      pairs.add((key, val))
      i = p2
  symexTarget("n36_optregion_block_after")

suite "symex N36 -- iekStrInOptionRegion BV-bound decline inside a block:":

  test "N36-1: post-block target reachable honestly (sxUnknown), never a false sxUnsat":
    ## Ground truth: the empty string `s == \"\"` never enters the loop and
    ## the block completes trivially -- concretely reachable regardless of
    ## region-membership machinery. PRE-FIX (stash-confirmed): sxUnsat with
    ## ZERO errors -- the decline's raise is lost inside the block,
    ## `w.sawUnknown` never set, default-to-UNSAT fires for a concretely
    ## reachable target. POST-FIX: honest classified sxUnknown (this shape's
    ## own fallback branch separately hits `beBudgetExhausted` k-unroll and
    ## the SAME `iekStrSubstr`/`iekStrInOptionRegion` BV-bound declines the
    ## fallback's own closed forms reach -- multiple honest reasons, never a
    ## silent completion).
    symexTargetSolveStats = default(typeof(symexTargetSolveStats))
    let r = symexFind(sutOptionRegionBlockAfter, tLabel("n36_optregion_block_after"))
    # RFC-0005 S8y: the suite's runtime floor, by count (never wall time).
    checkpoint "S8y budgetOut=" & $symexTargetSolveStats.budgetOut &
               " declined=" & $symexTargetSolveStats.declined &
               " slowSat=" & $symexTargetSolveStats.slowSat &
               " units=" & $symexTargetSolveStats.units
    # RFC-0005 S8ag: the one-character `str.indexof` split finds a model for
    # every exit hit S8y saw run out (N36-1's five-iteration solves), and a
    # tainted SAT after half its budget bounds later hits as a budget-out
    # does: no target-hit solve runs out of budget, at most one is slow,
    # and the walk's target solves stay under two 20M budgets (measured
    # 24-27M on Z3 5.1, 3.6-4.7M on 4.13.4; 31-33M with a budget-out
    # before).
    check symexTargetSolveStats.budgetOut == 0
    check symexTargetSolveStats.slowSat <= 1
    check symexTargetSolveStats.units < 40_000_000
    var sawOptRegionKind = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedStringOp and "iekStrInOptionRegion" in e.msg:
        sawOptRegionKind = true
    check r.status == sxUnknown
    check sawOptRegionKind
