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
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_r6_n36_raise_degrade`, `tsymex_r6_n36_raise_degrade_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 66 s).

import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/runtime

# =============================================================================
# 2. iekStrSplit cap-exceeded decline (join/split family) --
#    (RFC-0005 S8g: an empty separator gives `@[s]` in Nim and never declines,
#    so the vehicle is a literal separator splitting into > maxSplitParts.)
#    directly constructible from ordinary literal DSL code. A bare `block:`
#    around the single `let` statement was NOT sufficient to reproduce the
#    loss (confirmed this slice); a `block:` containing a WHILE LOOP (mirroring
#    N31's own repro shape) was.
# =============================================================================

proc sutSplitOversizeBlockAfter(unused: int) =
  block:
    var i = 0
    while i < 1:                        ## always runs exactly once
      let parts = "a,b,c,d,e,f,g,h,i,j".split(",")   ## 10 parts > default maxSplitParts=8
      discard parts
      i.inc
  symexTarget("n36_split_oversize_block_after")

suite "symex N36 -- iekStrSplit cap-exceeded decline inside a block: (loop-in-block shape)":

  test "N36-2: post-block target reachable honestly (sxUnknown), never a false sxUnsat":
    ## PRE-FIX (stash-confirmed): sxUnsat with ZERO errors -- lost. POST-FIX:
    ## honest sxUnknown carrying seZ3StringIncomplete (plus the loop's own
    ## beBudgetExhausted, since a single-iteration k-unrollable while loop
    ## still walks through the generic loop machinery).
    let r = symexFind(sutSplitOversizeBlockAfter, tLabel("n36_split_oversize_block_after"))
    var sawSplitCapKind = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seZ3StringIncomplete and "maxSplitParts" in e.msg:
        sawSplitCapKind = true
    ## RFC-0005 S10: the label is reached unconditionally in reality and the
    ## path's only taint is `seZ3StringIncomplete` (`dcFreshSymbol`), so the
    ## candidate is replayed and CONFIRMED -> sxSat (rules 1-2 alone decide
    ## sxUnknown). Still never a false sxUnsat.
    check r.status == sxSat
    check rfc0005RawStatus == sxUnknown
    check sawSplitCapKind

proc sutSplitOversizeNoBlockAfter(unused: int) =
  let parts = "a,b,c,d,e,f,g,h,i,j".split(",")
  discard parts
  symexTarget("n36_split_oversize_noblock_after")

suite "symex N36 -- regression: iekStrSplit no-block companion stays correct":

  test "N36-2-noblock: same shape without the block -- honest sxUnknown, same kind pre- and post-fix":
    let r = symexFind(sutSplitOversizeNoBlockAfter, tLabel("n36_split_oversize_noblock_after"))
    ## RFC-0005 S10: the label is reached unconditionally in reality and the
    ## path's only taint is `seZ3StringIncomplete` (`dcFreshSymbol`), so the
    ## candidate is replayed and CONFIRMED -> sxSat (rules 1-2 alone decide
    ## sxUnknown). Still never a false sxUnsat.
    check r.status == sxSat
    check rfc0005RawStatus == sxUnknown
    var sawSplitCapKind = false
    for e in r.errors:
      if e.kind == seZ3StringIncomplete and "maxSplitParts" in e.msg:
        sawSplitCapKind = true
    check sawSplitCapKind

# =============================================================================
# 3. isVariantReassign's defaultZero float-field shape -- via a plain proc-call
#    frame (NOT an explicit `block:` -- see the header's "NEW pre-existing bug"
#    note: an explicit `block:` around a variant reassignment hits an UNRELATED,
#    pre-existing confound bug that masks this class entirely, reproduced even
#    for a fully-backed arm with no degrade involved). A plain call frame was
#    NOT sufficient to reproduce full loss either (this slice's stash test:
#    pre-fix already reached the generic catch-all, `weInternalWalkerFault`,
#    honest but poorly classified) -- so this pin demonstrates the
#    CLASSIFICATION improvement the fix delivers for this family (generic ->
#    specific), not a wrong-verdict fix. Reported exactly that way, not oversold.
# =============================================================================

type
  N36FKind = enum n36fkA, n36fkB
  N36FRec = object
    case kind: N36FKind
    of n36fkA: a: int
    of n36fkB: f: float

proc n36ReassignToFB(v: var N36FRec) =
  v.kind = n36fkB

proc sutFloatReassignCallAfter(v: var N36FRec) =
  n36ReassignToFB(v)
  symexTarget("n36_floatreassign_call_after")

suite "symex N36 -- isVariantReassign defaultZero(float) decline via a call frame":

  test "N36-3: post-call target is reached from the n36fkB branch, never a crash":
    ## PRE-FIX (stash-confirmed): sxUnknown/weInternalWalkerFault ("ValueError:
    ## defaultZero(float): lands with F7"). N36: sxUnknown/feUnsupportedOp.
    ## RFC-0005 S8f (walker 154): a reassignment no longer zero-initialises
    ## (Nim raises `FieldDefect` on a branch change and keeps the fields on
    ## `n36fkB -> n36fkB`), so no `defaultZero` is reached: the target is a
    ## clean sxSat whose witness starts on `n36fkB`.
    let r = symexFind(sutFloatReassignCallAfter, tLabel("n36_floatreassign_call_after"))
    check r.status == sxSat
    var sawGenericFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == weInternalWalkerFault:
        sawGenericFault = true
    check not sawGenericFault
    var w = N36FRec(kind: n36fkB, f: 1.5)
    sutFloatReassignCallAfter(w)
    check w.f == 1.5
