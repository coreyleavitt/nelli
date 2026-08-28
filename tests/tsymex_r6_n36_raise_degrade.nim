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
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

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
    let r = symexFind(sutOptionRegionBlockAfter, tLabel("n36_optregion_block_after"))
    var sawOptRegionKind = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedStringOp and "iekStrInOptionRegion" in e.msg:
        sawOptRegionKind = true
    check r.status == sxUnknown
    check sawOptRegionKind

# --- non-block companion: same shape, no `block:` wrapper -- must already be
#     an honest classified decline, unaffected by this slice's fix. ----------

proc sutOptionRegionNoBlockAfter(s: string) =
  var localOffset = 0
  var i = localOffset
  var pairs: seq[(string, string)] = @[]
  while i < s.len:
    let (key, p1) = readCStringOptN36(s, i)
    if key.len == 0:
      break
    let (val, p2) = readCStringOptN36(s, p1)
    pairs.add((key, val))
    i = p2
  symexTarget("n36_optregion_noblock_after")

suite "symex N36 -- regression: iekStrInOptionRegion no-block companion stays correct":

  test "N36-1-noblock: same shape without the block -- honest sxUnknown, same kind pre- and post-fix":
    let r = symexFind(sutOptionRegionNoBlockAfter, tLabel("n36_optregion_noblock_after"))
    var sawOptRegionKind = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seUnsupportedStringOp and "iekStrInOptionRegion" in e.msg:
        sawOptRegionKind = true
    check r.status == sxUnknown
    check sawOptRegionKind

# =============================================================================
# 2. iekStrSplit empty-sep cap-exceeded decline (join/split family) --
#    directly constructible from ordinary literal DSL code. A bare `block:`
#    around the single `let` statement was NOT sufficient to reproduce the
#    loss (confirmed this slice); a `block:` containing a WHILE LOOP (mirroring
#    N31's own repro shape) was.
# =============================================================================

proc sutSplitOversizeBlockAfter(unused: int) =
  block:
    var i = 0
    while i < 1:                        ## always runs exactly once
      let parts = "abcdefghij".split("")   ## 10 bytes > default maxSplitParts=8
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
    check r.status == sxUnknown
    check sawSplitCapKind

proc sutSplitOversizeNoBlockAfter(unused: int) =
  let parts = "abcdefghij".split("")
  discard parts
  symexTarget("n36_split_oversize_noblock_after")

suite "symex N36 -- regression: iekStrSplit no-block companion stays correct":

  test "N36-2-noblock: same shape without the block -- honest sxUnknown, same kind pre- and post-fix":
    let r = symexFind(sutSplitOversizeNoBlockAfter, tLabel("n36_split_oversize_noblock_after"))
    check r.status == sxUnknown
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

  test "N36-3: post-call target reaches an honest, PROPERLY-CLASSIFIED sxUnknown (feUnsupportedOp)":
    ## PRE-FIX (stash-confirmed): sxUnknown/weInternalWalkerFault ("ValueError:
    ## defaultZero(float): lands with F7") -- honest (not lost, not a wrong
    ## verdict) but generically classified by the outer catch-all, not the
    ## specific in-band idiom. POST-FIX: sxUnknown/feUnsupportedOp, the SAME
    ## idiom `isCall`'s and `applyClosureGround`'s pre-existing
    ## `defaultZero`-fallthrough guards already use.
    let r = symexFind(sutFloatReassignCallAfter, tLabel("n36_floatreassign_call_after"))
    check r.status == sxUnknown
    var sawProperKind = false
    var sawGenericFault = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feUnsupportedOp and "isVariantReassign" in e.msg:
        sawProperKind = true
      if e.kind == weInternalWalkerFault:
        sawGenericFault = true
    check sawProperKind
    check not sawGenericFault

proc sutFloatReassignNoBlockAfter(v: var N36FRec) =
  v.kind = n36fkB
  symexTarget("n36_floatreassign_noblock_after")

suite "symex N36 -- regression: isVariantReassign no-frame companion stays correct":

  test "N36-3-noframe: direct (non-call) reassignment -- properly classified, same kind":
    let r = symexFind(sutFloatReassignNoBlockAfter, tLabel("n36_floatreassign_noblock_after"))
    check r.status == sxUnknown
    var sawProperKind = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and "isVariantReassign" in e.msg:
        sawProperKind = true
    check sawProperKind

# =============================================================================
# 4. UNSAT companion -- proving the fix does not over-degrade into a false
#    sxSat/sxUnknown. NOTE: `w.sawUnknown` is a WHOLE-RUN flag, not scoped to
#    a specific target -- once ANYTHING on the walk degrades, EVERY target
#    query against that SUT reports sxUnknown, even one that is independently
#    provably unreachable (confirmed this slice: reusing section 2's
#    OVERSIZE-split shape here, with a data-independent-false guard after the
#    block, still reports sxUnknown, not sxUnsat -- this is the walker's
#    existing, pre-existing-and-unrelated global-taint behavior, not an
#    over-degrade bug this fix introduces). So the genuine "no over-degrade"
#    companion must use a shape that goes through the SAME `block:`-wrapped
#    `iekStrSplit` call path but does NOT trigger any decline at all (a
#    literal well under the `maxSplitParts` cap) -- proving the CHOKEPOINT
#    WRAP ITSELF (the `try/except` now sitting around every `lowerStrArm`
#    call) adds no spurious taint on the ordinary, non-degrading path. NO
#    while loop here (unlike section 2's RED repro): a k-unrollable `while`
#    loop reachable through a `block:` hits a SEPARATE, pre-existing,
#    already-documented decline class (N21's own file names it: "N20 --
#    k-unroll fallback reports beBudgetExhausted even when assumed
#    iterations fit under maxLoopUnwind" -- the walker descends into a while
#    loop's unrolled branches unconditionally and does not special-case a
#    concretely-bounded trip count) -- confirmed here too (a loop that
#    trivially runs exactly once still reported `beBudgetExhausted`) and is
#    orthogonal to this class entirely. A plain `block:` with no loop
#    sidesteps it cleanly.
# =============================================================================

proc sutSplitNormalBlockAfterUnsat(unused: int) =
  block:
    let parts = "ab".split("")   ## 2 parts, well under the cap -- no decline
    discard parts
  if unused > 0 and unused < 0:      ## always false, data-independent
    symexTarget("n36_split_normal_unreachable_after")

suite "symex N36 -- UNSAT companion: no over-degrade":

  test "N36-4: a data-independent false condition after a NON-degrading block still proves sxUnsat":
    let r = symexFind(sutSplitNormalBlockAfterUnsat,
                       tLabel("n36_split_normal_unreachable_after"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnsat
    check r.errors.len == 0

# =============================================================================
# 5. requireStr's own guard -- HONESTY NOTE (not independently pinned).
# =============================================================================
## `requireStr` (`runtime_strings.nim`) is a DEFENSIVE totality guard for a
## walker MODELING GAP (a non-svString operand reaching a string op), not a
## program-level invariant -- its own doc comment records the ONE field case
## that ever tripped it (a `char`-typed needle argument, pre-v65), which
## `needleAsStr` now bridges instead of raising. Every OTHER `requireStr`
## call site guards a RECEIVER, which -- under the current engine's
## type-correct lowering -- always allocates `svString` for a genuinely
## `string`-typed Nim value; no construction from valid, well-typed DSL
## surface was found this slice that forces a mismatched kind into a
## `requireStr` receiver check (unlike `iekStrSubstr`/`iekStrInOptionRegion`'s
## BOUND checks, which a BV-vs-Int REPRESENTATION choice can reach directly,
## independent of the operand's own Nim-level type). Reported honestly per
## the class description's own allowance ("If some shapes can't be
## constructed from the DSL surface... report that per-site honestly and
## rely on the mechanism argument") rather than forcing an artificial repro.
## The MECHANISM argument still applies in full: `requireStr`'s raise unwinds
## through the exact same plain-proc-frame path (`lowerStrArm` calling
## `requireStr` as an inlined template, in the SAME frame) that
## `degradeStrArm`'s catch already proves sound for the FOUR `lowerStrArm`-
## internal call sites pinned above and by N31 (`iekStrInOptionRegion`,
## `iekStrSplit`, `iekStrSubstr`) -- there is nothing site-specific about
## `requireStr`'s OWN unwind path that would make it behave differently.

# =============================================================================
# 6. isIndex's two declines -- HONESTY NOTE (not independently pinned).
# =============================================================================
## Both attempted DSL-surface constructions failed to reach the fixed code:
##   - Table value-type decline: a `Table[string, string]` (or any
##     non-`Table[string,int]`) reachable from a TOP-LEVEL SUT parameter --
##     directly, or nested inside an object/tuple field -- is intercepted
##     EARLIER, at PARAMETER-ALLOCATION time, by the witness-renderability
##     demotion (`demoteUnrenderableWitnessTy`, `dsl_parser.nim`; classified
##     `feUnsupportedWitnessType`, a documented Category-2-safe pre-walk
##     boundary) before `isIndex`'s runtime value-type check is ever reached
##     (confirmed this slice: both a bare `Table[string,string]` param and an
##     object-field-nested one hit `feUnsupportedWitnessType`, not
##     `seUnsupportedTableValType`). An INTERNALLY-constructed Table (not
##     derived from a witness-classified param) would sidestep this, but
##     `initTable`/bracket-assignment (`t[k] = v`) construction is not
##     parseable by this DSL subset ("node has no type" from `classifyType`,
##     confirmed this slice) -- no other construction route was found.
##   - Unsupported-receiver-kind decline: reached only when a bracket-index
##     expression's receiver lowers to something other than
##     array/seq/table/string -- structurally, Nim's OWN type checker already
##     rejects `x[i]` for any `x` that is not one of those indexable kinds
##     before the DSL macro ever sees the expression, so no valid Nim source
##     can reach this branch at all; it exists purely as an internal-
##     consistency backstop (its own comment: "a mis-classified receiver...
##     SND-4 mirror").
## Both rely on the MECHANISM argument: the SAME in-band idiom
## (`w.walkDegradeErrors`/`w.sawUnknown`/`forkPathTainted`) as the
## `isUnsupportedFieldPlaceholder` decline in this SAME `isIndex` arm, which
## IS empirically exercised by `tests/tsymex_r6_n27_hof_placeholder.nim` and
## `tests/tsymex_r6_n27_placeholder_read_audit.nim` (part of this file's own
## sweep) -- not a novel, unproven pattern.

# =============================================================================
# Version pin
# =============================================================================

suite "symex N36 -- walker version pin":

  test "walker version floor >= 101 (N36: raw-raise-in-lower class closure)":
    check parseInt(symexWalkerVersion) >= 101
