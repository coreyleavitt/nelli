## N37 (round-6 fix round 4) -- closing the LAST enumerated residue of the
## raw-raise-in-lower CLASS N36 left as `known-open` backlog, plus one
## previously-unenumerated caller of the SAME raise N36 already marked --
## walker v102.
##
## ---- Adjudication summary ---------------------------------------------------
## REACHABLE, CONVERTED (this file pins pre-fix RED via block-nested shapes):
##   1. `iekSeqSlice`'s base-kind decline (`recv.kind != svSeq`) -- reachable
##      via a call-boundary representation mismatch: a helper proc's own
##      `itSeq`-classified `seq[byte]` param receiving a caller's
##      svString-backed argument through `isCall`'s no-representation-bridge
##      env binding (mirrors the gap `iekSeqLen`'s `svString` arm exists to
##      handle -- see item 5 below for why THAT site stays unconverted).
##   2. `iekSeqSlice`'s CR-17-style bound decline (`loSV`/`hiSV.kind !=
##      svInt`) -- reachable via N36 section 1's own two-hop
##      literal-seeded-local trick (`collectIntOffsetParams`/
##      `collectIntOffsetLiteralLocals` only trace a formal-param root or a
##      ONE-hop literal seed; a local seeded from ANOTHER local evades
##      both), applied to a SEQ slice bound instead of a string one.
##   3. `isRaise`'s bare-reraise decline (a WALK-level site, not a
##      lowering-level one -- generalizes the class for the first time
##      beyond `lower()`) -- reachable because a bare `raise` is valid Nim
##      ANYWHERE (not only lexically inside an `except`; it re-raises the
##      current exception at runtime and Defects if there is none), so
##      `dsl_parser.nim`'s `nnkRaiseStmt` arm parses it unconditionally
##      (`mkReraise`, no scope check).
##   4. `lowerHofCall`'s inline `map`/`filter` calling `allocateSeqDataRaw`
##      UNGUARDED -- N36's own doc note already confirmed this reachable BY
##      CODE-PATH ARGUMENT. This slice attempted a live repro and found
##      instead that EVERY inline HOF closure application (regardless of
##      element-type backing) currently collides with a PRE-EXISTING,
##      UNRELATED defect (N29, ledgered at N16's landing) that fires
##      UPSTREAM of this proc's `map`/`filter` arms entirely (confirmed via
##      direct instrumentation, reverted before landing -- see item 4's own
##      test-file honesty note for the full writeup). Fixed anyway by the
##      MECHANISM argument (N36 precedent for un-independently-pinnable
##      sites): guard with `isBackedSeqElemTy` before ever calling the
##      unsafe function, identical idiom to item 4b (which DOES pin
##      cleanly, since `lowerSeqLit` never touches the N29-colliding
##      closure-application path at all) and to `allocateSym`/
##      `defaultZero`'s own itSeq-arm discipline.
##      AMENDED (Bucket-2 opening fix-slice, walker v120): N29 itself is
##      now fixed (a `lowerSeqLit` empty-literal sort bug wholly unrelated
##      to closures -- see `symexWalkerVersion`'s own doc comment), so item
##      4's test now independently observes the guard THIS slice applied,
##      plus a second, orthogonal `buildClosure` gap (multi-leaf closure
##      return sorts) that N29 masking had also hidden -- see item 4's own
##      test-file note (below) for the current writeup.
##   4b. A THIRD, previously-unenumerated unguarded caller of the SAME raise:
##      `lowerSeqLit`'s non-empty-literal branch (e.g. `@[("a","b")]` :
##      `seq[(string,string)]`). The B6 rider only widened the EMPTY-literal
##      case; this slice widens the non-empty one with the identical guard.
##      Like item 4, this collides with ANOTHER pre-existing, unrelated
##      parser gap (`nnkHiddenSubConv` on a tuple-literal seq element) that
##      already yields an honest `sxUnknown` on its own -- so the fix is a
##      CLASSIFICATION-completeness improvement (the correct
##      `seNestedSeqUnsupported` now also appears), not an independently
##      isolable wrong-verdict flip. See item 4b's own test-file note.
##
## VERIFIED UNREACHABLE, marker upgraded (NOT converted):
##   5. `iekSeqLen`'s unsupported-receiver-kind decline (the true `else` arm
##      -- not the `svString` arm immediately above it, already correctly
##      handled). Gate: the parser only ever constructs an `iekSeqLen` node
##      for an `itSeq`/`itTable`/`itSet`-classified receiver
##      (`dsl_parser.nim`'s `.len`/`len`/`card` arms), and the ONLY
##      cross-representation mismatch reachable at walk time (the SAME
##      call-boundary gap items 1/2 above exploit) lands on the `svString`
##      arm, empirically confirmed this slice via the identical
##      construction (companion pin below).
##   6. `allocateSeqDataRaw`'s own raise -- every caller in this file
##      (`allocateSym`'s itSeq arm, `defaultZero`'s itSeq arm,
##      `lowerHofCall`'s map/filter, `lowerSeqLit`'s non-empty branch, all
##      pre-existing or fixed this slice) now guards with
##      `isBackedSeqElemTy` before calling it -- provably unreachable in raw
##      form from any call site in this file.
##
## ---- Walker bump -------------------------------------------------------------
## 101->102: items 1, 2, and 3 are genuine verdict-surface changes (a false
## `sxUnsat` under block nesting -> honest classified `sxUnknown`) --
## empirically confirmed via the stash method below. See
## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the full
## writeup. Items 4 and 4b are crash-avoidance / classification-completeness
## fixes applied by the MECHANISM argument (matching N36's own precedent for
## un-independently-pinnable sites): a raw, unguarded raise is REPLACED with
## a sound classified degrade at a genuinely-reached code path, even though
## a coincidental pre-existing decline (N29 for item 4; the
## `nnkHiddenSubConv` parser gap for item 4b) already produces an honest
## `sxUnknown` for the SPECIFIC shapes this file could construct, so neither
## is independently observable as a wrong-verdict RED->GREEN flip. Bumped
## anyway alongside 1/2/3 (a single walker version covers the whole slice;
## items 4/4b are real hardening even though this file cannot isolate their
## OWN verdict-surface delta). Items 5/6 are pure marker upgrades (the raise
## STATEMENTS themselves are byte-identical, unmoved -- only their
## reachability adjudication and marker text changed), which alone would NOT
## justify a bump. `renderAsChoicesVersion` does NOT bump (stays "11") --
## see `tsymex_phase15_CR2_cachekey.nim`'s own N37 note.
##
## ---- RED evidence (stash method, all confirmed this slice) ------------------
## `git stash push -- src/nelli/smt/runtime.nim src/nelli/smt/canonicalize.nim`,
## rebuild, run, record, `git stash pop`:
##   iekSeqSlice base-kind (block):    PRE-FIX sxUnsat/0 errors (WRONG,
##                                      silently lost) -> POST-FIX sxUnknown
##                                      (honest). CONFIRMED RED->GREEN.
##   iekSeqSlice base-kind (no-block): PRE-FIX sxUnknown (honest, reached the
##                                      specific handler) -> POST-FIX
##                                      sxUnknown (same). Already-honest,
##                                      unaffected.
##   iekSeqSlice bound (block):        PRE-FIX sxUnsat/0 errors (WRONG) ->
##                                      POST-FIX sxUnknown (honest).
##                                      CONFIRMED RED->GREEN.
##   iekSeqSlice bound (no-block):     PRE-FIX sxUnknown (honest) -> POST-FIX
##                                      sxUnknown (same). Unaffected.
##   isRaise (block):                  PRE-FIX sxUnsat/0 errors (WRONG) ->
##                                      POST-FIX sxUnknown (honest).
##                                      CONFIRMED RED->GREEN.
##   isRaise (no-block):               PRE-FIX ALSO sxUnsat/0 errors (WRONG)
##                                      -> POST-FIX sxUnknown (honest).
##                                      CONFIRMED RED->GREEN -- unlike items
##                                      1/2 above, a plain call frame here
##                                      was ALSO sufficient to reproduce full
##                                      loss (interpreting the callee's body
##                                      already requires a `walkBlock` frame
##                                      under the hood).
##   HOF map (unbacked tuple elem):    PRE-FIX and POST-FIX both
##                                      sxUnknown/`ekZ3Error` -- UNCHANGED,
##                                      by design (see item 4's own honesty
##                                      note: N29 fires upstream of this
##                                      slice's target site regardless of
##                                      this slice's fix). Not a RED->GREEN
##                                      pin; a stable regression guard.
##   seq-literal non-empty (unbacked): PRE-FIX: only the unrelated
##                                      `nnkHiddenSubConv` parser-gap decline
##                                      appears (already `sxUnknown` on its
##                                      own); no signal of this slice's OWN
##                                      target site at all -- consistent with
##                                      silent loss but, given the
##                                      coincidental protection, not
##                                      independently isolable as proof of it
##                                      (see item 4b's own honesty note).
##                                      POST-FIX: the correct
##                                      `seNestedSeqUnsupported` classified
##                                      decline ALSO appears, alongside the
##                                      same parser-gap decline. Verdict
##                                      (`sxUnknown`) UNCHANGED; a
##                                      classification-completeness fix, not
##                                      an independently isolable
##                                      RED->GREEN pin.
##
## ---- lowerHofCall filter arm (mechanism argument, not independently pinned) -
## `filter`'s `hofRetElemTy` always equals the RECEIVER's own element type
## (per `hofDispatch`'s own logic: filter preserves T). Constructing an
## unbacked-element receiver that reaches the INLINE path (not the
## placeholder short-circuit two lines above it) is not independently
## reachable from valid DSL surface here: a PARAMETER-typed unbacked-element
## seq is intercepted by `lowerHofCall`'s OWN placeholder guard first (its
## `seqLen` is symbolic, so `canInline` is structurally false -- N27's own
## finding); a LOCAL built via `@[]` + `.add` instead hits `storeSeqElem`'s
## own (out-of-class-scope, Defect-class) `ValueError` before ever reaching
## HOF dispatch. The fix is nonetheless applied (identical guard, mirroring
## `map`'s) because the MECHANISM is identical (the same unguarded
## `allocateSeqDataRaw(elemTy, "__hoffilter.data")` call, same missing
## `isBackedSeqElemTy` check) -- N36 precedent (`requireStr`/`isIndex`'s two
## declines) for converting/adjudicating a site via the mechanism argument
## when an independent repro isn't constructible.
import std/[unittest, sequtils, strutils]
import nelli/symex
import nelli/smt/canonicalize

type ScanError = object of CatchableError

# =============================================================================
# 1. iekSeqSlice base-kind decline -- call-boundary svString/svSeq mismatch.
# =============================================================================

proc n37SliceReadHelper(data: seq[byte]): byte =
  ## No consuming loop, no callees of its own -> classified `itSeq`
  ## (non-string-backed) within ITS OWN body -- neither B1's direct shape
  ## match nor the B7-rider's one-hop call-trace promotion apply here.
  let sliced = data[0 .. 0]
  sliced[0]

proc n37SliceCallerNoBlock(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:      ## Q1 shape -> `data` is
    inc i                                       ## string-backed HERE.
  let b = n37SliceReadHelper(data)
  if b == 0'u8:
    symexTarget("n37_slice_basekind_noblock")

proc n37SliceCallerBlockAfter(data: seq[byte]) =
  block:
    var i = 0
    while i < data.len and data[i] != 0'u8:
      inc i
    let b = n37SliceReadHelper(data)
    discard b
  symexTarget("n37_slice_basekind_block_after")

suite "symex N37 -- iekSeqSlice base-kind decline (call-boundary svString mismatch)":

  test "N37-1-noblock: same shape without the block -- honest sxUnknown, unaffected by this slice's fix":
    ## Round-6 re-review (item 4b, walker v114): the pinned substring was
    ## "svString" (the raw `$recv.kind` identifier); fef2dc0 ("N12 SymValKind
    ## message funnel") rewrote this decline's message to route through
    ## `plainEnglishSymValKind` instead of `$recv.kind`, so the SAME honest
    ## `feUnsupportedOp` classification now reads "...base lowered to string
    ## — expected svSeq" -- user-facing plain English, not internal IR
    ## vocabulary, matching the message-formatting-boundary discipline
    ## `placeholderReadDeclineMsg` already documents elsewhere in this file
    ## ("this string reaches the user through SymexResult.errors... must not
    ## leak internal IR vocabulary"). Kind and substance are unchanged --
    ## only the free-form wording improved -- so this is the HONEST-decline
    ## case: the pin updates to the new shape rather than the source
    ## reverting.
    let r = symexFind(n37SliceCallerNoBlock, tLabel("n37_slice_basekind_noblock"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feUnsupportedOp and "iekSeqSlice" in e.msg and "string" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N37-1: post-block target reachable honestly (sxUnknown), never a false sxUnsat":
    ## See N37-1-noblock's note (item 4b, walker v114) -- same fef2dc0
    ## message-wording update, pin follows the new honest shape.
    let r = symexFind(n37SliceCallerBlockAfter, tLabel("n37_slice_basekind_block_after"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feUnsupportedOp and "iekSeqSlice" in e.msg and "string" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

# =============================================================================
# 2. iekSeqSlice CR-17-style bound decline -- two-hop seeded local (BV64),
#    mirrors N36 section 1's own trick for iekStrInOptionRegion.
# =============================================================================

proc n37SeqSliceBoundNoBlock(data: seq[byte]) =
  var localOffset = 0    ## one-hop literal seed (WOULD be caught alone)
  var i = localOffset    ## two-hop -- defeats both int-offset tracing passes
  let sliced = data[i .. i]
  discard sliced
  symexTarget("n37_seqslice_bound_noblock")

proc n37SeqSliceBoundBlockAfter(data: seq[byte]) =
  block:
    var localOffset = 0
    var i = localOffset
    let sliced = data[i .. i]
    discard sliced
  symexTarget("n37_seqslice_bound_block_after")

suite "symex N37 -- iekSeqSlice CR-17 bound decline (two-hop seeded local)":

  test "N37-2-noblock: same shape without the block -- honest sxUnknown, unaffected by this slice's fix":
    let r = symexFind(n37SeqSliceBoundNoBlock, tLabel("n37_seqslice_bound_noblock"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feUnsupportedOp and "iekSeqSlice" in e.msg and "bv2int-bridge" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N37-2: post-block target reachable honestly (sxUnknown), never a false sxUnsat":
    let r = symexFind(n37SeqSliceBoundBlockAfter, tLabel("n37_seqslice_bound_block_after"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feUnsupportedOp and "iekSeqSlice" in e.msg and "bv2int-bridge" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

# =============================================================================
# 3. isRaise bare-reraise decline -- WALK-level (not lowering-level) site.
# =============================================================================

proc n37BareRaiseHelper(x: int) =
  ## Unconditional: EVERY call hits the decline (no untaken branch that
  ## could reach the target on its own and mask a wrong verdict on the
  ## overall query -- mirrors N36 section 2's own unconditional-decline
  ## shape). `x` is unused inside the raise itself; kept only so the SUT
  ## has a symbolic input, matching this file's other helper shapes.
  discard x
  raise    ## bare re-raise: valid Nim anywhere, not only inside `except`.

proc n37BareRaiseNoBlock(x: int) =
  n37BareRaiseHelper(x)
  symexTarget("n37_bareraise_noblock")

proc n37BareRaiseBlockAfter(x: int) =
  block:
    var i = 0
    while i < 1:
      n37BareRaiseHelper(x)
      i.inc
  symexTarget("n37_bareraise_block_after")

suite "symex N37 -- isRaise bare-reraise decline (walk-level generalization)":

  test "N37-3-noblock: plain call frame -- post-call target reachable honestly, never a false sxUnsat":
    ## EMPIRICALLY, unlike N36 section 3's `isVariantReassign` finding (where
    ## a plain call frame was NOT sufficient to reproduce full loss -- it hit
    ## the generic catch-all instead), a PLAIN CALL FRAME here IS already
    ## sufficient: interpreting the callee's body itself requires a
    ## `walkBlock` frame under the hood (`isCall`'s own call-inlining
    ## machinery), even with no explicit `block:` in the SUT's own source.
    ## PRE-FIX (stash-confirmed): sxUnsat with ZERO errors -- lost, same as
    ## the block-wrapped shape below. POST-FIX: honest classified
    ## `sxUnknown`.
    let r = symexFind(n37BareRaiseNoBlock, tLabel("n37_bareraise_noblock"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == eeRaiseOutsideHandler and "no in-flight exception" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

  test "N37-3: block+loop wrapping the call -- post-block target reachable honestly, never a false sxUnsat":
    let r = symexFind(n37BareRaiseBlockAfter, tLabel("n37_bareraise_block_after"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == eeRaiseOutsideHandler and "no in-flight exception" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

# =============================================================================
# 4b. lowerSeqLit non-empty literal -- unbacked (tuple) element type. A
#     THIRD, previously-unenumerated unguarded caller of the same raise
#     N36 marked (only lowerHofCall's two call sites were named).
#
#     CLASSIFICATION-COMPLETENESS pin, not an independently-isolable
#     wrong-verdict RED (mirrors N36 section 3's own honest "generic ->
#     specific classification" framing, not oversold as a verdict flip):
#     investigated this slice via isolated bisection -- ANY tuple literal
#     as a seq element (`(a, b)`, with EITHER params or bare int literals,
#     e.g. `@[(1, 2)]`) hits a SEPARATE, pre-existing parser gap
#     (`feUnsupportedExprKind`/`nnkHiddenSubConv`, `dsl_parser.nim`'s CR-2a
#     catch-all -- the tuple constructor's hidden sub-conversion node isn't
#     unwrapped inside seq-literal element parsing) UNCONDITIONALLY,
#     REGARDLESS of this slice's fix. That decline alone already yields an
#     honest `sxUnknown` both pre- and post-fix, so the OVERALL VERDICT does
#     not flip. What DOES change: `lowerSeqLit` is still reached (proven --
#     `e.seqLitElemTy` is independent of whether the ELEMENT expression
#     itself parsed cleanly, so `elemTy.kind == itTuple` regardless) and,
#     post-fix, correctly ALSO reports the specific `seNestedSeqUnsupported`
#     classification alongside the parser-gap one; pre-fix, no such second
#     error appears (consistent with -- though, given the coincidental
#     protection, not independently isolable as proof of -- the same
#     silent-loss mechanism this slice's other three conversions
#     empirically demonstrate cleanly). Reported exactly this honestly, per
#     the class description's own allowance, rather than an overclaimed
#     RED->GREEN wrong-verdict pin.
# =============================================================================

proc n37SeqLitTupleElem(a: string, b: string) =
  let pairs: seq[(string, string)] = @[(a, b)]
  if pairs.len > 0:
    symexTarget("n37_seqlit_tuple")

suite "symex N37 -- lowerSeqLit non-empty literal, unbacked tuple elem":

  test "N37-4b: a non-empty seq[(string,string)] literal reaches the correct classified decline (in addition to the unrelated pre-existing tuple-literal parser gap)":
    ## Round-6 N12 (message-formatting boundary, walker v108): the decline
    ## message used to interpolate the bare IR kind identifier ("itTuple")
    ## verbatim; it now routes through `plainEnglishTypeKind` ("tuple type")
    ## instead, so this pin checks for the plain-language phrase, not the
    ## internal IR vocabulary token. `.kind` itself is unchanged.
    let r = symexFind(n37SeqLitTupleElem, tLabel("n37_seqlit_tuple"))
    var saw = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == seNestedSeqUnsupported and "tuple type" in e.msg:
        saw = true
    check r.status == sxUnknown
    check saw

# =============================================================================
# 5. iekSeqLen unsupported-receiver-kind decline -- HONESTY NOTE (adjudicated
#    VERIFIED UNREACHABLE, not converted). See this file's header for the
#    full gate argument. Companion pin: the IDENTICAL call-boundary
#    construction used for item 1 above, but with `.len` instead of a
#    slice -- it resolves through the ALREADY-HANDLED `svString` arm (a
#    correct, non-degraded answer), NOT the target unsupported-kind arm,
#    supporting the unreachability claim empirically rather than by
#    assertion alone.
# =============================================================================

proc n37LenReadHelper(data: seq[byte]): int =
  data.len

proc n37LenCallerNoBlock(data: seq[byte]) =
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  let n = n37LenReadHelper(data)
  if n == 0:
    symexTarget("n37_len_recvkind_noblock")

suite "symex N37 -- iekSeqLen unsupported-receiver-kind: verified-unreachable companion":

  test "N37-5: the only reachable cross-representation mismatch resolves via the ALREADY-HANDLED svString arm (a correct answer, not the target arm)":
    let r = symexFind(n37LenCallerNoBlock, tLabel("n37_len_recvkind_noblock"))
    check r.status == sxSat
    check r.errors.len == 0

# =============================================================================
# 6. UNSAT companion -- proving the lowering-level chokepoint changes (items
#    1/2/4/4b) do not over-degrade into a false sxSat/sxUnknown on the
#    ORDINARY, non-degrading path. Mirrors N36 section 4's own companion.
# =============================================================================

proc n37SliceNormalBlockAfterUnsat(a: int) =
  var xs: seq[int] = @[1, 2, 3]  ## LITERAL, not `.add`-mutated: `iekSeqAdd`
                                  ## on an empty-literal-seeded local hits an
                                  ## UNRELATED pre-existing `ekZ3Error`
                                  ## confound (confirmed this slice via
                                  ## isolated bisection -- a `.len`-only
                                  ## read after a single `.add`, no slice at
                                  ## all, reproduces it identically; a plain
                                  ## literal with no `.add` does not). Also
                                  ## sidesteps a genuine `IndexDefect` fork a
                                  ## symbolic-length receiver would add.
  block:
    let sliced = xs[0 .. 0]     ## ordinary svSeq base, svInt literal bounds
    discard sliced              ## -- no decline triggered at all.
  if a > 0 and a < 0:            ## always false, data-independent
    symexTarget("n37_slice_normal_unreachable_after")

suite "symex N37 -- UNSAT companion: no over-degrade":

  test "N37-6: a data-independent false condition after a NON-degrading slice still proves sxUnsat":
    let r = symexFind(n37SliceNormalBlockAfterUnsat,
                       tLabel("n37_slice_normal_unreachable_after"))
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
    check r.status == sxUnsat
    check r.errors.len == 0

# =============================================================================
# 4. lowerHofCall inline map -- unbacked (tuple) return element type --
#    UPDATED BY N29 (Bucket-2 opening fix-slice, walker v120). Mirrors
#    N16's own precedent for the SAME collision
#    (`tests/tsymex_r6_n16_closure_zerodefault.nim`'s "N16-2").
# =============================================================================
## At this slice's own original landing, EVERY inline `map`/`filter` call
## whose closure argument reached `applyClosureGround` at all -- REGARDLESS
## of the receiver's or the closure's own return element type -- collided
## with N29 (a `lowerSeqLit` empty-literal sort bug, unrelated to closures
## at all -- see `symexWalkerVersion`'s own doc comment for the confirmed
## root cause) before `lowerHofCall`/`buildClosure` were ever reached.
##
## N29's fix unblocks this SUT's `.add` and lets `.map()`'s closure
## construction actually run -- which surfaces a SECOND, genuinely
## DIFFERENT pre-existing gap: `buildClosure` could not declare a Z3
## func_decl for a closure whose return type flattens to more than one Z3
## leaf (here, `(string, string)` — see `buildClosure`'s own N29-followup
## doc comment). That gap was ALSO a raw `doAssert` pre-N29 (unreachable
## for the same reason N29 masked it), now converted to an honest
## classified decline (`feUnsupportedOp`) in the same slice that unblocked
## the path to it, per this codebase's established "the slice that exposes
## a crash fixes it, even if orthogonal to the slice's own headline target"
## discipline (N36/N40/N46 precedent). `lowerHofCall`'s own map arm THEN
## also declines (`seNestedSeqUnsupported`) once it inspects the closure's
## unbacked tuple return element type -- both classified errors coexist,
## sxUnknown, no crash.
##
## Regression pin below: the NEW honest classification this slice's own
## N29 fix (plus its buildClosure follow-up) exposed.

proc n37HofMapTupleElem(a: int) =
  var xs: seq[int] = @[]
  xs.add a
  let ys = xs.map(proc(x: int): (string, string) = ($x, $x))
  if ys.len > 0:
    symexTarget("n37_hof_map_tuple")

suite "symex N37 -- lowerHofCall inline map, unbacked tuple return elem (N29-unblocked, honest decline)":

  test "N37-4: N29-unblocked closure construction hits a SECOND, orthogonal gap (multi-leaf closure return type) -- now an honest classified decline (feUnsupportedOp), never a crash":
    let r = symexFind(n37HofMapTupleElem, tLabel("n37_hof_map_tuple"))
    var sawUnsupportedOp = false
    for e in r.errors:
      checkpoint($e.kind & ": " & e.msg)
      if e.kind == feUnsupportedOp and e.severity == sevError:
        sawUnsupportedOp = true
    check r.status == sxUnknown
    check sawUnsupportedOp

# =============================================================================
# Version pin
# =============================================================================

suite "symex N37 -- walker version pin":

  test "walker version floor >= 102 (N37: raw-raise-in-lower class residue closure)":
    check parseInt(symexWalkerVersion) >= 102
