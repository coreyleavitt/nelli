## N27 (round-6 fix round 2, D1-verifier finding, HIGH-classified soundness
## hardening), walker v97 — `lowerHofCall`'s missing R1-chokepoint guard.
##
## ----------------------------------------------------------------------------
## The gap the D1/N27 finding identified
## ----------------------------------------------------------------------------
## `lowerHofCall` (`runtime.nim`, backs `.map`/`.filter`/`.fold`) read
## `concreteSeqLen(seqSV)` -> `seqSV.seqLen` with NO
## `isUnsupportedFieldPlaceholder` check anywhere in the proc -- the R1
## chokepoint (`declinePlaceholderInLower`) every OTHER `svSeq`-consuming
## `lower()` arm calls FIRST (`iekSeqLen`, `iekSeqSlice`, `iekSeqAdd`; see
## `tests/tsymex_r6_r1_placeholder_totality.nim`, which has ZERO HOF
## mentions -- this file is its missing sibling). That is a real,
## structural gap: `lowerHofCall` was the one `svSeq`-consuming arm in the
## entire file that did not inherit R1's "totality by construction"
## guarantee, and the R1 chokepoint's own doc comment is explicit that
## every such arm must call it first.
##
## ----------------------------------------------------------------------------
## HONEST empirical finding: no live wrong-verdict reproduces through
## reachable DSL syntax today (reported per this slice's own mandate to
## verify, not assume, the RED evidence)
## ----------------------------------------------------------------------------
## The D1 finding's hypothesized mechanism ("`concreteSeqLen` folds the
## placeholder's forced-0 `seqLen` to a literal 0, `canInline` picks n=0,
## the result drops the taint flag, a downstream `.len > 0` is silently
## proven `sxUnsat`") does NOT reproduce for either currently-reachable
## placeholder-receiver SOURCE, for two independent, pre-existing reasons
## -- both confirmed empirically (`symexFind` run against the pre-fix tree,
## `git stash`-isolated) before this fix landed:
##
##   1. BARE local/param/call-return receiver (`sutMapPlaceholder`/
##      `sutFilterPlaceholder` below, mirroring
##      `tsymex_r6_r1_placeholder_totality.nim`'s own `makePairs` idiom):
##      `allocateSym`'s `itSeq` placeholder arm (`runtime.nim` ~1910) sets
##      `seqLen` to a FRESH SYMBOLIC Z3 variable (`mkIntVar`), constrained
##      `== 0` only via a SEPARATE assumed path-condition
##      (`pcOut.add (lenSym == mkInt(0))`) -- the constraint is never baked
##      into the `seqLen` AST node itself. `concreteSeqLen`'s
##      `simplify(seqSV.seqLen)` is Z3's pure LOCAL term rewriter -- it does
##      not consult path-condition assertions -- so it can never fold a bare
##      symbolic variable to a numeral. `lenOpt` is therefore always `none`,
##      `canInline` is ALWAYS false regardless of `inlinePolicy` (even
##      `ipAlwaysInline` still requires `lenOpt.isSome`), and every
##      placeholder receiver of this kind was ALREADY routed to the AXIOM
##      path pre-fix. Confirmed pre-fix: `sutMapPlaceholder` -> `sxUnknown`
##      via `ceUnsupportedHof` (map's axiom-path elemTy!=itInt guard, which
##      a placeholder receiver's structurally-unbacked `seqElemTy` always
##      trips); `sutFilterPlaceholder` -> `sxUnknown` via filter's axiom
##      path, which declines UNCONDITIONALLY regardless of length. Neither
##      the pre-fix axiom-map guard nor the pre-fix axiom-filter/-fold
##      declines ever read the placeholder receiver's `seqLen`/`seqDataRaw`
##      content, so they were already sound by (accidental, not by
##      construction) type-guard placement.
##   2. DECLARED-FIELD receiver (`sutFieldMapPlaceholder` below): a field
##      whose declared type is the scoped-decline placeholder is
##      intercepted at PARSE time by `dsl_parser.nim`'s generic `nnkDotExpr`
##      arm (`isUnsupportedFieldPlaceholder(lhsCls.ty.fields[ix])` ->
##      `declineUnsupportedFieldRead`) -- BEFORE any `.map`/`.filter` call
##      node is even built over it, exactly as already documented for
##      `.len`/slice/index in `tsymex_r6_r1_placeholder_totality.nim`'s file
##      doc. The substitute is a genuine EMPTY SEQ LITERAL (`mkSeqLit`) --
##      NOT the `allocateSym` placeholder machinery -- so it is NOT
##      `isUnsupportedFieldPlaceholder`-flagged and DOES have a literal
##      `seqLen`. If it reaches `lowerHofCall`, `concreteSeqLen` WOULD fold
##      it and `canInline` WOULD go true -- but the SND-1 taint was already
##      deposited on the field-READ statement itself
##      (`declineUnsupportedFieldRead`'s own doc: "deposits the SND-1 taint
##      ... on THIS READ's own statement"), independent of whatever the
##      substitute computes downstream. The overall reported verdict for
##      that path is therefore ALREADY `sxUnknown` regardless of what
##      `lowerHofCall` does with the substitute -- confirmed empirically
##      below (single classified error, at the field READ, before `.map`
##      is ever reached).
##
## Neither finding makes this fix pointless: (1) means the fix is DEFENSE
## IN DEPTH against a currently-benign-by-accident axiom-path arrangement
## that a single future edit (to `concreteSeqLen`, to any one axiom-path
## type guard, or to `allocateSym`'s placeholder construction -- e.g. if it
## were ever changed to a literal `seqLen` for a bare source, matching
## `defaultZero`'s OWN itSeq placeholder arm, which already IS a literal --
## would immediately reintroduce the exact false-verdict class with no test
## to catch it); (2) confirms `lowerHofCall` is now sound BY CONSTRUCTION
## (the R1 chokepoint discipline) rather than by relying on an unstated,
## easily-broken invariant elsewhere in the file. Post-fix, both receiver
## sources below decline IMMEDIATELY and specifically through the R1
## chokepoint (`seNestedSeqUnsupported`, "higher-order call (.op)") --
## pinned below as the observable, meaningful behavior change: pre-fix the
## decline came from a generic, differently-worded axiom-path reason (or,
## for the bare sources, arrived only after the closure was needlessly
## lowered); post-fix it is immediate and attributes the true cause.
##
## ----------------------------------------------------------------------------
## Lambda shape note
## ----------------------------------------------------------------------------
## `tsymex_phase15_C4_hof.nim`'s own inline shapes (`x > 0`, `x + 1`) are
## PRE-EXISTING RED (N29, HOF lambda Z3 domain-sort mismatch, unrelated to
## this slice) whenever the closure body is actually LOWERED and APPLIED
## per-element (`applyClosureGround`, inside the loop). This fix's guard
## sits before `e.hofClosure` is even lowered for a placeholder receiver
## (see `lowerHofCall`'s guard, which returns before "Build the closure
## value"), and -- per finding 1 above -- a placeholder receiver never
## reaches the inline path (where `applyClosureGround` is actually called)
## even pre-fix, so N29 cannot leak into any assertion below regardless of
## lambda shape.
##
## ----------------------------------------------------------------------------
## `fold` reachability (honesty note, not a gap this slice owns)
## ----------------------------------------------------------------------------
## `lowerHofCall`'s `fold` arm is guarded identically to `map`/`filter` by
## this fix, but `tsymex_phase15_C4_hof.nim`'s own header already documents
## that `std/sequtils.foldl`/`foldr` are TEMPLATES the typed macro expands
## into a `for x in items(xs)` loop BEFORE the symex parser ever runs -- so
## `e.hofOp == "fold"` is not reachable through any real DSL source today
## (`walkHofFold`/the `fold` case arm exists "for a hypothetical closure-
## fold"). This file therefore cannot pin a source-level assertion for
## fold's guard specifically; the fix still guards it (defensively, for
## whenever a real closure-taking `fold` becomes reachable), and the
## `for`-loop desugar a real `foldl` over a placeholder-ized seq DOES take
## is already covered by `tsymex_r6_r1_placeholder_totality.nim`'s
## S1/iteration suite (the SAME `.len`-gated chokepoint any `for`-loop
## bound check goes through).
import std/[unittest, sequtils, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# Bare call-return placeholder receiver (finding 1 above). Mirrors
# `tsymex_r6_r1_placeholder_totality.nim`'s own `makePairs` idiom: a proc
# RETURNING the unbacked-elem seq allocates a FRESH placeholder-flagged
# `retSym` at every call site (`allocateSym`'s `itSeq` arm via
# `freshRetSym`), regardless of what the proc body does. (A bare SUT
# PARAMETER of this type instead hits the SEPARATE, EARLIER CR-2b/CR-2c
# witness/param-type classifier, degrading the whole walk before the body
# is even reached -- the exact anti-pattern the R1 file's own doc warns
# against; call-return avoids it.)
# =============================================================================

proc makePairsN27(n: int): seq[(string, string)] =
  discard

proc sutMapPlaceholder(n: int) =
  let ps = makePairsN27(n)
  let mapped = ps.map(proc(p: (string, string)): bool = true)
  if mapped.len > 0:
    symexTarget("map_placeholder")

proc sutFilterPlaceholder(n: int) =
  let ps = makePairsN27(n)
  let kept = ps.filter(proc(p: (string, string)): bool = true)
  if kept.len > 0:
    symexTarget("filter_placeholder")

# =============================================================================
# Declared-field placeholder receiver (finding 2 above) -- companion
# confirming the upstream parse-time field-read interception already
# protects this source, unaffected by this slice.
# =============================================================================

type
  RecN27 = object
    tag: int
    case kind: bool
    of true: options: seq[(string, string)]
    of false: plain: int

proc sutFieldMapPlaceholder(p: RecN27) =
  if p.kind:
    let mapped = p.options.map(proc(x: (string, string)): bool = true)
    if mapped.len > 0:
      symexTarget("field_map_placeholder")

# =============================================================================
# Backed-elem companions (regression: normal HOF behavior unaffected).
# `xs: seq[int]` is always backed (isBackedSeqElemTy includes itInt), so
# `lowerHofCall`'s new guard is provably a no-op here -- `seqSV.
# isUnsupportedFieldPlaceholder` is always false for these receivers. Mirrors
# C4-2/C4-3's own symbolic-length shapes.
# =============================================================================

proc sutFilterBackedSymbolic(xs: seq[int]) =
  let kept = xs.filter(proc(x: int): bool = x > 0)
  if kept.len > 0:
    symexTarget("filter_backed_symbolic")

proc sutMapBackedSymbolic(xs: seq[int]) =
  let ys = xs.map(proc(x: int): int = x + 1)
  if ys.len > 0:
    symexTarget("map_backed_symbolic")

suite "symex N27 — lowerHofCall now declines a placeholder receiver through the R1 chokepoint":

  test "N27-map: `ps.map(...)` over a bare-source placeholder receiver declines sxUnknown, immediately attributed to the R1 chokepoint (never sxSat/sxUnsat)":
    ## Pre-fix this SUT was ALREADY sxUnknown (see the file doc's finding 1)
    ## -- via a generic axiom-path `ceUnsupportedHof` reason, with NO
    ## `seNestedSeqUnsupported` error at all (confirmed empirically pre-fix).
    ## Post-fix it is `seNestedSeqUnsupported`, attributed to the receiver's
    ## placeholder status specifically, and it is the FIRST error recorded
    ## (the closure is never even lowered) -- the meaningful, pinned change.
    let r = symexFind(sutMapPlaceholder, tLabel("map_placeholder"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    check r.errors.len > 0
    check r.errors[0].kind == seNestedSeqUnsupported
    check r.errors[0].severity == sevError
    check "higher-order call (.map)" in r.errors[0].msg

  test "N27-filter: `ps.filter(...)` over a bare-source placeholder receiver declines sxUnknown, immediately attributed to the R1 chokepoint (never sxSat/sxUnsat)":
    ## Pre-fix this SUT was ALREADY sxUnknown too (finding 1) -- via filter's
    ## own unconditional axiom-path decline, plus an INCIDENTAL second
    ## `seNestedSeqUnsupported` from a `.len` read on a DIFFERENT, freshly
    ## substituted placeholder (`__hofFilterUnsupported`) -- not from the
    ## receiver's own placeholder status. Post-fix, the FIRST error is now
    ## the receiver's own decline, attributed correctly and immediately.
    let r = symexFind(sutFilterPlaceholder, tLabel("filter_placeholder"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    check r.errors.len > 0
    check r.errors[0].kind == seNestedSeqUnsupported
    check r.errors[0].severity == sevError
    check "higher-order call (.filter)" in r.errors[0].msg

suite "symex N27 — declared-field placeholder receiver (companion, unaffected by this slice)":

  test "N27-field-map: `.map` over a declared-field placeholder receiver still declines sxUnknown at the parse-time field-read interception -- unaffected by this slice's runtime guard":
    let r = symexFind(sutFieldMapPlaceholder, tLabel("field_map_placeholder"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    check r.errors.len > 0
    var sawFieldDecline = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and "field `options`" in e.msg:
        sawFieldDecline = true
    check sawFieldDecline

suite "symex N27 — backed-elem HOF companions (regression: unaffected by the guard)":

  test "N27-companion-filter: symbolic-length seq[int] filter still emits ceUnsupportedHof (sevError), sxUnknown -- identical to C4-2, guard never triggers":
    let r = symexFind(sutFilterBackedSymbolic, tLabel("filter_backed_symbolic"))
    check r.status == sxUnknown
    var sawHof = false
    for e in r.errors:
      if e.kind == ceUnsupportedHof and e.severity == sevError:
        sawHof = true
    check sawHof

  test "N27-companion-map: symbolic-length seq[int] map still terminates (sxSat or sxUnknown, never a hang/crash) -- identical to C4-3, guard never triggers":
    let r = symexFind(sutMapBackedSymbolic, tLabel("map_backed_symbolic"))
    check r.status in {sxSat, sxUnknown}

suite "symex N27 — walker version pin":

  test "walker version floor >= 97 (N27: lowerHofCall placeholder-receiver guard)":
    check parseInt(symexWalkerVersion) >= 97
