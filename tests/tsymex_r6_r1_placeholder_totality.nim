## R1 (post-0.4.0 remediation slice) — placeholder READ-TOTALITY chokepoint,
## walker v89.
##
## Round-6 (v85-v88) introduced `isUnsupportedFieldPlaceholder`: a `svSeq`
## whose element type `allocateSym`'s `itSeq` arm cannot back with a real Z3
## array (e.g. `seq[(string,string)]`) is allocated with `seqLen`
## HARD-FORCED `== 0` and an INERT data array nothing may legitimately
## select from. A verdict-affecting READ of such a value must always
## CLASSIFIED-DECLINE (`seNestedSeqUnsupported`), never silently compute a
## verdict from the fake length/content. The v85-v88 guard set covered only
## `isIndex`'s `svSeq` arm (plus the PARSE-TIME `nnkDotExpr` field-read
## interception for a DECLARED FIELD source) — this slice's review found two
## further Critical false-verdict gaps and a message-quality gap:
##
##   S1 — `iekSeqLen`'s `of svSeq:` arm (the `.len` read, and — since the
##   `for x in seq:` desugar compiles its bound check to exactly this same
##   `.len` read — every FOR-LOOP over a placeholder too) returned
##   `SymVal(kind: svInt, zi: recv.seqLen)` with NO placeholder check: a
##   `.len`-gated query was silently PROVEN against the forced length 0 (a
##   false `sxUnsat`).
##
##   N1 — `iekSeqSlice` read `recv.seqLen`/`recv.seqDataRaw` with no check:
##   a slice's own OOB bound was tautologically violated under the forced
##   `lenSym == 0` path condition, forking a guaranteed-spurious
##   `IndexDefect` and pruning the real continuation (another false
##   `sxUnsat`); WORSE, the returned slice `SymVal` omitted the flag, so the
##   taint was LOST for any further consumer of the slice result.
##
##   Q2 — the `isIndex` decline message (added v88) omitted the `<loc>: `
##   prefix idiom the SAME handler's non-seq-receiver decline already uses,
##   despite the parser already populating `stmt.ixLoc`.
##
## Both S1 and N1 (plus `iekSeqAdd`'s mutation arm, audited this slice) are
## now routed through a shared CHOKEPOINT (`placeholderReadDeclineMsg` +
## `declinePlaceholderInLower`, `runtime.nim`, just above `freshRetSym`)
## rather than two more hand-placed checks; `isIndex`'s existing guard now
## shares the same message formatter (Q2's fix).
##
## ---- Two placeholder SOURCES, only ONE of which exercises S1/N1/iekSeqAdd
##
## A DECLARED-FIELD placeholder source (`Rec.options` below) is INTERCEPTED
## AT PARSE TIME — `dsl_parser.nim`'s `nnkDotExpr` field-read arm declines
## the READ OF THE FIELD ITSELF (`declineUnsupportedFieldRead`, returning an
## ordinary empty-literal `IRExpr` substitute) BEFORE any `.len`/slice/index
## IR node is even built over it — so `.len`/slice/index applied to a
## field-sourced placeholder were ALREADY safe pre-v89 (confirmed below as
## honest companions, not new RED). A BARE call-return placeholder source
## (`makePairs` below) has NO static field-access site for the parser to
## intercept — the `SymVal` itself must carry the flag all the way to
## whichever runtime arm actually consumes it, which is exactly where S1/N1
## lived unguarded. The bare-value SUTs below are therefore the ones that
## demonstrate genuine RED; the field SUTs are regression companions
## confirming the pre-existing guard is undisturbed.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# Placeholder sources
# =============================================================================

# ---- Bare call-return source: every call to a proc RETURNING an
# unbacked-element seq allocates a FRESH placeholder-flagged `retSym`
# (`allocateSym`'s `itSeq` arm, via `freshRetSym`) regardless of what this
# body itself does — the B7r2-1c call-boundary mechanism.
proc makePairs(n: int): seq[(string, string)] =
  discard

proc readsLen(ps: seq[(string, string)]): int =
  ## Callee for the pass-to-callee form below. Its OWN formal binding is a
  ## direct value-copy of the caller's already-lowered actual (`isCall`'s
  ## `calleeEnv[formal.name] = argVals[i]`, runtime.nim ~7269) — the
  ## placeholder flag rides through unchanged; safety here comes from the
  ## SAME `iekSeqLen` chokepoint the bare-.len test below exercises, not a
  ## distinct site.
  ps.len

# ---- Declared-field source: already parse-time-guarded (see file doc above).
type
  RKind = enum rkOpts, rkPlain
  Rec = object
    tag: int
    case kind: RKind
    of rkOpts: options: seq[(string, string)]
    of rkPlain: plain: int

# =============================================================================
# S1 — `.len` read
# =============================================================================

proc sutBareLenRead(n: int) =
  let ps = makePairs(n)
  if ps.len > 0:
    symexTarget("bare_len_read")

proc sutFieldLenRead(p: Rec) =
  if p.kind == rkOpts and p.options.len > 0:
    symexTarget("field_len_read")

# =============================================================================
# N1 — slice read
# =============================================================================

proc sutBareSliceRead(n: int) =
  let ps = makePairs(n)
  let sl = ps[0 .. 0]
  discard sl
  symexTarget("bare_slice_read")

proc sutFieldSliceRead(p: Rec) =
  if p.kind == rkOpts:
    let sl = p.options[0 .. 0]
    discard sl
    symexTarget("field_slice_read")

# =============================================================================
# Iteration — `for x in ps:` desugars to a `.len`-gated `while`, so this is
# mechanically the SAME S1 chokepoint under a different surface syntax.
# =============================================================================

proc sutBareIterationCount(n: int) =
  let ps = makePairs(n)
  var cnt = 0
  for x in ps:
    cnt.inc
  if cnt == 3:
    symexTarget("bare_iteration_three")

# =============================================================================
# Index read — the v88 `isIndex` guard already exists and already declines;
# ZERO coverage pre-v89 (Q1). Pinned here, asserting the decline message now
# carries the `<loc>: ` prefix (Q2's fix — this file's own path/line, proving
# `stmt.ixLoc` reached the message, not merely that it declined).
# =============================================================================

proc sutBareIndexRead(n: int) =
  let ps = makePairs(n)
  let first = ps[0]
  discard first
  symexTarget("bare_index_read")

proc sutFieldIndexRead(p: Rec) =
  if p.kind == rkOpts:
    let first = p.options[0]
    discard first
    symexTarget("field_index_read")

# =============================================================================
# Equality — `ps == qs`. Round-6 re-review (walker v112): `lowerCmp` routes a
# non-int/bool/float/string comparison to `eqBV`/`neBV`/`cmpBV`, which now
# GUARD-BEFORE (B7r2 precedent) on an `isUnsupportedFieldPlaceholder` operand
# — routed through the SAME `declinePlaceholderInLower`/
# `placeholderReadDeclineMsg` chokepoint S1/N1/iekSeqAdd use, classified
# `seNestedSeqUnsupported`, BEFORE ever reaching the generic non-placeholder
# catch-all. (General, non-placeholder seq equality remains unmodeled — that
# capability-addition gap is still out of this chokepoint slice's scope.)
#
# `n` is deliberately `range[0 .. 1000]`, not a bare `int` — mirroring
# `sutUntouchedUnsat`'s own precedent below. Root-caused during this slice's
# regression hunt: a bare `int n` makes `makePairs(n + 1)`'s own `n + 1`
# GENUINELY overflow-reachable (`n == high(int)`), an accidental defect
# entirely unrelated to the placeholder-equality decline this test names. Per
# E6, a reachable `Defect` always surfaces in the verdict regardless of the
# search target and regardless of what any comparison-site guard does
# downstream — so with a bare `int`, this test's own helper arithmetic wins
# the verdict as `sxRaised(OverflowDefect)`, independent of (and masking) the
# eqBV placeholder decline this test intends to exercise. Bounding `n` makes
# `n + 1` provably in-range, closing that accidental hole.
# =============================================================================

proc sutBareEquality(n: range[0 .. 1000]) =
  let ps = makePairs(n)
  let qs = makePairs(n + 1)
  if ps == qs:
    symexTarget("bare_equality_eq")

# =============================================================================
# Mutation (`iekSeqAdd`) — N6 audit item, not in the prompt's explicit access-
# form list but explicitly named ("iekSeqAdd/iekSeqDel/iekSeqSetLen/any
# mutation arms") as a site to audit-and-route-through-the-chokepoint.
# `.add` parses unconditionally for ANY `itSeq` receiver (`dsl_parser.nim`'s
# `.add` arm dispatches on receiver KIND only, not element backedness) --
# pre-fix, `.add` on a placeholder fell through to `iekSeqAdd`'s `case
# recv.seqElemTy.kind` dispatch, whose `else` arm raises a bare `ValueError`
# for the unbacked kind, unwinding to `runSymexImpl`'s catch-all and
# poisoning the WHOLE run (`weInternalWalkerFault`) -- not branch-scoped.
# =============================================================================

proc sutBareMutation(n: int) =
  var ps = makePairs(n)
  ps.add(("a", "b"))
  if n == 5:
    symexTarget("bare_mutation")

# =============================================================================
# Pass-to-callee — `f(ps)`. Not a distinct chokepoint site (see `readsLen`'s
# doc comment above); pinned to confirm the flag survives a call boundary.
# =============================================================================

proc sutPassToCallee(n: int) =
  let ps = makePairs(n)
  let L = readsLen(ps)
  if L > 0:
    symexTarget("pass_to_callee_hit")

# =============================================================================
# UNTOUCHED-path soundness companions — a query that never reads the
# placeholder must still resolve a REAL sxSat/sxUnsat (the entire point of
# SCOPED decline: mere allocation of an unbacked-seq-typed value, param or
# call-return, must never poison an unrelated target).
# =============================================================================

## NOTE: deliberately NOT a bare top-level `seq[(string,string)]` SUT
## PARAMETER — a bare unbacked-seq FORMAL hits the SEPARATE, EARLIER
## witness/param-type classifier (`dsl_typebridge.nim`, CR-2b/CR-2c), which
## degrades the WHOLE walk regardless of whether the param is ever touched
## (confirmed empirically: this is why NEITHER `tsymex_r6_bug2_scopeddecline
## .nim` NOR `tsymex_r6_b7r2_pathscope.nim` ever use a bare unbacked-seq
## PARAM — always a declared FIELD, a LOCAL, or a call-return). `allocateSym`
## never raising for mere allocation (the v85-v88 fix this file's
## "UNTOUCHED" companions exist to regression-guard) is a WALK-TIME/RUNTIME
## property, orthogonal to that earlier gate — a LOCAL call-return binding
## exercises it without tripping the param-classifier.
proc sutUntouchedSat(n: int) =
  let dummy = makePairs(n)
  discard dummy
  if n == 7:
    symexTarget("untouched_sat")

proc sutUntouchedUnsat(n: range[0 .. 1000]) =
  let dummy = makePairs(n)
  discard dummy
  if n == 7 and n == 8:
    symexTarget("untouched_unsat")

# =============================================================================
# Tests
# =============================================================================

suite "symex R1 — S1 (.len read) false-verdict fix":

  test "R1-S1a (bare call-return): `.len > 0` on a placeholder no longer silently proves sxUnsat off the forced length 0 -- declines sxUnknown/seNestedSeqUnsupported":
    let r = symexFind(sutBareLenRead, tLabel("bare_len_read"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

  test "R1-S1b (declared field, companion): `.len` on a field-sourced placeholder was ALREADY guarded pre-v89 by the parse-time nnkDotExpr field-read interception -- unaffected by this slice, still declines":
    let r = symexFind(sutFieldLenRead, tLabel("field_len_read"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex R1 — N1 (slice read) false-verdict fix":

  test "R1-N1a (bare call-return): `ps[0 .. 0]` on a placeholder no longer forks a guaranteed-spurious IndexDefect off the forced length 0 -- declines sxUnknown/seNestedSeqUnsupported":
    let r = symexFind(sutBareSliceRead, tLabel("bare_slice_read"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

  test "R1-N1b (declared field, companion): slice on a field-sourced placeholder was ALREADY guarded pre-v89 -- unaffected by this slice, still declines":
    let r = symexFind(sutFieldSliceRead, tLabel("field_slice_read"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex R1 — iteration over a placeholder (mechanically the S1 chokepoint)":

  test "R1-iter: `for x in ps: cnt.inc` on a placeholder no longer silently proves cnt==3 unreachable (sxUnsat) off the forced-zero-iteration loop -- declines sxUnknown/seNestedSeqUnsupported":
    let r = symexFind(sutBareIterationCount, tLabel("bare_iteration_three"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex R1 — Q1/Q2 (index read coverage + location-prefixed message)":

  test "R1-Q1a (bare call-return): `ps[0]` declines sxUnknown/seNestedSeqUnsupported (the v88 guard, now covered)":
    let r = symexFind(sutBareIndexRead, tLabel("bare_index_read"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

  test "R1-Q2: the index-read decline message now carries the `<loc>: ` site prefix (this file's own path), not just the bare reason text":
    let r = symexFind(sutBareIndexRead, tLabel("bare_index_read"))
    check r.status == sxUnknown
    var sawLocPrefix = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and ".nim:" in e.msg:
        sawLocPrefix = true
    check sawLocPrefix

  test "R1-Q1b (declared field, companion): index read on a field-sourced placeholder was ALREADY guarded pre-v89 -- unaffected by this slice, still declines":
    ## Loose form (status + non-empty classified errors only, no specific
    ## `kind` match): `p.options[0]`'s RECEIVER is parsed via the SAME
    ## `nnkDotExpr` field-read guard `.len`/slice go through (an EMPTY seq
    ## LITERAL substitute, not the runtime placeholder), so the taint here
    ## is deposited BEFORE `isIndex` ever runs -- `isIndex`'s OWN (real,
    ## non-placeholder) OOB check then forks a "genuine" IndexDefect against
    ## the substitute's literal length 0, on an ALREADY-SND-1-tainted path.
    ## The status still correctly demotes to `sxUnknown` (confirmed below),
    ## but the SPECIFIC classified `kind` `isIndex`'s dedicated `forkDefect`
    ## raise-path surfaces for an already-tainted path was found, empirically,
    ## NOT to be `seNestedSeqUnsupported` here (unlike the `.len`/slice
    ## companions, whose accessor never forks a defect) -- an asymmetry
    ## between `forkDefect` and `iekSeqSlice`'s `drainStrIndexRaises` sink
    ## this slice did not chase further (this flow never touches the
    ## `isUnsupportedFieldPlaceholder`-flagged runtime value at all -- the
    ## field guard already substitutes an honest empty literal before either
    ## accessor runs -- so it is outside R1's chokepoint-audit scope; see the
    ## R1 summary's residual-gaps list).
    let r = symexFind(sutFieldIndexRead, tLabel("field_index_read"))
    check r.status == sxUnknown
    check r.errors.len > 0

suite "symex R1 — equality (walker v112: eqBV/neBV/cmpBV/svLeafEq/iteSV now guard-before on a placeholder operand)":

  test "R1-eq: `ps == qs` over two placeholders declines sxUnknown/seNestedSeqUnsupported (never a crash, never a false sat/unsat) via the SAME R1 chokepoint S1/N1 use":
    let r = symexFind(sutBareEquality, tLabel("bare_equality_eq"))
    check r.status == sxUnknown
    check r.status != sxSat
    check r.status != sxUnsat
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex R1 — iekSeqAdd mutation arm (N6 audit item)":

  test "R1-mutate: `.add` on a placeholder no longer whole-run-poisons via a bare ValueError -- declines branch-scoped sxUnknown/seNestedSeqUnsupported":
    let r = symexFind(sutBareMutation, tLabel("bare_mutation"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex R1 — pass-to-callee (flag survives a call boundary)":

  test "R1-call: `readsLen(ps)` inside a callee still declines sxUnknown/seNestedSeqUnsupported via the SAME S1 chokepoint, reached through a call boundary":
    let r = symexFind(sutPassToCallee, tLabel("pass_to_callee_hit"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seNestedSeqUnsupported and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex R1 — UNTOUCHED-path soundness companions (scoped decline never poisons an unrelated target)":

  test "R1-untouched-sat: a target unrelated to the placeholder param still proves real sxSat":
    let r = symexFind(sutUntouchedSat, tLabel("untouched_sat"))
    check r.status == sxSat
    check r.witness[0] == 7

  test "R1-untouched-unsat: a genuine contradiction unrelated to the placeholder param still resolves real sxUnsat":
    let r = symexFind(sutUntouchedUnsat, tLabel("untouched_unsat"))
    check r.status == sxUnsat

suite "symex R1 — walker version pin":

  test "walker version floor >= 89 (R1: placeholder read-totality chokepoint)":
    check parseInt(symexWalkerVersion) >= 89
