## RFC-chapulin-hardening TOT-1 — table-driven §0-invariant regression corpus
## (§Totality harness & integration exit).
##
## §0's totality invariant ("the walker/macro layer never crashes, never
## macro-`error()`s at compile time, and never reports a false `sxSat`/
## `sxRaised` with empty `errors`; any unmodeled construct degrades to a
## CLASSIFIED `sxUnknown`") is otherwise only *asserted* in the RFC prose, not
## *built* into CI — a one-time grep audit at slice-close time catches no
## future regression. This file is the permanent backstop: a FIXED,
## hand-authored table of constructs that are CURRENTLY genuinely unmodeled
## (verified empirically, 2026-07-25, both backends), each covering one of
## the three open §0 surfaces named by the RFC:
##
##   1. Parser catch-all         (CR-2a, `dsl_parser.nim` `parseExpr`)
##   2. Type/witness classifier  (CR-2b `dsl_typebridge.nim` param types;
##      catch-all                 CR-2c `symex.nim` `emitTyAndReader` witness
##                                 shapes — reuses CR-2b's degrade pipeline)
##   3. Internal-fault /          (SND-1 statement taint, SND-1b closure-body
##      uncertain-taint            taint, CR-1c last-resort walker catch)
##
## Every corpus item is asserted NEVER to be a false `sxSat`/`sxUnsat` (the
## §0 soundness half) and, wherever the engine exposes a classified degrade
## KIND, that the classification is actually present (not a silent
## empty-`errors` `sxUnknown`) — mirroring the strong-form assertions in the
## individual CR-2a/b/c, SND-1/1b, and CR-1c slice tests this file mines its
## repros from. This is intentionally NOT independent test authorship: each
## item is a proven-still-degrading construct lifted from a landed slice
## test, so a regression in the underlying fix trips THIS file too (the DoD:
## "a deliberately-reintroduced regression makes it fail").
##
## ## Historical RFC repros EXCLUDED as now-modeled (verified empirically)
##
## The RFC's own repro list (`docs/RFC-chapulin-hardening.md` L672-675) names
## several constructs that no longer degrade — they were the RED repros for
## fixes that have since LANDED and now return REAL verdicts, so locking a
## `sxUnknown` assertion on them would be testing the WRONG thing (and would
## silently stop being a backstop for anything):
##   * bitwise-on-`svInt` (was CR-1a's repro) — now correctly modeled.
##   * tail-return-of-local (was CR-1b's repro) — now correctly modeled.
##   * `&=` on a string LHS (was SND-1's original repro) — Phase 16 M4 models
##     it as `iekStrConcat` (`s := s & x`); see `tsymex_snd1_uncertain_taint.nim`
##     SUT 1 (`concatMutate`), which flipped RED->real-`sxSat` at M4. Reused
##     `/=` (float div-assign) here instead — M4 does not touch it, so it is
##     still a genuine bare Class-B `mkUnsupported` drop.
##   * an `if`-EXPRESSION nested as a sub-expression (an earlier CR-2a repro)
##     — RFC M5 (walker v51) added an `nnkIfExpr` arm to `parseExpr`; both
##     `if`-expr shapes now resolve to real verdicts (see
##     `tsymex_CR2a_expr_catchall.nim` SUTs 1-2). Reused `cast[int32](x)`
##     nested as an operand here instead — `parseExpr` still has no `nnkCast`
##     arm outside the R11 pointer-materialisation guard.
##   * `symexAssume`/`symexAssert` edge shapes — SND-2 (landed) models these
##     directly; they are not a §0 catch-all surface at all.
##   * plain tuple/obj/slice edge shapes — CR-2c's renderable-nested
##     regression guards (`tsymex_CR2c_witnessreader_catchall.nim` CR-2c-10..12)
##     prove these resolve normally; only NON-renderable nested leaves
##     (e.g. `seq[Widget]` nested in a tuple) still degrade, which this file's
##     Item 6 covers instead.
##   * B2 same-width signedness reinterpret (`uint32(x)` from `int32`) — was
##     Round-6 B2's own repro for "no reinterpret primitive modeled";
##     9019d90 (fix-slice item 7a) corrected the scope (a pure signed-tag
##     flip on an already-signedness-agnostic BV bit pattern is sound, not
##     unrepresentable). Unlike the other exclusions above, this one is NOT
##     simply dropped — see the dedicated "B2 same-width reinterpret" suite
##     immediately below the corpus table, which pins the sxSat witness AND
##     an UNSAT soundness companion.
##
## No production code / no `symexWalkerVersion` bump — TOT-1 is a
## test-only regression corpus (RFC DoD, Size M).

import std/[unittest, strutils, tables, sets]
import nelli/symex
import nelli/smt/canonicalize

# =============================================================================
# SUTs — one per corpus item, grouped by the §0 surface it backstops.
# =============================================================================

# ---- Surface 1: parser catch-all (CR-2a) -----------------------------------

# `cast[int32](x)` nested as an operand of `+`. `parseExpr` has no `nnkCast`
# arm outside the R11 pointer-materialisation guard (which only matches
# `cast[ptr T]`/`addr`, and only at let-rhs classification) — this still
# lands on the catch-all today. A leaked dummy of 0 would make `y == 1`
# trivially satisfiable for every `x`; SND-1's taint must block that.
proc corpusCastSubExpr(x: int64) =
  let y = cast[int32](x) + 1
  if y == 1:
    symexTarget("cast_subexpr")

# Round-6 A0: `low(T)`/`high(T)` on a non-int-family type (`bool`, here) is
# out of A0's fold scope (only `intTyNames` folds to a literal) — must
# decline cleanly to a classified `sxUnknown`, never fall through to the
# pre-A0 walker fault the fold itself fixes for the int-family case.
proc corpusLowHighNonIntFamily(flag: bool, y: int) =
  if flag == low(bool) and y == 42:
    symexTarget("low_high_non_int_family")

# Round-6 A1 (ADR-0029): a multi-`case`-object (`itMultiVariant`)
# constructor stays a classified decline after A1 SPLITS the former
# combined `of itVariant, itMultiVariant:` P2b arm — construction ships as
# its own slice only if a consumer needs it first (ADR-0029 "Deliberately
# not covered"). Must decline cleanly, never crash and never fall through
# to the now-real `itVariant` literal-discriminant construction path.
type
  Tot1AxisA = enum tot1aX, tot1aY
  Tot1AxisB = enum tot1bP, tot1bQ
  Tot1MultiVariant = object
    case axis1: Tot1AxisA
    of tot1aX: a1: int
    of tot1aY: a2: int
    case axis2: Tot1AxisB
    of tot1bP: b1: int
    of tot1bQ: b2: int

proc corpusMultiVariantConstr(x: int) =
  let t = Tot1MultiVariant(axis1: tot1aX, a1: x, axis2: tot1bP, b1: x)
  if t.a1 == 42:
    symexTarget("multivariant_constr")

# Round-6 A3 (ADR-0029): a symbolic-discriminant variant CONSTRUCTION whose
# feasible tag set exceeds `maxVariantConstructorForks` (default 8) — here a
# 10-tag enum constructed at TOP LEVEL, with no enclosing `case` branch to
# narrow it — must decline cleanly to a classified `sxUnknown`
# (`beBudgetExhausted`, the SAME kind `maxLoopUnwind`/`maxFrontierSize`
# exhaustion uses — SND-4 "mirror, don't reinvent"), never an unbounded
# fork explosion and never a crash.
type
  Tot1WideTag = enum
    tot1w0, tot1w1, tot1w2, tot1w3, tot1w4,
    tot1w5, tot1w6, tot1w7, tot1w8, tot1w9
  Tot1WideVariant = object
    tag: int
    case kind: Tot1WideTag
    of tot1w0: f0: int
    of tot1w1: f1: int
    of tot1w2: f2: int
    of tot1w3: f3: int
    of tot1w4: f4: int
    of tot1w5: f5: int
    of tot1w6: f6: int
    of tot1w7: f7: int
    of tot1w8: f8: int
    of tot1w9: f9: int

proc corpusVariantConstructBudgetExceeded(b: byte, x: int) =
  let op = if b == 1'u8: tot1w0 else: tot1w1
  let v = Tot1WideVariant(kind: op, tag: x)
  if v.tag == 42:
    symexTarget("variant_construct_budget_exceeded")

# Round-6 B2: a NARROWING int conversion (`uint8(x)` truncating an `int32`)
# has no truncate primitive modeled — must decline cleanly to a classified
# sxUnknown, never fall through to the pre-B2 identity pass-through's
# silent unsoundness (the value left unmasked).
proc corpusNarrowIntConv(x: int32) =
  let b = uint8(x)
  if b == 42'u8:
    symexTarget("narrow_int_conv")

# Round-6 B2 recorded a SAME-WIDTH signedness REINTERPRET (`uint32(x)` from
# an `int32`) as a classified decline ("no reinterpret primitive modeled").
# 9019d90 (fix-slice item 7a, A1 adjudication) corrected the scope: every
# fixed-width Nim int already allocates as an svBV* whose raw Z3 bit pattern
# is signedness-agnostic, so a same-width reinterpret is a pure signed-tag
# flip on the SAME bits — sound for every input, not merely a decline. This
# CAPABILITY GAIN moves the cell out of the §0 corpus below (asserting
# `sxUnknown` here would now be testing the WRONG thing, mirroring this
# file's own "EXCLUDED as now-modeled" precedent) and into the dedicated
# suite just below the corpus, which pins the new honest behavior: a real
# `sxSat` witness, plus an UNSAT soundness companion proving the tag flip
# never spuriously equates a value it shouldn't.
proc corpusReinterpretIntConv(x: int32) =
  let u = uint32(x)
  if u == 42'u32:
    symexTarget("reinterpret_int_conv")

# Soundness companion (item 7a): the reinterpret is a BIT-PATTERN-preserving
# tag flip, so `u == 42'u32` should hold for EXACTLY `x == 42`, never for any
# other `x` — this target must stay UNSAT.
proc corpusReinterpretIntConvSoundness(x: int32) =
  let u = uint32(x)
  if x != 42 and u == 42'u32:
    symexTarget("reinterpret_int_conv_soundness")

# ---- Surface 2: type/witness classifier catch-all (CR-2b / CR-2c) ---------

# `cstring` is not in `classifyType`'s supported scalar set. Params are
# allocated before the body is walked, so this degrades the WHOLE RUN to
# sxUnknown even though `y == 42` is trivially reachable.
proc corpusCstringParam(s: cstring, y: int) =
  if y == 42:
    symexTarget("cstring_param")

type
  Widget = object
    a: int
    b: int

# `seq[Widget]` — a non-scalar/non-ref seq element — hits
# `emitTyAndReader`'s `itSeq` catch-all (CR-2c).
proc corpusSeqObjectWitness(ws: seq[Widget], y: int) =
  if y == 42:
    symexTarget("seq_object_witness")

# `HashSet[string]` — element type is not `itInt(64, signed)` — hits
# `emitTyAndReader`'s `itSet` catch-all (CR-2c).
proc corpusHashSetStringWitness(s: HashSet[string], y: int) =
  if y == 42:
    symexTarget("hashset_string_witness")

# Nested-aggregate shape: a tuple whose field is an unrenderable
# `seq[Widget]` — proves the CR-2c recursive predicate still degrades a
# NESTED unrenderable leaf, not just a bare top-level seq/Table/HashSet
# param (the "completeness gap" CR-2c itself closed).
proc corpusNestedTupleWitness(x: tuple[a: seq[Widget], n: int], y: int) =
  if y == 42:
    symexTarget("nested_tuple_witness")

# ---- Surface 3: internal-fault / uncertain-taint (SND-1 / SND-1b / CR-1c) -

# `acc /= 2.0` is a bare Class-B `mkUnsupported` statement (no accompanying
# `sevError` parseError) — SND-1's `isUnsupported` taint-and-continue must
# demote the downstream target to sxUnknown, never let the walk falsely
# "solve" against the stale (un-divided) value.
proc corpusDivAssignTaint(acc: var float) =
  acc /= 2.0
  if acc == 5.0:
    symexTarget("div_assign_taint")

# A closure body that drops a mutation via the same still-unsupported `/=`.
# `applyClosureGround` must skip axiomatizing an uncertain sub-path (SND-1b)
# rather than assert a possibly-wrong ground fact for the rest of the run.
proc corpusClosureBodyTaint(t: var float) =
  let f = proc(s: float): int =
    var r = s
    r /= 2.0
    if r == 5.0:
      return 1
    return 0
  if f(t) == 1:
    symexTarget("closure_body_taint")

# A closure body whose internal call has no base case, so every call bails
# on `maxCallDepth` — the closure's own returned sub-path is uncertain too.
proc corpusAlwaysRecurse(n: int): int =
  return corpusAlwaysRecurse(n) + 1

proc corpusClosureDepthBail(x: int) =
  let f = proc(n: int): int = corpusAlwaysRecurse(n)
  if f(x) == 999999:
    symexTarget("closure_depth_bail")

# Synthetic injected native fault (CR-1c's last-resort `runSymex` catch).
# The `symexTestInjectWalkerFault` define (companion `.nim.cfg`) raises a
# plain `ValueError` — deliberately indistinguishable in TYPE from a real
# internal-invariant bug — the moment dispatch reaches this sentinel label.
proc corpusInternalFaultInjector() =
  symexTarget("__inject_walker_fault__")

# ---- Surface 5: per-field scoped decline / read-taint (Round-6 Bug #2) ----

# Round-6 Bug #2 (`docs/RFC-chapulin-hardening.handoff.md`'s FORK
# RESOLUTION bullet; see `tests/tsymex_r6_bug2_scopeddecline.nim` for the
# full pin set). A declared object/variant field whose type is structurally
# unsupported for allocation backing (`options: seq[(string,string)]` — the
# element kind `itTuple` is not in `allocateSeqDataRaw`'s backed set)
# classifies to a KIND-MARKED placeholder instead of eagerly poisoning the
# whole type. A DIRECT READ of that field (not merely allocating the
# containing object) is the one surface that still degrades — this is the
# `dsl_parser.nim` `nnkDotExpr` field-read arm's own classified decline
# (`seNestedSeqUnsupported`), a genuinely new reachable site distinct from
# CR-2a/CR-2b/CR-2c/SND-1/CR-1c's surfaces (it fires on the READ, not on
# allocation or parse-time expression-kind dispatch).
type
  Tot1PKind = enum tot1pRrq, tot1pData
  Tot1Packet = object
    tag: int
    case kind: Tot1PKind
    of tot1pRrq: options: seq[(string, string)]
    of tot1pData: blockNum: int

proc corpusUnsupportedFieldRead(p: Tot1Packet) =
  if p.kind == tot1pRrq:
    let opts = p.options
    discard opts
    symexTarget("unsupported_field_read")

# R1 (post-0.4.0 remediation slice, placeholder read-totality chokepoint,
# walker v89): the DECLARED-FIELD read above (`corpusUnsupportedFieldRead`)
# was already intercepted at PARSE TIME (`dsl_parser.nim`'s `nnkDotExpr`
# field-read arm) since v85 — but a BARE call-return placeholder (no
# declared field, no static field-access site for the parser to intercept)
## had NO runtime guard on its `.len` read until this slice: `iekSeqLen`'s
## `of svSeq:` arm returned the placeholder's HARD-FORCED-`==0` length
## directly, letting a `.len`-gated query get silently PROVEN false instead
## of honestly declining (Critical soundness bug S1). This is a genuinely
## NEW reachable decline surface distinct from the field-read row above (it
## fires from `iekSeqLen`'s own chokepoint, not the parser's field-access
## interception) — R1 landed `placeholderReadDeclineMsg`/
## `declinePlaceholderInLower` (`runtime.nim`, just above `freshRetSym`) as
## the shared chokepoint every `svSeq`-consuming `lower()` arm now calls.
proc corpusMakeUnsupportedPairs(n: int): seq[(string, string)] =
  discard

proc corpusBareLenRead(n: int) =
  let ps = corpusMakeUnsupportedPairs(n)
  if ps.len > 0:
    symexTarget("bare_len_read")

# Round-6 A6-rider: a callee whose body reaches the end via IMPLICIT
# fallthrough (no explicit `return`) after a CONDITIONAL, multi-statement
# `result = expr` assignment, where the returned VALUE is a composite kind
# outside the scalar-wired set `isReturn`'s explicit-return arm already
# supports (`svTuple`/`svVariant` and every scalar — but NOT `svSeq` here).
# Pre-fix this degraded to an UNSOUND unconstrained `retSym` (the BLOCKER
# #12 root cause, see `tests/tsymex_r6_a6r_callwitness.nim`); post-fix, a
# composite kind the walker doesn't yet have a `retBindEq` arm for degrades
# cleanly to a classified `sxUnknown` (mirroring `isReturn`'s own existing
# composite-return degrade net verbatim, `feUnsupportedOp`), never a false
# `sxSat` and never a crash.
proc corpusCompositeFallthroughReturn(x: int): seq[int] =
  if x < 0:
    raise newException(ValueError, "negative")
  result = @[x]

proc corpusCompositeImplicitFallthrough(x: int) =
  let s = corpusCompositeFallthroughReturn(x)
  if s.len == 1:
    symexTarget("composite_implicit_fallthrough")

# ---------------------------------------------------------------------------
# The table. `symexFind` requires a literal `typed` proc per call (macro-time
# constraint — this cannot itself be data-driven), so each row's VERDICT is
# computed once above via its own `symexFind` call; what IS genuinely
# table-driven is the §0 invariant check applied uniformly, in a loop, across
# every row below (mirrors the `for backend in [...]: test ...` idiom already
# used elsewhere in this suite, e.g. `tfuzzcbuild.nim`).
# ---------------------------------------------------------------------------

type
  CorpusItem = object
    label:        string   ## short id
    surface:      string   ## which §0 surface this backstops
    backstops:    string   ## which RFC fix landing this guards against reverting
    status:       SymexStatusKind
    errors:       seq[SymexErrorInfo]
    expectedKind: SymexErrorKind  ## only meaningful when hasKindCheck
    hasKindCheck: bool            ## Class-A sites carry a classified kind;
                                   ## SND-1's bare Class-B drop does not (by
                                   ## design — see tsymex_snd1_uncertain_taint.nim)

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k and e.severity == sevError:
      return true
  false

let
  rCast          = symexFind(corpusCastSubExpr,          tLabel("cast_subexpr"))
  rLowHighNonInt = symexFind(corpusLowHighNonIntFamily,  tLabel("low_high_non_int_family"))
  rMultiVariant  = symexFind(corpusMultiVariantConstr,   tLabel("multivariant_constr"))
  rVariantConstructBudget = symexFind(corpusVariantConstructBudgetExceeded,
                                       tLabel("variant_construct_budget_exceeded"))
  rNarrowIntConv      = symexFind(corpusNarrowIntConv,      tLabel("narrow_int_conv"))
  rReinterpretIntConv = symexFind(corpusReinterpretIntConv, tLabel("reinterpret_int_conv"))
  rReinterpretIntConvSoundness = symexFind(corpusReinterpretIntConvSoundness,
                                            tLabel("reinterpret_int_conv_soundness"))
  rCstring       = symexFind(corpusCstringParam,         tLabel("cstring_param"))
  rSeqObject     = symexFind(corpusSeqObjectWitness,     tLabel("seq_object_witness"))
  rHashSetString = symexFind(corpusHashSetStringWitness, tLabel("hashset_string_witness"))
  rNestedTuple   = symexFind(corpusNestedTupleWitness,   tLabel("nested_tuple_witness"))
  rDivAssign     = symexFind(corpusDivAssignTaint,       tLabel("div_assign_taint"))
  rClosureBody   = symexFind(corpusClosureBodyTaint,     tLabel("closure_body_taint"))
  rClosureDepth  = symexFind(corpusClosureDepthBail,     tLabel("closure_depth_bail"))
  rInternalFault = symexFind(corpusInternalFaultInjector, tLabel("__inject_walker_fault__"))
  rUnsupportedFieldRead = symexFind(corpusUnsupportedFieldRead, tLabel("unsupported_field_read"))
  rBareLenRead   = symexFind(corpusBareLenRead,          tLabel("bare_len_read"))
  rCompositeFallthrough = symexFind(corpusCompositeImplicitFallthrough,
                                     tLabel("composite_implicit_fallthrough"))

let corpus = @[
  CorpusItem(label: "CR-2a: cast[int32](x) as sub-expr",
             surface: "1. parser catch-all",
             backstops: "CR-2a (parseExpr expr-kind catch-all)",
             status: rCast.status, errors: rCast.errors,
             expectedKind: feUnsupportedExprKind, hasKindCheck: true),

  CorpusItem(label: "A0: low(bool) — non-int-family low/high",
             surface: "1. parser catch-all",
             backstops: "Round-6 A0 (low/high int-magic parse-time fold — " &
                        "non-int-family decline)",
             status: rLowHighNonInt.status, errors: rLowHighNonInt.errors,
             expectedKind: feUnsupportedExprKind, hasKindCheck: true),

  CorpusItem(label: "A1: itMultiVariant (multi-case-object) constructor",
             surface: "1. parser catch-all",
             backstops: "Round-6 A1 (ADR-0029 — itVariant/itMultiVariant " &
                        "arm split; itMultiVariant construction stays a " &
                        "classified decline)",
             status: rMultiVariant.status, errors: rMultiVariant.errors,
             expectedKind: feUnsupportedExprKind, hasKindCheck: true),

  CorpusItem(label: "A3: symbolic-disc variant construction past maxVariantConstructorForks",
             surface: "4. walk-time resource-budget decline",
             backstops: "Round-6 A3 (ADR-0029 — isVariantConstructSym's " &
                        "maxVariantConstructorForks structural budget, " &
                        "reusing the beBudgetExhausted kind the " &
                        "maxLoopUnwind/maxFrontierSize precedents use)",
             status: rVariantConstructBudget.status, errors: rVariantConstructBudget.errors,
             expectedKind: beBudgetExhausted, hasKindCheck: true),

  CorpusItem(label: "B2: narrowing int conversion (uint8(x) from int32)",
             surface: "1. parser catch-all",
             backstops: "Round-6 B2 (int-family width-conversion modeling — " &
                        "narrowing is a recorded decline, no truncate " &
                        "primitive modeled)",
             status: rNarrowIntConv.status, errors: rNarrowIntConv.errors,
             expectedKind: feUnsupportedExprKind, hasKindCheck: true),

  CorpusItem(label: "CR-2b: cstring SUT param",
             surface: "2. type-classifier catch-all",
             backstops: "CR-2b (classifyType param-type catch-all)",
             status: rCstring.status, errors: rCstring.errors,
             expectedKind: feUnsupportedParamType, hasKindCheck: true),

  CorpusItem(label: "CR-2c: seq[Widget] witness",
             surface: "2. witness-reader catch-all",
             backstops: "CR-2c (emitTyAndReader itSeq catch-all)",
             status: rSeqObject.status, errors: rSeqObject.errors,
             expectedKind: feUnsupportedWitnessType, hasKindCheck: true),

  CorpusItem(label: "CR-2c: HashSet[string] witness",
             surface: "2. witness-reader catch-all",
             backstops: "CR-2c (emitTyAndReader itSet catch-all)",
             status: rHashSetString.status, errors: rHashSetString.errors,
             expectedKind: feUnsupportedWitnessType, hasKindCheck: true),

  CorpusItem(label: "CR-2c: tuple nesting an unrenderable seq[Widget] field",
             surface: "2. witness-reader catch-all (nested-aggregate)",
             backstops: "CR-2c (recursive unrenderable-leaf predicate)",
             status: rNestedTuple.status, errors: rNestedTuple.errors,
             expectedKind: feUnsupportedWitnessType, hasKindCheck: true),

  CorpusItem(label: "SND-1: `acc /= 2.0` dropped-mutation taint",
             surface: "3. internal-fault / uncertain-taint",
             backstops: "SND-1 (isUnsupported taints Path.uncertain)",
             status: rDivAssign.status, errors: rDivAssign.errors,
             expectedKind: feUnsupportedOp, hasKindCheck: false),

  CorpusItem(label: "SND-1b: closure body drops `/=` mutation",
             surface: "3. internal-fault / uncertain-taint",
             backstops: "SND-1b (applyClosureGround skips uncertain sub-paths)",
             status: rClosureBody.status, errors: rClosureBody.errors,
             expectedKind: ceClosureBodyUncertain, hasKindCheck: true),

  CorpusItem(label: "SND-1b: closure body's internal call bails on maxCallDepth",
             surface: "3. internal-fault / uncertain-taint",
             backstops: "SND-1b (applyClosureGround skips uncertain sub-paths)",
             status: rClosureDepth.status, errors: rClosureDepth.errors,
             expectedKind: ceClosureBodyUncertain, hasKindCheck: true),

  CorpusItem(label: "CR-1c: injected unanticipated internal walker fault",
             surface: "3. internal-fault / uncertain-taint",
             backstops: "CR-1c (narrow last-resort runSymex catch)",
             status: rInternalFault.status, errors: rInternalFault.errors,
             expectedKind: weInternalWalkerFault, hasKindCheck: true),

  CorpusItem(label: "Bug #2: direct READ of a scoped-decline placeholder field",
             surface: "5. per-field scoped decline (read-taint)",
             backstops: "Round-6 Bug #2 (dsl_parser.nim nnkDotExpr field-read " &
                        "arm's classified decline — mere ALLOCATION of the " &
                        "containing object/variant no longer poisons the " &
                        "run; only a direct read of the placeholder field " &
                        "itself degrades)",
             status: rUnsupportedFieldRead.status, errors: rUnsupportedFieldRead.errors,
             expectedKind: seNestedSeqUnsupported, hasKindCheck: true),

  CorpusItem(label: "R1: `.len` READ of a BARE call-return placeholder (no declared field)",
             surface: "5. per-field scoped decline (read-taint)",
             backstops: "R1 (placeholder read-totality chokepoint, walker v89 -- " &
                        "`iekSeqLen`'s `svSeq` arm now declines instead of " &
                        "returning the forced-`==0` length directly; a " &
                        "genuinely NEW reachable decline surface distinct " &
                        "from the field-read row above, since a bare value " &
                        "has no static field-access site for the parser to " &
                        "intercept)",
             status: rBareLenRead.status, errors: rBareLenRead.errors,
             expectedKind: seNestedSeqUnsupported, hasKindCheck: true),

  CorpusItem(label: "A6-rider: composite-typed implicit-result call fallthrough",
             surface: "3. internal-fault / uncertain-taint",
             backstops: "Round-6 A6-rider (isCall's implicit-fallthrough " &
                        "retSym binding — a composite return kind outside " &
                        "the scalar/tuple/variant wired set mirrors " &
                        "isReturn's own existing composite-return degrade " &
                        "net rather than leaving retSym unconstrained)",
             status: rCompositeFallthrough.status, errors: rCompositeFallthrough.errors,
             expectedKind: feUnsupportedOp, hasKindCheck: false),
]

# =============================================================================
# B2 same-width signedness reinterpret — CAPABILITY GAIN (9019d90), NOT a §0
# corpus row. Kept in this file (rather than only in
# tsymex_phase15_A1_bitwise.nim, which independently pins the same fix via
# its own cell 6 chronos-faithful repro) because this is the cell's
# HISTORICAL HOME — a silent regression back to the pre-9019d90 decline would
# otherwise only be caught elsewhere, defeating the "a regression in the
# underlying fix trips THIS file too" contract this file's header states.
# =============================================================================

suite "symex TOT-1 — B2 same-width reinterpret: sxSat capability + soundness companion":

  test "B2/9019d90: uint32(x) from int32 now resolves a REAL sxSat witness (x == 42), never the pre-fix decline":
    check rReinterpretIntConv.status == sxSat
    check rReinterpretIntConv.status != sxUnknown  ## the pre-9019d90 behavior
    check int32(rReinterpretIntConv.witness[0]) == 42'i32

  test "B2/9019d90 SOUNDNESS: the tag-flip reinterpret never equates u == 42'u32 for any x other than 42":
    check rReinterpretIntConvSoundness.status == sxUnsat
    check rReinterpretIntConvSoundness.status != sxSat  ## would be a false witness

# =============================================================================
# The §0 invariant, applied uniformly across every corpus row.
# =============================================================================

suite "symex TOT-1 — §0-totality regression corpus":

  test "corpus is non-empty (sanity — a silently-empty table would vacuously pass)":
    check corpus.len >= 8

  for item in corpus:
    test "§0 [" & item.surface & "] " & item.label & " -> classified sxUnknown, never crash/false-sat":
      ## The core §0 assertion (see `item.backstops` for which fix this
      ## backstops): reaching this check at all already proves no native
      ## crash and no macro-error() compile abort occurred (both would have
      ## prevented this test binary from existing). The three explicit
      ## status checks below then rule out every remaining false-verdict
      ## shape §0 forbids.
      check item.status == sxUnknown
      check item.status != sxSat    ## never a false witness
      check item.status != sxUnsat  ## never a false "unreachable" claim
      if item.hasKindCheck:
        check hasKind(item.errors, item.expectedKind)

  test "walker version floor >= 46 (every surface exercised here landed by CR-2c/v46)":
    ## Floor-idiom pin (RFC §Version-pin discipline): this incidental
    ## feature-test pin uses the tolerant `>=` floor — only the canonical
    ## tsymex_phase15_CR2_cachekey.nim keeps the brittle `==` conscious-bump
    ## gate. All three §0 surfaces this corpus exercises (CR-2a/b/c, SND-1,
    ## SND-1b, CR-1c) landed at or before walker v46.
    check parseInt(symexWalkerVersion) >= 46
