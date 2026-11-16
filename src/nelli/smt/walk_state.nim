## RFC-0016 review D3c-2. The per-run walk state the lowering layer reads, and
## the hooks it calls upward through: the second leaf `runtime.nim` and its
## four small `include` files compile against.
##
## `runtime.nim` is one 33k-line module whose includes share its namespace.
## This leaf is the part of that namespace the includes need and that depends
## on nothing later in the file:
##
##   * the per-run lowering threadvars (the raise-predicate sinks, the
##     regex and strip sinks, the closure and ref-sort caches, the in-flight
##     exception mirror), all reset together by `resetWalkState`;
##   * `LowerSinks`, the lists the `sync*` family appends to while a walk is
##     active. `WalkCtx` embeds one (`w.sinks`) and the walk publishes its
##     address in `currentLowerSinks`, exactly where it publishes
##     `currentWalkCtxPtr`; the `sync*` procs are direct appends on that
##     pointer, nil-guarded as before: with no walk active the deposit is
##     dropped;
##   * `LowerHooks`, a record of `{.nimcall.}` procs for the verbs an include
##     calls that are defined later than it (`lower`, `lowerClosureCall`,
##     `seqElemAt`, `storeSeqElem`, `sameSymVal`, `entryValueOf`). It is
##     filled once, at `runtime.nim` module init, before any walk.
##
## A threadvar added here MUST be reset in `resetWalkState`: a value left over
## from the previous run holds Z3 terms of a freed context.
##
## Imports only `symval` and the existing leaves; the census
## (`tests/tsymex_0016_d3_include_census.nim`) pins that.
import std/tables
import std/options
import z3
import ./types
import ./symval
import ./definedness
import ./errorkind
import ./pcre_syntax

type
  RaiseSinkKind* = enum
    ## RFC-0005 S8bb. Which raise sink a deposit went to, in the order
    ## `drainScalarRaiseForks`'s fixed fallback drains them (see
    ## `WalkCtx.raiseOrder`).
    rskClosure, rskConvBound, rskParseInt, rskDivByZero, rskOverflow,
    rskArithTrap, rskStrIndex, rskSeqOob, rskRange, rskRegex,
    rskUninitRead,   ## RFC-0005 S8bv: not a raise, a taint fork
    rskClosureExit
      ## RFC-0005 S8bi. Not a raise: one closure exit fact
      ## (`currentClosureExitPc`, one entry per fact), logged where the call
      ## completed. A raise evaluated before the call is forked without it;
      ## every survivor of the stages before it gains it.

type DistinctSortEntry* = object
  sort*:    Z3Sort[stUninterpreted]    ## the fresh "DistinctName" sort
  inject*:  RawZ3FuncDecl              ## inject_T: Base → Distinct
  eject*:   RawZ3FuncDecl              ## eject_T: Distinct → Base

type ConvBound* = object
  ## K10a-float. One `convFloatToIntBoundConds` deposit: the conversion's
  ## in-range domain, and the source site that names its undefined side.
  cond*: Z3Bool
  site*: string
  cls*: OperandClass   ## the `convert/` row (`floatToIntLowering`)

proc convBoundOf*(domain: Z3Bool, site: string, cls: OperandClass): ConvBound =
  ConvBound(cond: domain, site: site, cls: cls)

type ArithTrap* = object
  ## RFC-0016 W1-d1a. One `arithTrapConds` deposit: the trap predicate, and
  ## whether the C division is UNDEFINED there rather than a definite
  ## hardware outcome. `ub` names the kind the deposit halts with
  ## (`ubIntMinModMinusOne` for `low(T) mod -1`; `ubSignedOverflow` for
  ## `low(T) div -1` with overflow checks off, at 32 and 64 bits) and `site`
  ## the construct for the omission's text; `none` is a definite outcome.
  ## `drainArithTraps` halts a `some` deposit through `haltUndefined`; the
  ## rest still confine the survivor.
  cond*: Z3Bool
  ub*: Option[UbKind]
  site*: string
  raiseName*: string
    ## RFC-0016 PRC-07 (float half). Non-empty: not a trap but Nim's float
    ## check after a float `+ - * /` (`FloatInvalidOpDefect`,
    ## `FloatOverflowDefect`), an ordinary catchable raise forked on `cond`.
    ## It rides this sink so the checks of one expression stay in evaluation
    ## order: each deposit's raise is forked after the earlier ones' negations.

type ParseIntRaise* = object
  ## RFC-0005 S10. One `parseInt(s)` lowering's raise obligation, SPLIT by
  ## whether the model is Nim's `parseutils.rawParseInt` on the inputs it
  ## covers. Nim accepts `_` separators after a digit; the model cannot
  ## compute their value (`str.replace_all` is version-gated), so:
  ##   * `exact` -- the raise predicate restricted to strings with no `_`:
  ##     there the model is Nim's (RFC-0005 S8b: one optional `+`/`-` sign,
  ##     then digits only, in `int` range). Forked CLEAN.
  ##   * `lax`   -- a `_` anywhere: Nim may raise or parse. Both the raise
  ##     fork and the continuation (on a fresh value) are `scSpurious`-tainted
  ##     (`seParseIntLaxSyntax`, `dcFreshSymbol`) -- candidates that only a
  ##     confirming replay may report (RFC-0005 §2.6).
  ## S10 had `+` in the lax half too, and the digits survivor carried `not
  ## lax`: every `+`/`_` string was dropped from the continuation, a false
  ## `sxUnsat` for a target reachable only through one (S8b).
  exact*: Z3Bool
  lax*:   Z3Bool

type ClosureSymKey* = tuple[siteHash: int64, declOrder: int,
                            envSortId: string, paramsSortTupleId: string]
  ## Phase 15 C2a (ADR-0009). The memo key: the lambda-site identity PLUS the
  ## construction-time env/param sort fingerprints (so the SAME site at two
  ## monomorphizations — distinct leaf/param sorts — gets distinct funcSyms).

type ClosureBody* = object  ## Phase 15 C2b. The descent payload for a lambda
                            ## site, stashed at construction so the CALL can
                            ## reach the body that `svClosure` does not carry.
  body*:     IRStmt
  params*:   seq[IRParam]
  captures*: seq[string]
  retTy*:    IRType
  aliasPairs*:  seq[tuple[keep, gone: int]]   ## RFC-0005 S8bh (`lambdaAliasPairs`)
  aliasBodies*: seq[IRStmt]                   ## RFC-0005 S8bh
  ptrLocal*:    seq[bool]                     ## RFC-0005 S8bh (`lambdaPtrLocal`)
  outer*:       seq[string]                   ## RFC-0005 S8bh (`lambdaOuter`)

type RegexPointSite* = object
  ## RFC-0005 S8cf. A `std/re` call `checkCapped` reads at the points the
  ## search proposes before it tries Z3's encoding (`pointCheck`): its value
  ## as the query reads it (`exact`), the assertions that only define it
  ## (`defs`, their ids) and its operands. `declined`: the encoding is past
  ## its size cap, so `exact` is a fresh value with nothing else defining it.
  ## `light`: Z3 reads this encoding well, so a query only takes its value at
  ## a subject pinned beside a call that is not (`pointCheck`'s pinned round).
  exact*: Z3AnyAst
  defs*: seq[int]
  subject*, by*: Z3String
  start*: Z3Int
  sp*: RegexSpec
  pr*: PcreParse
  safe*: int       ## `limitReach`'s safe length (`high(int)`: no limit)
  declined*: bool
  light*: bool

type RegexLimitSite* = object
  ## RFC-0005 S8cf. One `std/re` call whose subject can be long enough to
  ## reach one of PCRE's own limits (`pcre_select.LimitReach`): its value as
  ## the model reads it (`exact`), what std/re surfaces if the limit is hit
  ## (`err`, with `errConds`), the subject and the length up to which no
  ## limit can be hit (`safe`), and the assertions true only of `exact`
  ## (`guarded`: a recursive `replace` value's definition and facts).
  exact*, err*: Z3AnyAst
  errConds*: seq[Z3Bool]
  subject*: Z3String
  safe*: int
  guarded*: seq[int]
  what*: string

var currentWalkCtxPtr* {.threadvar.}: pointer
  ## Phase 15 C2b. A `ptr WalkCtx` to the live walk, set in `runSymexImpl`
  ## immediately before the top-level `walk` so `lowerClosureCall` (running in
  ## the `lower` evaluator, which has no `WalkCtx` parameter) can drive a body
  ## descent through `walk`. Typed `pointer` because `WalkCtx` is declared far
  ## below `lower`; cast back at use. Nil outside an active walk (the C2a probes
  ## and `c1ClosurePoCApply` never set it — they don't reach `iekClosureCall`).
  ## CR-9 Stage 4: also used by `allocRefSort`/`assertFreshness` (pre-WalkCtx
  ## procs) via `syncRefSortEntry` to populate `WalkerStatics.refSorts/nilConsts`
  ## during an active walk.

var currentRefSorts* {.threadvar.}: Table[string, RawZ3Sort]
  ## Phase 15 R1 (ADR-0010). Per-run cache of `Ref_T` uninterpreted sorts,
  ## keyed by pointee typeId. The LIVE populator (`allocateSym(itRef)` /
  ## `allocRefSort`); reset at `runSymexImpl` entry; mirrored into
  ## `WalkerStatics.refSorts`. Allocated AT MOST ONCE per (typeId, run).

var currentNilConsts* {.threadvar.}: Table[string, Z3AnyAst]
  ## Phase 15 R1 (ADR-0010). The `nil_<typeId>` distinguished constant of each
  ## `Ref_T` sort. Allocated alongside the sort in `allocRefSort`; reset at
  ## `runSymexImpl` entry; mirrored into `WalkerStatics.nilConsts`.

var currentDistinctSorts* {.threadvar.}: Table[string, DistinctSortEntry]
  ## Phase 15 G4. Per-run cache of distinct sorts + their inject/eject
  ## func-decls, keyed by distinct type name. Reset at `runSymexImpl` entry.
  ## Shared across all call frames (one entry per distinct type per run) — the
  ## sort allocation + bijectivity axioms fire AT MOST ONCE per (name, run).

var currentClosureSyms* {.threadvar.}: Table[ClosureSymKey, RawZ3FuncDecl]
  ## Phase 15 C2a. Per-run cache of per-site closure funcSyms. Reset at
  ## `runSymexImpl` entry; the LIVE populator (`lower(iekLambda)` has no
  ## `WalkCtx`). Mirrored into `WalkerStatics.closureSyms` after the walk.

var currentClosureBodies* {.threadvar.}: Table[
    tuple[siteHash: int64, declOrder: int], ClosureBody]
  ## Phase 15 C2b. Per-run site→body map (the body `svClosure` does not carry).
  ## Populated by `buildClosure` (C2a construction path), consumed by
  ## `lowerClosureCall` (C2b application). Reset at `runSymexImpl` entry.

var currentMaxSplitParts* {.threadvar.}: int
  ## CR-11/CR-18. The active `SymexSettings.budget.maxSplitParts`, set at the
  ## top of `runSymexImpl` so the `iekStrSplit` concrete-inline arms in
  ## `lowerStrArm` can enforce the cap without threading settings through the
  ## lower() recursion. Mirrors F7's `extractionErrors` threadvar idiom.
  ## A value of 0 means unlimited (no cap applied). When the computed parts
  ## count exceeds this cap, the split is classified sxUnknown via
  ## SymexZ3StringIncompleteError (seZ3StringIncomplete) — the same error
  ## kind used by the general symbolic split path — rather than emitting
  ## potentially thousands of Z3 store calls (compile-time DoS prevention).

var convFloatToIntBoundConds* {.threadvar.}: seq[ConvBound]
  ## Phase 15 CR-3/CR-4; RFC-0005 S8g. The in-range DOMAIN of each float ->
  ## int conversion lowered by `lower(iekConvFloatToInt)` (the operand's
  ## truncation fits the target type). The lowered value is
  ## `ite(domain, exact, fresh)`; `drainConvFloatToIntFresh` (a stage of
  ## `drainScalarRaiseForks`) forks the continuation on it -- clean in range,
  ## `feConvFloatToIntUndefined`-tainted out of range. Until S8g the walker
  ## NARROWED the path to the domain here and raised `RangeDefect` outside it
  ## (ADR-0011 R16-2, reversed: Nim never raises there). Reset at each
  ## `lower` call-site in the walker (before the call). Reset at
  ## `runSymexImpl` entry.

var rangeDefectConds* {.threadvar.}: seq[Z3Bool]
  ## RFC-0005 S8g. Raise-fork sink for `RangeDefect` predicates deposited by
  ## a lowering: a `range` target's check on a float -> int conversion
  ## (`Natural(f)`), a negative slice length (`s[a .. b]` with `b < a - 1`),
  ## and `del`'s `Natural` index. Drained by `drainRangeRaises` (a
  ## `genRaiseForkDrain`, gated by `acRange`). The name was R16-2's parallel
  ## float -> int domain sink, retired with that model; this is a plain
  ## raise-predicate sink like `seqOobConds`. `syncRangeDefectCond` appends
  ## here when in a walk.

var divByZeroConds* {.threadvar.}: seq[Z3Bool]
  ## Phase 16 R16-3. Raise-fork sink for div/mod-by-zero predicates.
  ## `lowerArith` pushes `divisorIsZero(b)` here for every `bDiv`/`bMod`
  ## op on svInt or BV operands. `drainDivByZeroRaises` (called via
  ## `drainScalarRaiseForks`) reads and resets this sink, forking each
  ## predicate as a `DivByZeroDefect` raise path. The surviving non-zero
  ## continuation carries the negated predicates in its pc.
  ## `syncDivByZeroCond` appends to `WalkCtx.divByZeroConds` when in a walk.
  ## Reset alongside `convFloatToIntBoundConds`/`rangeDefectConds`
  ## at every reset site.

var overflowConds* {.threadvar.}: seq[Z3Bool]
  ## Phase 16 R16-4. Raise-fork sink for signed integer overflow predicates.
  ## `lowerArith` pushes overflow conditions here for bAdd/bSub/bMul ops on
  ## signed BV operands (int, int8..int64). `drainOverflowRaises` (called via
  ## `drainScalarRaiseForks`) reads and resets this sink, forking each predicate
  ## as an `OverflowDefect` raise path. The surviving non-overflow continuation
  ## carries the negated predicates in its pc.
  ## `syncOverflowCond` appends to `WalkCtx.overflowConds` when in a walk.
  ## svInt (unbounded Z3Int) is skipped — overflow is meaningless there AND BV
  ## predicates on Int terms hang Z3. Unsigned BV is skipped — Nim wraps silently.
  ## Reset alongside `divByZeroConds` at every reset site.

var strIndexOobConds* {.threadvar.}: seq[Z3Bool]
  ## RFC-chapulin-hardening SND-4 (ADR-0024). Raise-fork sink for string-index
  ## (`s[i]`) out-of-bounds predicates. `lowerStrArm`'s `iekStrAt` arm pushes
  ## `(idx < 0) or (idx >= len(s))` here for every `s[i]` (char read) lowered.
  ## `drainStrIndexRaises` (called via `drainScalarRaiseForks`) reads and
  ## resets this sink, forking each predicate as a routed `IndexDefect` raise
  ## path — parity with the seq/array/Table indexing arms, which already fork
  ## `IndexDefect` unconditionally (Phase 16 D1a); `s[i]` was the sole
  ## container-index site with zero bounds modeling (an OOB read silently
  ## degraded to a fabricated byte value via Z3's `at`/`toCode` spec instead of
  ## raising). The surviving in-bounds continuation carries the negated
  ## predicates as `defectSurvivorPc` facts (ADR-0012), exactly like
  ## `parseIntRaiseConds`/`divByZeroConds`/`overflowConds`.
  ## `syncStrIndexOobCond` appends to `WalkCtx.strIndexOobConds` when in a walk.
  ## Reset alongside `overflowConds` at every reset site.

var regexRaiseMsgs* {.threadvar.}: seq[string]
  ## RFC-0005 S8ay. `RegexError` raises of an expression: one message per
  ## `re"..."` / `rex"..."` whose pattern PCRE rejects (Nim's exact
  ## `RegexError.msg`, from `pcre_syntax`). The raise is unconditional --
  ## `re` compiles the pattern each time the call runs -- so the sink holds
  ## messages, not predicates. `drainRegexRaises` (the LAST stage of
  ## `drainScalarRaiseForks`) routes the first as a `RegexError` raise and
  ## ends the continuation. `syncRegexRaiseMsg` appends to
  ## `WalkCtx.regexRaiseMsgs` when in a walk. Reset alongside
  ## `arithTrapConds` at every reset site.

var parseIntRaiseConds* {.threadvar.}: seq[ParseIntRaise]
  ## Phase 15 S10b. Raise predicates emitted by the `iekStrToInt` (`parseInt`)
  ## lowering — one `(not isNeg) and (posVal < 0)` clause per `parseInt` lowered
  ## (the non-digit, non-`-`-prefixed case, where Nim's runtime RAISES
  ## `ValueError`). `lower` cannot route a raise itself (no WalkCtx/Path), so the
  ## predicate is surfaced here and DRAINED by the enclosing statement walk arm
  ## (`drainParseIntRaises`), which forks a routed-`ValueError` raise sub-path and
  ## a digits continuation. Reset before each lower-and-drain so predicates never
  ## leak across paths/statements. Closes the S10a `seParseIntPreE` window — that
  ## hint is no longer emitted.

var regexRecDefConds* {.threadvar.}: seq[Z3Bool]
  ## RFC-0005 S8bj. The definitions `r == rec(s)` of the `replace` values
  ## lowered by a recursive function (`runtime_strings.regexReplaceRec`),
  ## each over its own fresh `r`: definitional, asserted in every query
  ## (`globalRoots`). `checkCapped` first tries a query WITHOUT them (the
  ## value's facts, `regex_parser.replaceLemmas`, stay): its models are a
  ## superset of the real ones, so its UNSAT is the query's own; Z3's
  ## unfolding of the recursive term never reaches the facts' conflict
  ## (S8bb's Q7, Q8: `replace(s, re"a", "").contains("a")`).

var regexRecFactConds* {.threadvar.}: seq[Z3Bool]
  ## RFC-0005 S8bt. The facts of the `replace` values in `regexRecDefConds`
  ## (`regex_parser.replaceLemmas`): each over one occurrence's own `r`,
  ## its receiver and `by`, and fresh Ints (the match count, the bytes
  ## removed), and true of every receiver, so they prune no real model.
  ## `checkCapped` asserts them where it leaves the definitions out, and
  ## leaves both out of the steps after it (each `r` replaced by its term).
  ## S8bj put them in `stripDecompConds`.

var regexPointSites* {.threadvar.}: seq[RegexPointSite]
  ## RFC-0005 S8cf. Every such call of the walk. Reset per run.

var regexLimitSites* {.threadvar.}: seq[RegexLimitSite]
  ## RFC-0005 S8cf. Every such call of the walk (`checkCapped`). Reset per
  ## run.

var stripDecompConds* {.threadvar.}: seq[Z3Bool]
  ## Round-4 Slice B (ADR-0026). Decomposition constraints emitted by the
  ## `iekStrStrip` lowering: for `strip(s, leading, trailing, chars)` with a
  ## literal char set, fresh strings `pre`/`core`/`suf` are allocated and
  ##   s == pre ++ core ++ suf
  ##   pre ∈ (union chars)*    (leading; else pre == "")
  ##   suf ∈ (union chars)*    (trailing; else suf == "")
  ##   core == "" ∨ (¬startsWith(core, c) ∀c   when leading
  ##                 ∧ ¬endsWith(core, c) ∀c   when trailing)
  ## are pushed here and drained into EVERY solver check (`trySolve`) —
  ## exactly the `currentClosureCallAxioms` idiom.
  ## GLOBAL assertion is sound because the clauses are DEFINITIONAL: for
  ## every value of `s` there exists exactly ONE satisfying assignment of
  ## (pre, core, suf) — the maximal-strip decomposition (maximality is
  ## forced by the boundary clause: were `suf` non-maximal, `core` would
  ## end in a stripped char) — so conjoining them never prunes a model of
  ## any other variable, and `core` is FORCED to `strutils.strip`'s exact
  ## value (soundness AND completeness, no over-approximation). The
  ## fragment is quantifier-free string+regex (concat / prefixof /
  ## suffixof / re.star over a finite literal char union) — the same
  ## decidable machinery class as S6b regex membership; no Int/BV mixing
  ## (the CR-17 hang shape). Reset at `runSymexImpl` entry.

var stripSynthCounter* {.threadvar.}: int
  ## Round-4 Slice B. Per-run unique-name counter for `iekStrStrip`'s fresh
  ## `pre`/`core`/`suf` allocations — two strip occurrences MUST NOT share
  ## Z3 consts (same name = same const = unsound cross-linking). Reset at
  ## `runSymexImpl` entry.

var currentInFlightTypeId* {.threadvar.}: Option[string]
  ## Phase 15 E8. The in-flight exception's TYPE id while an `except` handler
  ## body is being walked (mirrors `w.frame.inFlightExn.get.typeId`). `none`
  ## outside any handler. The two `getCurrent*` magic intrinsics lower in
  ## `lower` (a pure Env→SymVal function with no WalkCtx/frame access), so the
  ## walk arms that set/clear `w.frame.inFlightExn` keep this threadvar in
  ## lockstep. A `none` value at lower time means the intrinsic was called
  ## out-of-handler → `SymexNotInHandlerError`. Mirrors the F7/S7a/S10 threadvars.

var currentInFlightMsg* {.threadvar.}: Option[string]
  ## Phase 15 E8. The in-flight exception's MESSAGE (mirrors
  ## `w.frame.inFlightExn.get.msg`) while an `except` handler body is walked.
  ## `none` if the raise carried no message (zero-arg object construction);
  ## `getCurrentExceptionMsg()` returns `currentInFlightMsg.get("")`.

var currentExnRefCounter* {.threadvar.}: int
  ## Phase 15 E8. Monotonic counter for fresh `getCurrentException()` constant
  ## names, so distinct call sites get distinct uninterpreted constants. Reset
  ## per run in `runSymexImpl`.

var lastGetCurrentExnRef* {.threadvar.}: tuple[sortName, typeTag: string]
  ## Phase 15 E8 (test hook). Records the `sortName`/`typeTag` of the most
  ## recently produced `getCurrentException()` `svUninterpRef`. The returned
  ## opaque ref is not witness-extractable through `symexFind`, so E8's test 2
  ## inspects this threadvar to assert the tagging (`Exn_<typeId>` / `typeId`).

type LowerSinks* = object
  ## RFC-0016 review D3c-2. What the `sync*` family appends to while a walk is
  ## active: the walk's own copy of each raise-predicate sink, the hint and
  ## error lists, and the per-walker ref-sort, distinct-sort and closure
  ## caches. `WalkCtx.sinks` embeds one; `currentLowerSinks` points at it for
  ## the duration of the walk. Before this object these were fields of
  ## `WalkCtx` and `WalkerStatics`, written through a cast of
  ## `currentWalkCtxPtr`; the threadvar of the same name (above) remains the
  ## store for probe paths with no walk.
  refSorts*: Table[string, RawZ3Sort]
  nilConsts*: Table[string, Z3AnyAst]
  distinctSorts*: Table[string, DistinctSortEntry]
  distinctSortNames*: seq[string]
  closureSyms*: Table[ClosureSymKey, RawZ3FuncDecl]
  closureBodies*: Table[tuple[siteHash: int64, declOrder: int], ClosureBody]
  freshnessCapHints*: seq[SymexErrorInfo]
  distinctBijectivityHints*: seq[SymexErrorInfo]
  extractionErrors*: seq[SymexErrorInfo]
  closureCallErrors*: seq[SymexErrorInfo]
  rangeDefectConds*: seq[Z3Bool]
  divByZeroConds*: seq[Z3Bool]
  overflowConds*: seq[Z3Bool]
  strIndexOobConds*: seq[Z3Bool]
  seqOobConds*: seq[Z3Bool]
  uninitReadConds*: seq[Z3Bool]
  convFloatToIntBoundConds*: seq[ConvBound]
  parseIntRaiseConds*: seq[ParseIntRaise]
  regexRaiseMsgs*: seq[string]
  arithTrapConds*: seq[ArithTrap]
  raiseOrder*: seq[RaiseSinkKind]
    ## RFC-0005 S8bb. The evaluation-order log of the raise sinks above: every
    ## deposit appends the sink it went to, so `drainScalarRaiseForks` forks
    ## the expression's raises in the order they were evaluated.

var currentLowerSinks* {.threadvar.}: ptr LowerSinks
  ## `addr w.sinks` of the live walk, set and cleared exactly where
  ## `currentWalkCtxPtr` is. Nil outside an active walk (the probe paths), when
  ## every `sync*` deposit is dropped.

# ---- the sync* family: direct appends on the live walk's sinks ----------

proc syncRefSortEntry*(typeId: string, srt: RawZ3Sort, nc: Z3AnyAst) =
  ## CR-9 Stage 4 (currentRefSorts/currentNilConsts migration). If
  ## `currentLowerSinks != nil` (a walk is active), copies `srt` and `nc` into
  ## `LowerSinks.refSorts[typeId]` and `.nilConsts[typeId]` so that
  ## `WalkerStatics` becomes the LIVE store for the ref-sort cache during a walk.
  ## When `currentLowerSinks == nil` (probe paths: C2a construction probes,
  ## `allocateSym(itRef)` outside a walk), this is a no-op; the threadvar cache
  ## (`currentRefSorts`/`currentNilConsts`) remains the sole store for those paths.
  if currentLowerSinks != nil:
    currentLowerSinks[].refSorts[typeId] = srt
    currentLowerSinks[].nilConsts[typeId] = nc

proc syncDistinctSortEntry*(name: string, entry: DistinctSortEntry) =
  ## CR-9 Stage 4 (currentDistinctSorts/distinctSortNames migration). If
  ## `currentLowerSinks != nil` (a walk is active), copies `entry` into
  ## `LowerSinks.distinctSorts[name]` and appends `name` to
  ## `.distinctSortNames`. No-op when no active walk (probe paths and pre-walk
  ## env-setup calls); `currentDistinctSorts`/`distinctSortNames` threadvars
  ## remain the sole store for those paths.
  if currentLowerSinks != nil:
    currentLowerSinks[].distinctSorts[name] = entry
    currentLowerSinks[].distinctSortNames.add name

proc syncClosureSymEntry*(key: ClosureSymKey, fd: RawZ3FuncDecl) =
  ## CR-9 Stage 4 (currentClosureSyms migration). If `currentLowerSinks != nil`
  ## (a walk is active), copies `fd` into `LowerSinks.closureSyms[key]`
  ## so that `WalkerStatics.closureSyms` is the LIVE store during a walk.
  ## No-op when no active walk (C2a construction probes and probe functions
  ## that directly reset/read `currentClosureSyms`); the threadvar remains
  ## the sole store for those paths.
  if currentLowerSinks != nil:
    currentLowerSinks[].closureSyms[key] = fd

proc syncClosureBodyEntry*(siteKey: tuple[siteHash: int64, declOrder: int],
                           cb: ClosureBody) =
  ## CR-9 Stage 4 (currentClosureBodies migration). If `currentLowerSinks != nil`
  ## (a walk is active), copies `cb` into `LowerSinks.closureBodies[siteKey]`
  ## so that `WalkerStatics.closureBodies` is the LIVE store during a walk.
  ## No-op when no active walk; `currentClosureBodies` remains the sole store.
  if currentLowerSinks != nil:
    currentLowerSinks[].closureBodies[siteKey] = cb

proc syncFreshnessCapHint*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (freshnessCapHints migration). If `currentLowerSinks != nil`
  ## (a walk is active), appends `info` to `LowerSinks.freshnessCapHints` so that
  ## the LowerSinks field is the LIVE store for this hint during a walk. No-op when
  ## `currentLowerSinks == nil` (probe paths, pre-walk assertFreshness calls);
  ## the `freshnessCapHints` threadvar remains the sole store for those paths.
  if currentLowerSinks != nil:
    currentLowerSinks[].freshnessCapHints.add info

proc syncDistinctBijectivityHint*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (distinctBijectivityHints migration). If
  ## `currentLowerSinks != nil` (a walk is active), appends `info` to
  ## `LowerSinks.distinctBijectivityHints`. No-op when `currentLowerSinks == nil`
  ## (probe paths and pre-walk allocDistinctSym calls from env setup).
  if currentLowerSinks != nil:
    currentLowerSinks[].distinctBijectivityHints.add info

proc syncRangeDefectCond*(cond: Z3Bool) =
  ## RFC-0005 S8g. If `currentLowerSinks != nil`
  ## (a walk is active), appends `cond` to `LowerSinks.rangeDefectConds`
  ## so the field is the LIVE store for the raise-fork sink during a walk.
  ## No-op when `currentLowerSinks == nil` (probe-path lower() calls outside an
  ## active walk — no raise drain runs on probe paths).
  if currentLowerSinks != nil:
    currentLowerSinks[].rangeDefectConds.add cond
    currentLowerSinks[].raiseOrder.add rskRange   # RFC-0005 S8bb

proc syncExtractionError*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (extractionErrors migration). If `currentLowerSinks != nil`
  ## (a walk is active), appends `info` to `LowerSinks.extractionErrors` so the
  ## field is the LIVE store for extraction failures during a walk. No-op when
  ## `currentLowerSinks == nil` (extractLeaf/extractFromSymVal are called from
  ## trySolve which runs inside walk arms — ptr is always set at these sites —
  ## but the nil-guard ensures correctness if that assumption ever changes).
  if currentLowerSinks != nil:
    currentLowerSinks[].extractionErrors.add info

proc syncClosureCallError*(info: SymexErrorInfo) =
  ## CR-9 Stage 5 (currentClosureCallErrors migration). If
  ## `currentLowerSinks != nil` (a walk is active), appends `info` to
  ## `LowerSinks.closureCallErrors`. No-op when `currentLowerSinks == nil`
  ## (lowerClosureCall short-circuits early when ptr==nil, but
  ## applyClosureGround/lowerHofCall have nil-guard checks — this proc
  ## stays safe for all paths).
  if currentLowerSinks != nil:
    currentLowerSinks[].closureCallErrors.add info

proc syncConvFloatToIntBoundCond*(cond: ConvBound) =
  ## CR-9 Stage 6 Group-1 (convFloatToIntBoundConds migration). If
  ## `currentLowerSinks != nil` (a walk is active), appends `cond` to
  ## `LowerSinks.convFloatToIntBoundConds` so the field is the LIVE store for
  ## float→int domain-bound constraints during a walk. No-op when
  ## `currentLowerSinks == nil` (lower() can be called from probe paths via
  ## c1ClosurePoCApply / applyClosureGround outside an active walk).
  if currentLowerSinks != nil:
    currentLowerSinks[].convFloatToIntBoundConds.add cond
    currentLowerSinks[].raiseOrder.add rskConvBound   # RFC-0005 S8bb

proc syncParseIntRaiseCond*(cond: ParseIntRaise) =
  ## CR-9 Stage 6 Group-2. Appends `cond` to `LowerSinks.parseIntRaiseConds` (the
  ## LIVE store) when a walk is active; no-op on probe paths (currentLowerSinks
  ## == nil — no drain runs there).
  if currentLowerSinks != nil:
    currentLowerSinks[].parseIntRaiseConds.add cond
    currentLowerSinks[].raiseOrder.add rskParseInt   # RFC-0005 S8bb

proc syncDivByZeroCond*(cond: Z3Bool) =
  ## R16-3. div/mod-by-zero raise predicates. See syncParseIntRaiseCond.
  if currentLowerSinks != nil:
    currentLowerSinks[].divByZeroConds.add cond
    currentLowerSinks[].raiseOrder.add rskDivByZero   # RFC-0005 S8bb

proc syncOverflowCond*(cond: Z3Bool) =
  ## R16-4. signed-integer-overflow raise predicates. See syncParseIntRaiseCond.
  if currentLowerSinks != nil:
    currentLowerSinks[].overflowConds.add cond
    currentLowerSinks[].raiseOrder.add rskOverflow   # RFC-0005 S8bb

proc syncStrIndexOobCond*(cond: Z3Bool) =
  ## SND-4. string-index OOB raise predicates. See syncParseIntRaiseCond.
  if currentLowerSinks != nil:
    currentLowerSinks[].strIndexOobConds.add cond
    currentLowerSinks[].raiseOrder.add rskStrIndex   # RFC-0005 S8bb

proc syncSeqOobCond*(cond: Z3Bool) =
  ## N14. seq `del(i)` OOB raise predicates. See syncParseIntRaiseCond.
  if currentLowerSinks != nil:
    currentLowerSinks[].seqOobConds.add cond
    currentLowerSinks[].raiseOrder.add rskSeqOob   # RFC-0005 S8bb

proc syncRegexRaiseMsg*(msg: string) =
  ## RFC-0005 S8ay. See the forward declaration.
  if currentLowerSinks != nil:
    currentLowerSinks[].regexRaiseMsgs.add msg
    currentLowerSinks[].raiseOrder.add rskRegex   # RFC-0005 S8bb

proc syncUninitReadCond*(cond: Z3Bool) =
  ## RFC-0005 S8bv. An inline HOF's unwritten-element read condition. See
  ## syncParseIntRaiseCond.
  if currentLowerSinks != nil:
    currentLowerSinks[].uninitReadConds.add cond
    currentLowerSinks[].raiseOrder.add rskUninitRead

proc syncArithTrapCond*(cond: ArithTrap) =
  ## RFC-0005 S8i. Survivor-only arithmetic-trap predicates. See
  ## syncParseIntRaiseCond.
  if currentLowerSinks != nil:
    currentLowerSinks[].arithTrapConds.add cond
    currentLowerSinks[].raiseOrder.add rskArithTrap   # RFC-0005 S8bb

# ---- the upward verbs -----------------------------------------------------

var degradeSymCounter*  {.threadvar.}: int
  ## Round-6 re-review (item 3, walker v115; consolidated round-6 item 1).
  ## Single per-run unique-name counter shared by EVERY fixed-name degrade
  ## fresh-placeholder allocation site (`iteSV`'s merge/uninterp arms,
  ## `eqBV`/`neBV`'s catch-alls, `cmpBV`, `svLeafEq`, `boolOrder`, `strArm`,
  ## the seq-slice/set/contains/uNot/strCmpOrdering/lowerBool/refEqOrder/
  ## strOrdering/seqLitUnsupported sites, ...). Z3 interns consts by
  ## `(name, sort)`; a fixed name would let two DIFFERENT degrade occurrences
  ## in the same run (same site, hit twice on two sibling paths, or two
  ## unrelated sites that happen to share a base name) silently alias the
  ## same Z3 symbol -- unsound cross-linking between two logically distinct
  ## placeholders. One shared int is sufficient (rather than one threadvar
  ## per site) because every call site routes through `freshDegradeName`,
  ## which embeds the site's own tag in the returned name -- the counter only
  ## needs to be monotonically unique WITHIN a run, not per-tag. Mirrors
  ## `currentBorrowReboxCounter`/`currentExnRefCounter`. Reset at
  ## `runSymexImpl` entry.
  ##
  ## NOT cache-key-relevant: `symexCacheKey` (canonicalize.nim) hashes only
  ## `canonicalize(prog)`/`canonicalize(target)`/`canonicalize(settings)` --
  ## the pre-walk IR/target/settings -- plus explicit z3/nim/walker/rendering
  ## version strings. These names are allocated inside the WALK (`lower`,
  ## reached only once Z3 solving is already underway) and never flow back
  ## into any of those four canonicalized values, so uniquifying them (or
  ## reordering the counter across all sites, as this consolidation does)
  ## cannot change any cache key. No walker-version bump.

proc freshDegradeName*(tag: string): string =
  ## Per-run-unique Z3 const name for a fixed-name degrade site: `tag` is the
  ## site's own base name (e.g. `"__cmpBVDegrade"`), and the returned name
  ## appends `"#" & <counter>` so repeat hits of the SAME site (or of two
  ## different sites in the same run) never collide on `(name, sort)`. See
  ## `degradeSymCounter`'s doc for the collision rationale and the proof that
  ## this is display/solver-internal only (not cache-key-relevant).
  inc degradeSymCounter
  tag & "#" & $degradeSymCounter

type LowerHooks* = object
  ## The verbs an include calls that `runtime.nim` defines after it. Each is a
  ## `{.nimcall.}` proc (no closure environment), filled once by `runtime.nim`
  ## at module init, after the procs exist and before any walk runs; the
  ## census pins that every field is non-nil. A hook costs one indirect call
  ## per arm entry, on the string, float, exception and closure expression
  ## kinds only. The hot verbs (`checkedSelect`, `forkPath`, `lower` inside
  ## `runtime.nim` itself) stay direct.
  lower*: proc(env: Env, e: IRExpr, proto: Option[SymVal]): SymVal {.nimcall.}
  lowerClosureCall*: proc(env: Env, e: IRExpr): SymVal {.nimcall.}
  seqElemAt*: proc(seqSV: SymVal, idx: Z3Int): SymVal {.nimcall.}
  storeSeqElem*: proc(dataRaw: Z3AnyAst, elemTy: IRType, idx: Z3Int,
                      val: SymVal): Z3AnyAst {.nimcall.}
  sameSymVal*: proc(a, b: SymVal): bool {.nimcall.}
  entryValueOf*: proc(name: string): SymVal {.nimcall.}
  iteSV*: proc(cond: Z3Bool, t, e: SymVal): SymVal {.nimcall.}
    ## The merge of two SymVals under a condition. Heavy (it reaches
    ## `allocateSym` and the degrade chokepoints), so it stays in
    ## `runtime.nim` and the float conversion calls it through here.
  allocateSym*: proc(ty: IRType, baseName: string, pcOut: var seq[Z3Bool],
                     stringBacked: bool, intOffsetPositions: seq[int]):
                     SymVal {.nimcall.}
    ## The type-directed allocator (RFC-0016 review D3c-5). Heavy: it reaches
    ## every value kind and the heap model. The closure builder reads sorts
    ## off throwaway representatives it makes.
  currentFrameId*: proc(): int {.nimcall.}
    ## The live walk's `CallFrameCtx.frameId`, or -1 outside a walk. It reads
    ## `WalkCtx`, which `runtime.nim` defines.
  registerCapCell*: proc(local: string; v: SymVal) {.nimcall.}
    ## Keeps a by-reference capture in the frame's env cell (RFC-0005 S8ax);
    ## it writes the frame of `WalkCtx`.
  depositStrIndexOob*: proc(oob: Z3Bool) {.nimcall.}
    ## A string element access outside its bounds (RFC-0016 PRC-07): the
    ## checked build's `IndexDefect` sink or the undefined-access deposit. It
    ## reads the build's check options and `arithTrapConds`, which
    ## `runtime.nim` owns.

var lowerHooks*: LowerHooks
  ## Written once at `runtime.nim` module init; read-only afterwards.

# ---- the per-run reset ----------------------------------------------------

proc resetWalkState*(maxSplitParts: int) =
  degradeSymCounter = 0                  ## the shared degrade-name counter
  ## RFC-0016 review D3c-2. The per-run reset of every threadvar of this
  ## module, called by `resetSymexRunState` before the run's context is
  ## built. `maxSplitParts` is the run's `budget.maxSplitParts` (0: no cap).
  currentLowerSinks = nil
  currentWalkCtxPtr = nil
  currentMaxSplitParts = maxSplitParts
  currentRefSorts = initTable[string, RawZ3Sort]()
  currentNilConsts = initTable[string, Z3AnyAst]()
  currentDistinctSorts = initTable[string, DistinctSortEntry]()
  currentClosureSyms = initTable[ClosureSymKey, RawZ3FuncDecl]()
  currentClosureBodies = initTable[
    tuple[siteHash: int64, declOrder: int], ClosureBody]()
  convFloatToIntBoundConds = @[]
  rangeDefectConds = @[]
  divByZeroConds = @[]
  overflowConds = @[]
  strIndexOobConds = @[]
  regexRaiseMsgs = @[]
  parseIntRaiseConds = @[]
  regexRecDefConds = @[]
  regexRecFactConds = @[]
  regexPointSites = @[]
  regexLimitSites = @[]
  stripDecompConds = @[]
  stripSynthCounter = 0
  currentInFlightTypeId = none(string)
  currentInFlightMsg = none(string)
  currentExnRefCounter = 0
  lastGetCurrentExnRef = (sortName: "", typeTag: "")
