## Phase 15 code-review CR-2: stale-cache soundness fix.
##
## CR-2 identified that four verdict-affecting SymexSettings fields were absent
## from `canonicalize(SymexSettings)`, letting two runs with different values
## hash to the SAME cache key and serve a stale verdict.
##
## This test file is the TDD RED→GREEN harness for CR-2:
##
##   Part 1: the four omitted fields now produce DISTINCT canonical strings.
##   Part 2: `maxSplitParts` still produces the SAME canonical string (deliberate
##           exclusion — unwired today, belongs in the key when wired, CR-18).
##
## Written as individual sub-tests so CI can pinpoint which setting was missed
## if a regression is introduced later.

import std/unittest
import nelli/smt/canonicalize
import nelli/smt/types

suite "Phase 15 CR-2 — four missing settings now in cache key":

  test "CR-2 sub-test 1: defectExclusions changes canonical form":
    ## Changing which defect families are excluded changes whether a raise
    ## becomes sxRaised vs suppressed (runtime.nim typeIdToDefectKind +
    ## defectExclusions membership test). Two settings differing ONLY in
    ## defectExclusions must hash differently.
    var s0 = defaultSymexSettings()
    var s1 = s0
    s0.defectExclusions = {dkOutOfMemoryDefect, dkStackOverflowDefect}
    s1.defectExclusions = {dkOutOfMemoryDefect}   # one fewer exclusion
    check canonicalize(s0) != canonicalize(s1)

  test "CR-2 sub-test 2: maxClosureInlineCount changes canonical form":
    ## Changing maxClosureInlineCount changes whether a closure descent
    ## triggers ceInlineBudgetExceeded → sxUnknown vs proceeds to sxSat.
    ## Two settings differing ONLY in maxClosureInlineCount must hash differently.
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxClosureInlineCount = s0.budget.maxClosureInlineCount + 1
    check canonicalize(s0) != canonicalize(s1)

  test "CR-2 sub-test 3: maxBytesEncodingLen changes canonical form":
    ## Changing maxBytesEncodingLen changes whether a bytes(s) materialisation
    ## triggers seBytesLengthTooLarge → sxUnknown vs expands (sxSat).
    ## Two settings differing ONLY in maxBytesEncodingLen must hash differently.
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxBytesEncodingLen = s0.budget.maxBytesEncodingLen + 1
    check canonicalize(s0) != canonicalize(s1)

  test "CR-2 sub-test 4: maxFreshnessAssertions changes canonical form":
    ## Changing maxFreshnessAssertions changes how many `newRef != prior`
    ## distinctness constraints are emitted. When the cap is hit, dropped
    ## inequalities allow Z3 to alias refs it otherwise could not → false-SAT
    ## direction. Two settings differing ONLY in maxFreshnessAssertions must hash
    ## differently.
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxFreshnessAssertions = s0.budget.maxFreshnessAssertions + 1
    check canonicalize(s0) != canonicalize(s1)

  test "CR-2/CR-18: maxSplitParts NOW INCLUDED in canonical form (wired)":
    ## CR-11/CR-18 wired maxSplitParts into the concrete-inline split paths.
    ## A cap change now gates whether a large-literal split yields sxSat or
    ## sxUnknown; the two settings must produce DISTINCT canonical forms.
    ## (Previously excluded as unwired per the original CR-2 audit comment;
    ## that comment has been updated to reflect the new wired status.)
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxSplitParts = s0.budget.maxSplitParts + 1
    check canonicalize(s0) != canonicalize(s1)

suite "Phase 15 CR-2 — version bumps":

  test "CR-2 sub-test 5: symexWalkerVersion is now 74":
    ## RFC-parser-normalization A2b (2026-08-13) bumps the walker version
    ## 72→73: classify-first restructure of the bAnd/bOr block — the
    ## boolean-vs-bitwise decision (`classifyType(n).ty.kind != itBool`, with
    ## an untyped-node carve-out mirroring `parseAtomicOperand`'s own) now
    ## precedes both operand parses, so the BITWISE and/or family (Nim gives
    ## it no short-circuit semantics — the RHS always evaluates) atomizes
    ## both operands through the SAME `parseAtomicOperand` chokepoint A2a
    ## gave the general infix family, depositing unconditionally in the
    ## outer preamble. The boolean short-circuit path (D1c's fast/guarded
    ## split) is untouched verbatim — constraint 1 is now enforced by branch
    ## exclusivity rather than by never reaching this block. CACHE-KEY bump,
    ## not a verdict bump, for the same positional-slot-renumbering reason as
    ## "72": every program with a compound BITWISE and/or operand gets a new
    ## canonical form (and cache key), even where the verdict is unchanged;
    ## boolean-only programs' keys do not move. See `symexWalkerVersion`'s
    ## own doc comment (`canonicalize.nim`) for the full writeup.
    ##
    ## (Prior: RFC-parser-normalization A2a (2026-08-13) bumped the walker
    ## version 71→72: introduces the `parseAtomicOperand` chokepoint (D2) and
    ## routes the clean general infix family (comparisons, arithmetic,
    ## shl/shr, xor), the borrow/rune-compare/nil-compare/pred-succ/
    ## string-concat bypass sites, and the `not`/unary-minus prefix arms
    ## through it (never the boolean bAnd/bOr path — constraint 1, A2b's
    ## scope, at the time — and never inside a while-guard condition parse —
    ## constraint 4, `ctx.inGuardCond`). This was also a CACHE-KEY bump, not
    ## a verdict bump, for the same positional-slot-renumbering reason.)
    ##
    ## (Prior: RFC-parser-normalization N0 (2026-08-13) bumped the walker
    ## version 70→71: completes the #147 `nnkFuncDef` acceptance widening at
    ## three sites `799b0bc` missed — `borrowInfoFor` (`dsl_parser.nim:855`,
    ## bare `impl.kind != nnkProcDef`), C3 proc-as-value
    ## (`dsl_parser.nim:1048`/`:1050`, bare `symKind(n) == nskProc` — `func`
    ## symbols are the distinct `nskFunc` kind, so the `impl.kind` gate
    ## below it was unreachable for `func` until this one widened), and G8
    ## string-op disambiguation (`dsl_parser.nim:2083`, positive-match
    ## `calleeSym.getImpl.kind == nnkProcDef`). The C3 and G8 fixes turn a
    ## classified `sxUnknown` (`weInternalWalkerFault` / `seUnsupportedStringOp`
    ## respectively) into a real verdict for previously-degraded `func`
    ## programs — a verdict-surface change, so the cache key rotates. The
    ## `borrowInfoFor` widen is separately verdict/witness-inert (pinned by
    ## `tsymex_phase15_N0_kindgate_widen.nim`'s characterization test) but
    ## rode the same slice's bump.)
    ##
    ## (Prior: Cluster H Step B (ADR-0022) bumps the walker version 54→55:
    ## `refPointeeTypeId` (`runtime_heap.nim`) now prefers the pointee's
    ## `nominalId` (Cluster H Step A) over the structural `$pointeeTy`
    ## rendering for a named-object pointee, changing the `Ref_<...>` Z3 sort
    ## names minted for inline `ref`/`ptr` heap pointees. Sort names are
    ## internal — never surfaced in a witness/verdict — so this is a pure
    ## cache-key rotation: verdicts and witnesses are byte-identical for
    ## every existing SUT, only the DB slot changes. `renderAsChoicesVersion`
    ## stays "5" (no witness-shape change).
    ## (Prior: P2b (RFC-chapulin-hardening Cluster 4 — Parser expression coverage,
    ## ADR-0021) bumps the walker version 53→54: `ref object` construction as
    ## an EXPRESSION (`let p = Node(val: x, next: nil)`, `Node = ref object`).
    ## `classifyType` UNWRAPS a NAMED `ref object` alias to the SAME `itTuple`
    ## shape a plain value object produces, so P2a's `nnkObjConstr` arm
    ## ALREADY, silently, took this path for ref-object constructors too —
    ## every ref/ptr-typed field simply degraded (`sxUnknown`) because a bare
    ## `nnkNilLit` field value had no general `parseExpr` arm and an omitted
    ## ref-typed field had no `zeroValueForType` encoding. The RFC's original
    ## sketch (synthesise an `isNew` + `mkFieldDerefWrite` heap-allocation
    ## preamble) was EMPIRICALLY REJECTED: `let p = new(Node)` for a NAMED
    ## ref-object alias crashes TODAY at walk time (`field 'refPointeeTy' is
    ## not accessible for type 'IRType' using 'kind = itTuple'`) because Phase
    ## 16 D1a VALUE-MODELS every BARE symbol of a named ref-object-alias type
    ## regardless of how it was bound — a heap-based `svRef` would be
    ## invisible to every later bare `p.field` read (see ADR-0021). P2b
    ## instead hardens the EXISTING value-tuple construction arm: a `nil`
    ## field value or an omitted ref-typed field now lowers via `mkNil`
    ## (Nim's REAL ref/ptr zero — sound, not a degrade); a present ref-typed
    ## field whose value does not resolve to a genuine ref/ptr address
    ## (recursive construction from an existing bare-symbol node — no address
    ## to store, D1a) degrades THAT FIELD ONLY and fills with a
    ## type-compatible `mkNil` (never a shape-mismatched value); a VARIANT
    ## object constructor (`itVariant`/`itMultiVariant`) is GUARDED and
    ## degraded via a reference to a fresh, deliberately-UNBOUND synthetic var
    ## (a later `env[name]` lookup raises a safely-caught `KeyError`, never
    ## `isVariantField`'s uncatchable `doAssert false` Defect) — this
    ## retroactively hardens a P2a gap that hard-crashed macro expansion on
    ## ANY variant-object constructor (ref or value) reaching this arm. A pure
    ## VERDICT change (`sxUnknown` → real `sxSat`/`sxUnsat`) for SUTs
    ## constructing a ref object as an expression, hence the walker bump.
    ## `renderAsChoicesVersion` stays "5" for the SAME reason P1/P2a didn't
    ## bump: the witness surface is built only from top-level SUT PARAMETERS
    ## — a constructed ref object is an internal `let`/return value that never
    ## reaches `renderAsChoices` in a new shape.
    ## (Prior: P2a (RFC-chapulin-hardening Cluster 4 — Parser expression coverage)
    ## bumped the walker version 52→53: `parseExpr` (`dsl_parser.nim`) gains
    ## an `nnkObjConstr` arm — a value-object (non-ref) constructor
    ## `Point(x: a, y: b)` used as an EXPRESSION (e.g. `let p = Point(x: a,
    ## y: b)`, an object `return`) was previously recognised ONLY inside
    ## `nnkRaiseStmt`'s `newException(T, msg)` shape; any OTHER value-object
    ## construction fell through to CR-2a's catch-all, tainting the whole
    ## run to a classified `sxUnknown` (SND-1). Since a value object's
    ## `IRType` is `itTuple`-shaped (same as P1's tuple, just with
    ## `objectName` populated), P2a REUSES P1's `iekTupleLit`/`mkTupleLit`/
    ## `lowerTupleLit` wholesale rather than minting a new IR kind — every
    ## existing `iekTupleLit` dispatch site transfers for free. Object-
    ## constructor fields may be reordered or omitted (unlike a tuple); the
    ## new arm walks the TYPE's declared field order and synthesises Nim's
    ## genuine zero-init value for an omitted field (sound, via CR-2a's
    ## `zeroValueForType`) or degrades that one field via the same
    ## `feUnsupportedExprKind`/SND-1 taint idiom if its type has no clean
    ## zero-value encoding. A pure VERDICT change (`sxUnknown` → real
    ## `sxSat`/`sxUnsat`) for SUTs constructing a value object as an
    ## expression, hence the walker bump. `renderAsChoicesVersion` stays "5"
    ## for the SAME reason P1's didn't bump: the witness surface is built
    ## only from top-level SUT PARAMETERS (whose object/tuple reflection
    ## branch already existed) — a constructed value object is an internal
    ## `let`/return value that never reaches `renderAsChoices` in a new
    ## shape.
    ## (Prior: P1 (RFC-chapulin-hardening Cluster 4 — Parser expression coverage)
    ## bumped the walker version 51→52: `parseExpr` (`dsl_parser.nim`) gains a
    ## general N-ary `nnkTupleConstr` arm — a tuple constructor `(a, b, c)` /
    ## named `(x: a, y: b)` used as an EXPRESSION (e.g. `let t = (a, b)`, a
    ## tuple `return`) previously fell through to CR-2a's catch-all (only the
    ## narrow `yield (e1,e2)` A3-S2a special-case handled `nnkTupleConstr`
    ## before), degrading the whole run to a classified `sxUnknown` (SND-1
    ## taint). The new arm builds an `iekTupleLit` IR node lowering to
    ## `svTuple`, reusing the ALREADY-EXISTING itTuple/svTuple witness/runtime
    ## machinery (built for variant/object values) — a pure VERDICT change
    ## (`sxUnknown` → real `sxSat`/`sxUnsat`) for SUTs constructing a tuple as
    ## an expression, hence the walker bump. `renderAsChoicesVersion` does
    ## NOT bump: `renderAsChoices*[T]` (`symex.nim`) is built ONLY from the
    ## SUT's top-level parameter list (`emitTyAndReader`/`witnessTup`), never
    ## from an internal `let`-bound or returned value, and its `elif T is
    ## tuple:` branch (generic `fields(w)` reflection) already existed
    ## untouched before this slice — no new witness shape is ever serialised
    ## by P1.
    ## (Prior: M5 (RFC-chapulin-hardening Cluster 3 — Model/stdlib gaps) bumps the
    ## walker version 50→51: `parseExpr` (`dsl_parser.nim`) gains an
    ## `nnkIfExpr` arm — an if-EXPRESSION used as a SUB-EXPRESSION (nested as
    ## an operand, or as the direct RHS of a `let`) previously fell through to
    ## CR-2a's catch-all and degraded to a classified `sxUnknown`. It is now
    ## modeled via synthetic let+read A-normalisation: a fresh temp is bound
    ## to the chosen arm's value (`mkLet` inside each arm, safe per-path since
    ## the walker's `isIf` forks BEFORE running arm bodies), the if is emitted
    ## as a statement into the preamble, and a read of the temp replaces the
    ## if-expression. This ALSO makes `min`/`max` on `int` resolve to a real
    ## verdict with no separate modeling: `system.min`/`max`'s `int` overloads
    ## carry a `{.magic.}` pragma but ALSO a real `if x <= y: x else: y`-
    ## shaped body, and `parseCalleeImpl`'s existing single-`result = expr`
    ## rewrite calls `parseExpr` directly on that `nnkIfExpr` — ordinary
    ## proc-inlining routes it through the new arm. A pure verdict change
    ## (`sxUnknown` → real `sxSat`/`sxUnsat`) for SUTs containing an if-expr
    ## sub-expression or int `min`/`max` — cache key must rotate.
    ## `renderAsChoicesVersion` stays "5" (no new witness shape: the
    ## if-expression's unified arm type is always a plain int/bool/float/
    ## string scalar already rendered today).
    ## (Prior: M4 (RFC-chapulin-hardening Cluster 3 — Model/stdlib gaps) bumped the
    ## walker version 49→50: `s &= x` (augmented-assign) and `s.add(x)`
    ## (string-receiver, string arg) are now modeled as the in-place
    ## concat-assign `s := s & x`, reusing the EXISTING `iekStrConcat` IR (the
    ## same ctor the binary `s & x` expression arm already built) — a
    ## type-classify branch (string LHS/receiver → `mkStrOp`), NOT an addition
    ## to `binopForInfix` (still has no `"&"` case, by design). `&=` on a
    ## string LHS was SND-1's Class-B silent-no-op case (bare
    ## `mkUnsupported`, no `binopForInfix` `"&"` case) — it degraded to
    ## `sxUnknown` post-SND-1 (was a false `sxSat` pre-SND-1); `.add` on a
    ## string receiver degraded to `sxUnknown` cleanly (S11). Both now resolve
    ## to a real `sxSat`/`sxUnsat` — a verdict-surface change, so the cache
    ## key must rotate. `renderAsChoicesVersion` stays "5" (still a plain
    ## string witness). A char-arg `.add('c')` and a non-string `&=` still
    ## degrade cleanly (unchanged, out of scope — no char→1-char-string IR).
    ## (Prior: M3 (RFC-chapulin-hardening Cluster 3 — Model/stdlib gaps) bumped the
    ## walker version 48→49: `s.rfind(sub)` (std/strutils) is now modeled via
    ## nim-z3's native `lastIndexOf` (`Z3_mk_seq_last_index`) — a near-clone of
    ## the `iekStrFind`/`indexOf` arm (S4), returning the LAST occurrence's
    ## byte offset (or -1 when absent), same convention as `find`. New IR kind
    ## `iekStrRfind` / stdlib-model kind `smkStrRfind`. Previously `rfind` had
    ## no dedicated match in `dsl_parser.nim` and fell through to the generic
    ## string-receiver `iekStrUnsupported` catch-all → classified `sxUnknown`.
    ## Now it resolves to a real `sxSat`/`sxUnsat` verdict — a verdict-surface
    ## change, so the cache key must rotate. A native Z3 Sequence-theory
    ## primitive, not a bounded-scan encoding — no hang risk. `renderAsChoices-
    ## Version` stays "5" (same int witness shape `find` already produces).
    ## (Prior: M2 (RFC-chapulin-hardening Cluster 3 — Model/stdlib gaps) bumped the
    ## walker version 47→48: `parseBiggestInt(s)` (std/strutils) is now routed
    ## to the SAME `iekStrToInt` IR as `parseInt(s)` (identical on this 64-bit
    ## platform, where `BiggestInt` is `int64`). Previously `parseBiggestInt`
    ## had no dedicated match in `dsl_parser.nim` and fell through to the
    ## generic string-receiver `iekStrUnsupported` catch-all → classified
    ## `sxUnknown`. Now it resolves to a real `sxSat`/`sxUnsat`/`sxRaised`
    ## verdict — a verdict-surface change, so the cache key must rotate.
    ## `renderAsChoicesVersion` stays "5" (same int/string witness shape).
    ## (Prior: M1 (RFC-chapulin-hardening Cluster 3 — Model/stdlib gaps) bumped the
    ## walker version 46→47: `emitTyAndReader`'s `itSeq` arm (`symex.nim`)
    ## gains reader cases for fixed-width-int seq elements (`byte`/
    ## `uint8..uint64`/`int8..int32` — `int64` was already handled), and
    ## `isRenderableSeqElemTy` (`smt/types.nim`) is widened in lockstep from
    ## int64-only to any `itInt` width in `{8,16,32,64}`. A `seq[byte]`/
    ## `seq[uintN]`/`seq[intN]` SUT parameter (top-level or nested) that
    ## previously demoted the whole run to `sxUnknown` (CR-2c) now resolves
    ## to a real `sxSat`/`sxUnsat` — a verdict-surface change, so the cache
    ## key must rotate.
    ## (Prior: CR-2c (RFC-chapulin-hardening Cluster 2 — Crash-totality) bumped the
    ## walker version 45→46: `emitTyAndReader` (`symex.nim`) — the POST-
    ## SOLVE witness-reader codegen macro, a THIRD structurally-distinct
    ## macro-`error()` surface separate from CR-2a (SUT-body parse) and
    ## CR-2b (param-type classify) — no longer `error()`s at macro-
    ## expansion on a `seq[...]`/`Table[...]`/`HashSet[...]` witness shape
    ## outside its fixed renderable fragment. `classifyType`'s `seq`/
    ## `Table`/`HashSet` arms (`dsl_typebridge.nim`) now apply the SAME
    ## renderability predicate `emitTyAndReader` itself consults
    ## (`isRenderableSeqElemTy`/`isRenderableTableTy`/`isRenderableSetElemTy`,
    ## `smt/types.nim` — one shared helper per container kind) and route an
    ## unrenderable shape to an `itUninterp("__unsupported_witness:" & s)`
    ## placeholder instead of a real `itSeq`/`itTable`/`itSet` — mirroring
    ## CR-2b's `__unsupported:` idiom under a distinct marker.
    ## `allocateSym` raises the generic `SymexClassifiedDegradeError`
    ## carrier (CR-1c) with the new `feUnsupportedWitnessType` kind
    ## (distinct from CR-2b's `feUnsupportedParamType` — a different macro,
    ## different call site) at parameter-allocation time — before the body
    ## is walked and before witness codegen is ever reached — forcing a
    ## WHOLE-RUN classified `sxUnknown`. No new exception type; this
    ## maximally reuses CR-2b's live degrade pipeline. SUTs that previously
    ## failed to COMPILE (e.g. `seq[SomeObject]`, `Table[string, string]`,
    ## `HashSet[string]` witness shapes) now compile and resolve to a
    ## classified `sxUnknown`, so the cache key must rotate. (The RFC's
    ## CR-2c entry notes "otherwise none" for the version bump — superseded
    ## by the CR-2a/CR-2b precedent: converting a macro-`error()` compile-
    ## abort into a classified `sxUnknown` is always a verdict-surface
    ## change, and bumping is always cache-safe.)
    ## (Prior: CR-2b 44→45: `classifyType`'s resolved-type-name text-match
    ## catch-all (`dsl_typebridge.nim`) no longer `error()`s at
    ## macro-expansion on an unsupported PARAMETER type (which aborted
    ## compilation before any proc body was even walkable — a different
    ## mechanism from CR-2a's expression-position catch-all, since
    ## `classifyType` takes no `ctx`/`preamble` to taint and there is no
    ## sound dummy `IRType`). It now classifies to an
    ## `itUninterp("__unsupported:" & s)` placeholder; `allocateSym` raises
    ## the generic `SymexClassifiedDegradeError` carrier (CR-1c) with the new
    ## `feUnsupportedParamType` kind at parameter-allocation time — before
    ## the body is walked — forcing a WHOLE-RUN classified `sxUnknown`. SUTs
    ## that previously failed to COMPILE now compile and resolve to a
    ## classified `sxUnknown`, so the cache key must rotate.
    ## CR-2a 43→44: `parseExpr`'s expression-position catch-all no
    ## longer `error()`s at macro-expansion on an unsupported NimNode `kind`
    ## (which aborted compilation outright — strictly worse than `sxUnknown`,
    ## the SUT couldn't be analysed at all). It now registers a classified
    ## `sevError` (`feUnsupportedExprKind`), emits `mkUnsupported` into the
    ## preamble, and returns a type-correct dummy (`classifyType(n).ty`),
    ## reusing the A7-S3 `runeLen(symbolic)` degrade idiom.
    ## CR-1c 42→43: a final `except CatchableError` catch-all on the
    ## existing `runSymex` try now converts a genuinely UNANTICIPATED native
    ## exception (one escaping the walker unmatched by any specific arm) into
    ## a classified `sxUnknown` carrying the distinct `weInternalWalkerFault`
    ## kind, instead of crashing the process. CR-1b 41→42: a value-returning
    ## callee whose body binds a local `let` and implicitly returns an
    ## expression over it now parses the leading `let` into the `preamble`
    ## A-normalisation channel instead of silently dropping it, fixing a
    ## native `KeyError` crash at `iekVar` lowering. CR-1a 40→41: bitwise
    ## `and`/`or`/`xor` on a Z3-Int-sorted operand (`.len`/`.find`/`.indexOf`/
    ## `parseInt`) is now bridged to BV via `int2bv` and correctly modeled,
    ## instead of native-crashing. SND-2 39→40: `isAssume` is now a DISTINCT
    ## IR kind instead of lowering to `mkAssert`. `canonicalize` renders it
    ## with a new, distinct cache-key tag (`St<Am:...>`, vs `isAssert`'s
    ## `St<At:...>`) — any SUT containing `symexAssume` now hashes
    ## differently, so the cache key rotated. Prior still: SND-1b 38→39,
    ## SND-1 37→38, A7-S3 36→37, A7-S2 35→36, A7-S1 34→35, A9 33→34,
    ## A8 32→33.)
    ##
    ## RFC-chapulin-hardening SND-3 (ADR-0023) 57→58: a lowering-time
    ## `raise` reachable inside a loop guard (char/string-ordering compare,
    ## non-int64-set membership) is silently lost on the C backend's
    ## goto-exception model, producing a false `sxUnsat` (c==sxUnsat vs
    ## cpp==sxUnknown). Fixed by degrading in-band (fresh unconstrained bool
    ## + SND-1 per-path `uncertain` taint) instead of raising — both
    ## backends now agree (`sxUnknown`). See `symexWalkerVersion`'s own doc
    ## comment (`canonicalize.nim`) for the full writeup.
    ##
    ## (Prior: Cluster H H_containers (ADR-0022) 56→57: containers OF a named
    ## ref-object now construct/index to REAL verdicts (`seq[Node]` literal
    ## construction, `array[N, Node]` indexing) instead of raising a native
    ## exception classified to `sxUnknown`. `tuple[a: Node]` needed no code
    ## change. `Table[K, Node]`/`HashSet[Node]` stay degraded (confirmed out
    ## of scope). See `symexWalkerVersion`'s own doc comment
    ## (`canonicalize.nim`) for the full writeup.
    ##
    ## Cluster H Step C (ADR-0022, the atomic H1) 55→56: a bare named
    ## `ref object`/`ptr object` alias now classifies `itRef`/`itPtr` (true
    ## heap identity) instead of value-modelling — a broad verdict-surface
    ## change (aliasing/identity now yield real verdicts; ref-object
    ## construction now emits real heap ops; the `isNew` zero-write closes a
    ## false-SAT hole). See `symexWalkerVersion`'s own doc comment
    ## (`canonicalize.nim`) for the full writeup.)
    ## RFC-chapulin-hardening R1 (CRITICAL soundness fix) 60→61: five
    ## statement arms (`isWhile`, `isIndex` seq/array, `isVariantReassignSymbolic`,
    ## `isReturn`) lowered an expression without draining the scalar-raise-fork
    ## sinks (`strIndexOobConds`/`parseIntRaiseConds`/`divByZeroConds`/
    ## `overflowConds`) afterward, silently dropping any raise predicate that
    ## expression deposited — a target reachable only past a real defect was
    ## falsely `sxSat`. Fixed by draining + threading survivors at each site,
    ## mirroring `isLet`/`isAssign`/`isIf`. See `symexWalkerVersion`'s own doc
    ## comment (`canonicalize.nim`) for the full writeup.
    ## RFC-chapulin-hardening R2 (CRITICAL soundness fix) + R6 (MEDIUM
    ## hardening) 61→62: the Q1 scan-idiom recognizer's `boundNode` had no
    ## loop-invariance check (only a type check), so a counter-dependent
    ## bound (`while i < (n - i) and s[i] != 'z': inc i`) was mis-lifted
    ## against the loop-ENTRY value of `bound` — a false verdict/witness. Now
    ## rejected via `refersToSym`. Every "same variable as `i`" check
    ## (guard index, body increment, and the new bound check) now compares
    ## true symbol identity (`sameSym`) instead of `.strVal`. See
    ## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ## RFC-chapulin-hardening R14 (CRITICAL soundness fix) 62→63: the old
    ## `mkGuardedWhile` do-while rotation re-ran a short-circuit while-guard's
    ## hoisted preamble as a TRAILING body statement, which `continue` skipped
    ## (`walkBlock` stops on a zero-path statement) — the guard temp went
    ## stale, producing a false verdict. Replaced by `mkShortCircuitWhile`,
    ## which desugars `while (A and B): body` to `while A: <B's preamble>; if
    ## not B: break; body` at the loop level — continue-safe by construction.
    ## See `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ##
    ## NOTE: this pin was last updated at v63; versions 64→70 (chapulin
    ## round-6 hardening: SND-3, Cluster H H_containers/H_witness, Q1 scan-
    ## lift, round-6 sello fixes, the B0 scan-lift-bound hotfix — see
    ## `symexWalkerVersion`'s own doc comment in `canonicalize.nim` for that
    ## history) bumped without this file's `==` pin following along, because
    ## this test file was not wired into `nelli.nimble`'s `test` task at the
    ## time and so was never run as part of routine CI/regression sweeps.
    ## N0 (2026-08-13) was the first slice to update this pin since that gap
    ## was noticed, bringing it current to 70→71; A2a (2026-08-13) carried
    ## the same discipline forward, 71→72; A2b (2026-08-13) carries it
    ## forward again, 72→73; round-6 A0 carries it forward again, 73→74.
    ## RFC-parser-normalization round-1 review finding
    ## C1 closed the registration gap itself: this file is now wired into the
    ## `test` task, so future walker-version bumps that skip this pin will be
    ## caught by routine CI/regression sweeps going forward.)
    check symexWalkerVersion == "74"

  test "CR-2 sub-test 6: renderAsChoicesVersion is now 7":
    ## CR-4 changes how int32(f) materialises as svBV32 internally; however,
    ## renderAsChoices operates on the extracted Nim witness value (int32 →
    ## SomeSignedInt → integerChoice path), which is identical before and after.
    ## The renderAsChoices FORMAT is genuinely unaffected by CR-4.
    ## However, the consolidated version bump document (Part 2 of CR-2 task)
    ## instructs a bump to "4" as part of the CR-1/CR-3/CR-4/CR-5/CR-6
    ## consolidated model-change cache rotation.
    ## M1 (RFC-chapulin-hardening Cluster 3) bumps again, "4" → "5": a
    ## `seq[byte]`/`seq[uintN]`/`seq[intN]` witness is a genuinely NEW
    ## serialised witness shape (previously unreachable — these element
    ## types demoted the whole param to `sxUnknown` before any witness was
    ## ever rendered), so the render-format version rotates in lockstep with
    ## the walker bump (46→47) per the CR-2/CR-2c precedent.
    ## Cluster H Step C bumps again, "5" → "6": a bare named-ref-object PARAM
    ## is now `svRef` (was `svTuple`), making it eligible for
    ## `buildHeapSnapshot`/alias-group witness rendering — a genuinely new
    ## witness SHAPE for a parameter class that never produced a
    ## `heapSnapshot` entry before.
    ## Cluster H H_containers does NOT bump ("6" stays): `seq[Node]` literal
    ## construction / `array[N, Node]` indexing move to real verdicts, but
    ## the per-element `seq[Node]` witness stays the PRE-EXISTING R3
    ## length-only stub (unchanged), and `array`/`tuple` of a ref were
    ## already witness-renderable structurally — no new rendered shape.
    ## Cluster H H_witness bumps again, "6" → "7": `buildHeapSnapshot`/
    ## `pointeeRendering` now descend recursively into ref-typed object
    ## fields and container elements (bounded by the heap-depth budget,
    ## cycle-safe), replacing the flat `"<object>"` placeholder with a real
    ## structural rendering and populating `pointsTo`/`aliasRef` for the
    ## whole reachable graph — a genuinely new witness SHAPE. This is a
    ## post-solve rendering change only (no verdict changes), so
    ## `symexWalkerVersion` stays 57 (see sub-test 5 above).
    check renderAsChoicesVersion == "7"
