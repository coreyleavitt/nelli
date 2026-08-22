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

  test "CR-2 sub-test 5: symexWalkerVersion is now 82":
    ## Round-6 B4 (2026-08-15) bumps the walker version 81→82:
    ## `tryRecognizeAccumulatingScan`/`tryMatchAccumulatingScanIdiomShape`
    ## (`dsl_parser.nim`), the accumulating-string sibling of Q1/B0's and
    ## B3's scan-lift recognizers, for the `readCString` family idiom
    ## (`while i < s.len: (if s[i] == lit: return <expr>); acc.add(char(s[i]));
    ## inc i`), plus `readSeqUInt8`'s string-backed-param witness-reader fix
    ## (`runtime.nim`). See `symexWalkerVersion`'s own doc comment
    ## (`canonicalize.nim`) for the full writeup.
    ##
    ## (Prior: Round-6 B3 (2026-08-15) bumped the walker version 80→81:
    ## `tryRecognizeScanPairIdiom`/`tryMatchScanPairIdiomShape`
    ## (`dsl_parser.nim`), the int-result sibling of Q1/B0's scan-lift
    ## recognizer, for the early-return-on-match scan idiom
    ## (`while i < s.len: (if s[i] == lit: return <expr>); inc i`). See
    ## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ##
    ## (Prior: Round-6 B2 rider (2026-08-15) bumped the walker version
    ## 79→80: the
    ## `byte` alias (`normalizeIntTyName`/`isIntFamilyName`, `dsl_parser.nim`)
    ## is now recognized by the width-conversion arm — the RFC's own primary
    ## consumer shape, `uint16(b) shl 8` with `b: byte`, previously fell
    ## through to the untouched pre-B2 identity pass-through. See
    ## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ##
    ## (Prior: Round-6 B2 (2026-08-15) bumped the walker version 78→79:
    ## int-family WIDTH-CONVERSION modeling (`iekConvIntWidth`, widening
    ## only — `uint16(b)` call syntax / `b.uint16` method syntax).)
    ##
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
    ## forward again, 72→73; round-6 A0 carries it forward again, 73→74;
    ## round-6 A1 carries it forward again, 74→75; round-6 A2 carries it
    ## forward again, 75→76; round-6 A3 carries it forward again, 76→77;
    ## round-6 B1 carries it forward again, 77→78; round-6 B2 carries it
    ## forward again, 78→79; the round-6 B2 rider carries it forward again,
    ## 79→80; round-6 B3 carries it forward again, 80→81; round-6 B4 carries
    ## it forward again, 81→82; round-6 B5 carries it forward again, 82→83
    ## (chained scan composition -- retires catalog finding #6); round-6 B6
    ## carries it forward again, 83→84 (option-region star-segment
    ## membership for the `readOptions` pair-loop); round-6 Bug #2 (scoped
    ## decline with read-taint) carries it forward again, 84→85; round-6
    ## A6-rider (implicit-result-fallthrough call-boundary soundness fix —
    ## a callee reaching an IMPLICIT `return` after a conditional, multi-
    ## statement `result = expr` assignment left its `retSym` totally
    ## unconstrained at the call site, a genuine false-`sxSat` generator, not
    ## merely a witness-extraction cosmetic issue; see `symexWalkerVersion`'s
    ## own doc comment for the full writeup) carries it forward again, 85→86.
    ## RFC-parser-normalization round-1 review finding
    ## C1 closed the registration gap itself: this file is now wired into the
    ## `test` task, so future walker-version bumps that skip this pin will be
    ## caught by routine CI/regression sweeps going forward.
    ## Round-6 B7-rider carries it forward again, 86→87: the scan-recognizer
    ## family's receiver gate widened to string-backed `seq[byte]` receivers
    ## (see `symexWalkerVersion`'s own doc comment for the full writeup) —
    ## a `seq[byte]` receiver through Q1/B0/B3/B4/B6's closed forms now moves
    ## from an unrecognized k-unroll to a real verdict.
    ## Round-6 B7r2 carries it forward again, 87→88: a literal-seeded
    ## scan/pair-loop counter (`collectIntOffsetLiteralLocals`) and a
    ## call-boundary `seq[(string,string)]`-returning helper (generalized
    ## Bug-#2 placeholder) both move from a classified crash/whole-run
    ## poison to a real capability — see `symexWalkerVersion`'s own doc
    ## comment for the full writeup.
    ## R1 (placeholder read-totality chokepoint) carries it forward again,
    ## 88→89: `iekSeqLen`'s and `iekSeqSlice`'s `svSeq` arms (plus
    ## `iekSeqAdd`'s mutation arm) had NO placeholder check, letting a
    ## `.len`/for-loop-bound read or a slice's OOB bound compute a false
    ## `sxUnsat`/`sxRaised` verdict off the placeholder's forced-`==0` decoy
    ## length, and letting `.add` unwind to a whole-run-poisoning crash — see
    ## `symexWalkerVersion`'s own doc comment for the full writeup.
    ## R2 (zero-default result binding, S3) carries it forward again, 89→90:
    ## v86 only bound `retSym` when a fallthrough path had ASSIGNED `result`
    ## somewhere along the way (`cp.env.hasKey("result")`); a path that never
    ## touched `result` at all (legal Nim — `result` holds the type's zero
    ## value) reached the caller with `retSym` still totally free, the exact
    ## false-`sxSat` shape v86 was built to kill, reintroduced for the
    ## never-assigned case — see `symexWalkerVersion`'s own doc comment for
    ## the full writeup.
    ## R3 (svInt overflow honesty, S2) carries it forward again, 90→91:
    ## `overflowCond` forked `OverflowDefect` for signed BV operands only —
    ## a `svInt`-represented promoted counter never forked, a false-`sxUnsat`
    ## hole for defect-reachability searches touching it — see
    ## `symexWalkerVersion`'s own doc comment for the full writeup.
    ## R4 (collector scoping + guard hardening, W1/N8/N2/W2/W3) carries it
    ## forward again, 91→92: `ctx.stringBackedParams`/
    ## `ctx.intOffsetLiteralLocals` were name-keyed and unscoped across
    ## proc boundaries, letting an unrelated same-named callee param or
    ## same-proc colliding local inherit a classification that was never
    ## its own — see `symexWalkerVersion`'s own doc comment for the full
    ## writeup.
    ## R5 (B6 pair-loop counter advance, S4) carries it forward again,
    ## 92→93: `tryRecognizePairLoopIdiom`'s member-branch closed form left
    ## the loop counter unadvanced (an empty block), and no single
    ## closed-form binding for its exit value is faithful across every
    ## witness satisfying region membership — the recognizer now declines
    ## the closed form outright whenever the counter is read after the
    ## loop, falling back to the pre-existing per-iteration-correct
    ## k-unroll — see `symexWalkerVersion`'s own doc comment for the full
    ## writeup. N9 (variant-constructor field-allocation budget) carries it
    ## forward again, 93→94 (see `symexWalkerVersion`'s own doc comment).
    ## N21 (pair-loop member-branch region-grammar correction, CRITICAL
    ## soundness) carries it forward again, 94→95: the B6 region grammar
    ## the member branch's empty block was certified against was bare
    ## segment-star with no parity tie to the real loop's two-segments-per-
    ## iteration consumption, wrongly certifying an odd-segment,
    ## non-empty-final-segment region a member even though the real SUT
    ## raises reading the incomplete final pair's value — a genuine
    ## false-SAT / false-decline pair. Strengthened to the loop's actual
    ## clean-termination language (`PAIR* ("\0" anybyte*)?`) — see
    ## `symexWalkerVersion`'s own doc comment for the full writeup.
    ## N16 (closure/lambda zero-default result binding, MEDIUM soundness)
    ## carries it forward again, 95->96: `applyClosureGround`'s fallThrough
    ## loop (`runtime.nim`) had no `else` twin binding a never-assigned
    ## `result` path's `funcApp` to `defaultZero(cb.retTy, ...)` -- the
    ## SAME shape R2 (89->90, below) fixed for the `isCall` arm, never
    ## applied to the shared closure-call implementation despite a prior
    ## commit's comment falsely claiming it already handled this shape. See
    ## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ## N27 (HOF-over-placeholder-seq guard, HIGH soundness) carries it
    ## forward again, 96->97: `lowerHofCall` now declines through the R1
    ## chokepoint before any placeholder-sensitive read -- see
    ## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ## N28 (collector root/receiver acceptance by symbol identity, MEDIUM
    ## soundness) carries it forward again, 97->98: `markSymOrRootParam`
    ## now tests true symbol identity (`containsSym`/`sameSym`) instead of
    ## printed-name equality -- see `symexWalkerVersion`'s own doc comment
    ## (`canonicalize.nim`) for the full writeup.
    ## D2 (round-6 review remediation, confirmed Medium resource-budget
    ## undercount) carries it forward again, 98->99: `isVariantConstructSym`'s
    ## `maxVariantConstructorFieldAllocs` check now costs each arm field via
    ## the new recursive `allocCostOf` helper (`smt/types.nim`) instead of a
    ## flat field COUNT -- a composite arm-field type (array/tuple/nested
    ## variant) now contributes its true leaf-allocation cost, so a shape
    ## that previously passed the flat count may now classify
    ## `beBudgetExhausted` -- see `symexWalkerVersion`'s own doc comment
    ## (`canonicalize.nim`) for the full writeup.
    ## N31 (two-hop literal-seeded scan counter inside a block:, HIGH
    ## soundness) carries it forward again, 99->100: `iekStrSubstr`'s CR-17
    ## slice-bound decline now degrades in-band instead of raising -- see
    ## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ## N36 (round-6 fix round 4, raw-raise-in-lower CLASS closure, HIGH
    ## soundness) carries it forward again, 100->101: every classified raise
    ## `lowerStrArm` can raise now converts in-band at a single chokepoint
    ## (not just `iekStrSubstr`'s one CR-17 site), plus `isVariantReassign`'s
    ## `defaultZero` call and `isIndex`'s two raw declines -- see
    ## `symexWalkerVersion`'s own doc comment (`canonicalize.nim`) for the
    ## full writeup.
    ## N37 (round-6 fix round 4, raw-raise-in-lower CLASS residue closure,
    ## HIGH soundness) carries it forward again, 101->102: `iekSeqSlice`'s
    ## two raw declines and `isRaise`'s bare-reraise decline now degrade
    ## in-band instead of raising (both empirically confirmed to produce a
    ## false `sxUnsat` under block nesting pre-fix); `lowerHofCall`'s inline
    ## map/filter plus a third, previously-unenumerated `lowerSeqLit` caller
    ## now guard `allocateSeqDataRaw` with `isBackedSeqElemTy` instead of
    ## calling it unguarded -- see `symexWalkerVersion`'s own doc comment
    ## (`canonicalize.nim`) for the full writeup.
    ## N39 (round-6 fix round 5, closing a mis-scoped safety certification in
    ## the raw-raise CLASS) carries it forward again, 102->103:
    ## `isVariantConstructSym`/`lowerVariantLit` now guard their per-arm-
    ## field `allocateSym` calls with a new `unallocatableFieldIssue`
    ## predicate instead of calling it unguarded -- `isVariantConstructSym`'s
    ## half is a confirmed false `sxUnsat`-under-block-nesting -> honest
    ## `sxUnknown` verdict flip; `lowerVariantLit`'s half is a
    ## certification-accuracy hardening fix (mechanism argument, no isolable
    ## flip observed) -- see `symexWalkerVersion`'s own doc comment
    ## (`canonicalize.nim`) for the full writeup.
    ## N40 (round-6 fix round 6, allocateSym totality) carries it forward
    ## again, 103->104: `allocateSym` no longer raises for classifiable
    ## input at any call site -- the raw-raise-in-lower CLASS's last five
    ## sites now degrade in-band via a new `allocDegrade` chokepoint; a
    ## `unallocatableFieldIssue` false negative (non-string-key Table) is
    ## also closed; the pre-walk param-entry boundary keeps its whole-run
    ## raise semantics by design -- see `symexWalkerVersion`'s own doc
    ## comment (`canonicalize.nim`) for the full writeup.
    check symexWalkerVersion == "104"

  test "CR-2 sub-test 6: renderAsChoicesVersion is now 10":
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
    ## Round-6 B4 bumps again, "7" → "8": `readSeqUInt8`'s string-backed-
    ## param fix (`runtime.nim`) — a `seq[byte]` param B1 marked
    ## `isStringBacked` models as `svString`, so its solved value landed in
    ## `RawWitness.strVals` while the generated reader glue (picked off the
    ## DECLARED `seq[byte]` type) called `readSeqUInt8`, which only read
    ## `seqLens`/`uintVals` — silently degrading every such param's witness
    ## to an empty seq regardless of the solved model. `readSeqUInt8` now
    ## reads `strVals` first when present. A genuinely NEW/CHANGED witness
    ## CONTENT for the affected param class reaching `renderAsChoices` via
    ## the same generated-reader path "5" (M1) established — bump in
    ## lockstep with the walker bump (81→82) per that precedent.
    ## Round-6 B4-rider bumps again, "8" → "9": `extractLeaf`'s `svString`
    ## arm switches from nim-z3's `evalStr` (`Z3_get_lstring`-backed, proved
    ## to mis-render any byte it treats as needing SMT-LIB escaping — an
    ## embedded NUL came back as the 5-char literal text `\u{0}` instead of
    ## 1 real byte) to `evalStrBytes`, built on the separate already-bound
    ## `getStringLength`/`getStringContents` API. A genuinely NEW/CHANGED
    ## witness CONTENT for every string witness containing such a byte —
    ## bump per the "8" precedent; verdicts are unchanged so
    ## `symexWalkerVersion` does not bump.
    ## Round-6 A6-rider bumps again, "9" → "10": UNLIKE the "8"/"9" riders,
    ## this bump is lockstep with a `symexWalkerVersion` bump (85→86) — the
    ## fix (`runtime.nim`'s `isCall` arm now binds a call's implicit-result
    ## fallthrough to `retSym` via `retBindEq`, mirroring the closure-call
    ## path's existing idiom) corrects a genuine SOUNDNESS gap, not just
    ## rendering: a previously-unconstrained `retSym` let some targets prove
    ## a false `sxSat` with a witness disconnected from the solver's actual
    ## (nonexistent) justification. Bumped here per the established lockstep
    ## precedent so a stale "9"-keyed cache entry is never replayed as if it
    ## still reflects the corrected extraction path.
    ## Round-6 B7-rider bumps again, "10" → "11": LEG 2's char-widening fix
    ## (`normalizeIntTyName` now maps `char` to `"uint8"`, same as `byte` —
    ## see `symexWalkerVersion`'s own doc comment for the full root-cause
    ## writeup) is lockstep with the walker bump (86→87) for the same
    ## reason "10" was: not extraction-only, a genuine under-constrained-
    ## property parse-time gap, so a stale "10"-keyed witness must not be
    ## replayed as if it still reflects the corrected (properly-widened)
    ## constraint.
    ## Round-6 N37 does NOT bump the render version ("11" stays): the fix
    ## changes WHICH classified error a query reports and whether a query
    ## reaches `sxUnknown` vs a false `sxUnsat` -- a verdict-surface change,
    ## not a witness-CONTENT/serialization-shape change (no new rendered
    ## field, no previously-mis-rendered byte). `symexWalkerVersion` alone
    ## carries the cache-invalidation signal here, per the "6"/"CR2c" no-op
    ## precedent above.
    check renderAsChoicesVersion == "11"
