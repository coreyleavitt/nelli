## Canonical structural encoding for the symex IR.
##
## The output of every `canonicalize` proc here is a deterministic
## string that depends only on the witness-relevant structure of
## its input. Source locations, local-variable name spellings, and
## map-iteration order are all encoded out — the canonical string
## of two structurally-equivalent inputs is byte-identical.
##
## Used by Phase 10's content-addressed DB cache key
## (`symexCacheKey`). See `docs/symex/determinism.md`.
##
## Reserved sigils:
##   `<` `>`  — open/close one constructor's payload
##   `;`      — field separator within a constructor
##   `:`      — kind/payload separator
## No constructor's payload may contain an unescaped sigil; primitives
## are wrapped to enforce that.

import std/[strutils, tables, algorithm, sha1]
import ./types

const
  cacheKeySat*     = ":sat"
    ## Phase 13 cycle 2; renamed Phase 15 Z3e. Suffix appended to a
    ## content-addressed key for SAT witness entries. Sibling suffixes
    ## (`:sat`/`:unsat`/`:unknown` + per-type `:raised:<typeId>` via
    ## `cacheKeyRaised`) coexist under one `"sx:" & H` hash so verdicts
    ## have distinct DB slots.
  cacheKeyUnsat*   = ":unsat"
    ## UNSAT verdict sentinel slot. Value is `@[]` (empty seq).
  cacheKeyUnknown* = ":unknown"
    ## UNKNOWN verdict sentinel slot. Value is `@[]` (empty seq).
    ## Phase 15 Z3e: renamed from `cacheKeyUnkSuffix` / `:unk` to standardize
    ## suffixes on full English words (supersedes the Z0 deferral note).
    ## Entries written under the old `:unk` suffix are orphaned — harmless:
    ## a cache miss recomputes, and there are no external consumers.
  verdictCacheMaxEntries* = 1
    ## Mandatory `maxEntries` for `saveSymexVerdictImpl` calls.
    ## The default `maxEntries = 16` allows accumulation; with the
    ## positional sentinel invariant `result[0] == @[]`, a stray
    ## non-sentinel write under the same key would push the sentinel
    ## to position 1 and silently break load detection. Pinning
    ## to 1 makes the structural invariant impossible to violate.

proc cacheKeyRaised*(typeId: string): string =
  ## Phase 15 Z3e. Per-type cache-key suffix for an `sxRaised` finding, e.g.
  ## `cacheKeyRaised("ValueError") == ":raised:ValueError"`. Each raised
  ## exception type gets its own DB slot so multi-raise SUTs (cluster E) can
  ## accumulate one entry per `(exnType, pathCond)` finding.
  ":raised:" & typeId

const renderAsChoicesVersion* = "5"
  ## Phase 12 cycle 3 introduced the constant; cycle 6 bumped it
  ## "1" → "2" to invalidate stale collection witnesses cached
  ## under the old length-prefix `renderAsChoices` encoding for
  ## seq/Table/HashSet. The current "2" encoding emits per-element
  ## `booleanChoice(true, 0.9)` continue-bools terminated by one
  ## `booleanChoice(false, 0.9)`, matching `lists`/`tables`/`sets`
  ## strategies' replay shape. Non-collection witnesses' choice
  ## sequences are unaffected by the bump but invalidate via the
  ## same key — acceptable cost for one-off cache rotation.
  ##
  ## Distinct from `symexWalkerVersion` (walker semantics — how the
  ## walker reasons about the SUT). `renderAsChoicesVersion` covers
  ## *how a sat witness is serialised into the choice-IR*, not what
  ## the walker computes.
  ##
  ## - "1" — Phase 7 / 11 baseline: length-prefix encoding for
  ##   seq/Table/HashSet (broken round-trip through `lists`/`tables`/
  ##   `sets` strategies).
  ## - "2" — Phase 12 cycle 6: continue-boolean encoding matching
  ##   the strategy draw protocol; sorted iteration for Table/HashSet
  ##   to ensure deterministic encoding of the same logical witness.
  ## - "3" — Phase 15 Cluster R close-out (cycle R12): the heap-snapshot
  ##   witness FORMAT extension. An `sxSat`/`sxRaised` result for a SUT with
  ##   ref/ptr-typed params now carries a `heapSnapshot` (one
  ##   `HeapSnapshotEntry` per ref/ptr param: abstract address `value`,
  ##   modelled `pointsTo` pointee value, and alias-group `aliasRef` — the
  ##   lexicographically-first param of an address group is the primary that
  ##   holds `pointsTo`; nil refs render `value == "nil"`). A non-heap SUT's
  ##   witness is UNCHANGED (the `heapSnapshot` key is absent), but the bump
  ##   rotates the key so any "2"-era ref/ptr witness re-serialises under the
  ##   new format. See docs/symex/witness-format-v3.md.
  ## - "4" — Phase 15 CR-2 consolidated model-change cache rotation (cycle
  ##   CR-2). CR-1 (closure heap write-back), CR-3 (float→int domain bounds),
  ##   CR-4 (int32→svBV32 internal witness shape), CR-5 (closure liveRefs
  ##   seeding), and CR-6 (mixed-float compare) changed symex model semantics
  ##   and witness shapes. Note: CR-4 changes svBV32 INTERNALLY; the
  ##   `renderAsChoices` path (which operates on the extracted Nim int32 value
  ##   via `SomeSignedInt → integerChoice`) is UNCHANGED. Nevertheless, because
  ##   CR-3/CR-6 alter which float witnesses are accepted and CR-1/CR-5 alter
  ##   heap/closure witnesses, the rendering version bumps here in lockstep with
  ##   the walker bump (10→11) so the cache rotation covers all affected
  ##   serialised witness shapes in a single cycle.
  ## - "5" — RFC-chapulin-hardening M1: `seq[byte]`/fixed-width-int witness
  ##   readers. A `seq[T]` where `T` is `byte`/`uint8..uint64`/`int8..int32`
  ##   now renders as a real Nim `seq[T]` witness (previously these element
  ##   types demoted the WHOLE param to `sxUnknown` via CR-2c's
  ##   `isRenderableSeqElemTy` gate, so no witness of this shape was ever
  ##   serialised before). New shape → bump in lockstep with the walker bump
  ##   (46→47) per the CR-2/CR-2c precedent (a new witness shape is always a
  ##   cache-safe rotation).

const symexWalkerVersion* = "51"
  ## M5 (RFC-chapulin-hardening, Cluster 3 — Model/stdlib gaps): 50→51.
  ## `parseExpr` (`dsl_parser.nim`) gains an `nnkIfExpr` arm: an if-EXPRESSION
  ## used as a SUB-EXPRESSION (nested as an operand, e.g. `(if c: 1 else: 2) +
  ## 1`, or as the direct RHS of a `let`) previously fell through to CR-2a's
  ## catch-all and degraded to a classified `sxUnknown`. It is now modeled via
  ## synthetic let+read A-normalisation: a fresh temp is bound to the chosen
  ## arm's value (`mkLet` inside each arm — safe because the walker's `isIf`
  ## forks `paths` per-arm before running the arm body, so sibling arms can
  ## never collide over the same name), the if is emitted as a statement into
  ## the caller's preamble, and a read of the temp replaces the if-expression.
  ## This is a pure VERDICT change (`sxUnknown` → real `sxSat`/`sxUnsat`) for
  ## SUTs containing an if-expression sub-expression — hence the walker bump.
  ## `renderAsChoicesVersion` does NOT bump: the witness is whatever plain
  ## scalar type the if-expression's arms already unify to (int/bool/float/
  ## string), no new shape.
  ##
  ## No separate modeling was needed for `min`/`max` on `int`: `system.min`/
  ## `system.max`'s `int` overloads (`system/comparisons.nim`) carry a
  ## `{.magic: "MinI"/"MaxI".}` pragma but ALSO a real, parseable body
  ## (`if x <= y: x else: y` / `if y <= x: x else: y`); `parseCalleeImpl`'s
  ## existing single-`result = expr` rewrite (`resultRhs`) detects the whole
  ## body as one expression and calls `parseExpr` directly on its `nnkIfExpr`
  ## — routing straight through this new arm via ordinary proc-inlining. (The
  ## FLOAT overloads are intercepted earlier by `mathInterception`, Phase 15
  ## F6/A5, and never reach this path.)
  ##
  ## M4 (RFC-chapulin-hardening, Cluster 3 — Model/stdlib gaps): 49→50.
  ## `s &= x` (augmented-assign) and `s.add(x)` (string-receiver, string arg)
  ## are now modeled as the in-place concat-assign `s := s & x`, reusing the
  ## existing `iekStrConcat` IR (no new IR kind). `&=` on a string LHS was
  ## SND-1's Class-B silent-no-op case (bare `mkUnsupported`, no `binopForInfix`
  ## `"&"` case) — it degraded to `sxUnknown` post-SND-1 (was a false `sxSat`
  ## pre-SND-1); `.add` on a string receiver degraded to `sxUnknown` cleanly
  ## (S11). Both are now real modeled mutations — a pure VERDICT change
  ## (sxUnknown → sxSat/sxUnsat) for SUTs using either form, so cached results
  ## must rotate out. `renderAsChoicesVersion` does NOT bump: the witness is
  ## still a plain string (same shape `&`'s expression form already produces).
  ## A char-arg `.add('c')` (no char→1-char-string IR available) and a
  ## non-string-operand `&=` still degrade cleanly (unchanged, out of scope).
  ##
  ## M3 (RFC-chapulin-hardening, Cluster 3 — Model/stdlib gaps): 48→49.
  ## `s.rfind(sub)` (std/strutils) is now modeled via nim-z3's native
  ## `lastIndexOf` (`Z3_mk_seq_last_index`, `sequence.nim:199`) — a near-clone
  ## of the `iekStrFind`/`indexOf` arm (S4), returning the byte offset of the
  ## LAST occurrence (or -1 when absent), same convention as `find`. New IR
  ## kind `iekStrRfind` / stdlib-model kind `smkStrRfind`; `rfind` previously
  ## fell through to the string-call catch-all (`iekStrUnsupported`,
  ## classified `seUnsupportedStringOp`) → `sxUnknown`. This is a pure VERDICT
  ## change for `rfind` SUTs — a real Z3 Sequence-theory primitive, not a
  ## bounded-scan encoding, so no hang risk. `renderAsChoicesVersion` does NOT
  ## bump: the witness is the same int shape `find` already produces.
  ## M2 (RFC-chapulin-hardening, Cluster 3 — Model/stdlib gaps): 47→48.
  ## `parseBiggestInt(s)` (std/strutils) is now routed to the SAME `iekStrToInt`
  ## IR as `parseInt(s)` (`dsl_parser.nim`'s expression-match site and its
  ## discard-raise-fork site both widen their name guard from `"parseInt"` to
  ## `{"parseInt", "parseBiggestInt"}`). On this (64-bit) platform `BiggestInt`
  ## is `int64` — identical to `parseInt`'s result type — so no new runtime
  ## lowering or witness shape is introduced; this is a pure VERDICT change for
  ## `parseBiggestInt` SUTs: previously `sxUnknown` (classified
  ## `seUnsupportedStringOp`, falling into the generic string-receiver
  ## `iekStrUnsupported` catch-all since `parseBiggestInt` had no dedicated
  ## match), now a real `sxSat`/`sxUnsat`/`sxRaised` verdict — hence the walker-
  ## version bump. `renderAsChoicesVersion` does NOT bump: the witness is the
  ## same int/string shape `parseInt` already produces.
  ## M1 (RFC-chapulin-hardening, Cluster 3 — Model/stdlib gaps): 46→47.
  ## `emitTyAndReader`'s `itSeq` arm (`symex.nim`) gains reader cases for
  ## fixed-width-int seq elements — `byte`/`uint8..uint64`/`int8..int32`
  ## (`int64` was already handled) — calling new width/sign-correct
  ## `readSeq{Int,UInt}{8,16,32}`/`readSeqUInt64` helpers (`smt/runtime.nim`).
  ## `isRenderableSeqElemTy` (`smt/types.nim`) is widened in lockstep (its
  ## own doc comment: "mirrors exactly the shapes emitTyAndReader's itSeq
  ## arm can render") from `int64`-only to any `itInt` width in
  ## `{8,16,32,64}` (either signedness) — so a `seq[byte]`/`seq[uintN]`/
  ## `seq[intN]` top-level (or nested, via the recursive
  ## `isRenderableWitnessTy`) SUT parameter no longer gets demoted by CR-2c's
  ## `demoteUnrenderableWitnessTy` to a whole-run `sxUnknown` before the
  ## walker ever runs. The walker's allocation/extraction/indexing paths
  ## (`allocateSeqDataRaw`, `extractSeqElements`, `seqElemAt`) already
  ## dispatched on every one of these `(signed, width)` combinations — only
  ## the post-solve reader and its renderability gate were missing cases, so
  ## this is a genuine VERDICT change (`sxUnknown` → real `sxSat`/`sxUnsat`)
  ## for these SUT shapes, hence the walker-version bump; `renderAsChoices`
  ## also bumps (see its own "5" note) since this is a new witness shape.
  ##
  ## CR-2c (RFC-chapulin-hardening, Cluster 2 — Crash-totality):
  ## `emitTyAndReader` (`symex.nim`) — the POST-SOLVE witness-reader codegen
  ## macro, a THIRD structurally-distinct macro-`error()` surface separate
  ## from CR-2a (SUT-body parse) and CR-2b (param-type classify) — no
  ## longer `error()`s at macro-expansion on a `seq[...]`/`Table[...]`/
  ## `HashSet[...]` witness shape outside its fixed renderable fragment
  ## (`seq[int64|float64|float32|ref T]`, `Table[string, int64]`,
  ## `HashSet[int64]`). `parseProc*`'s TOP-LEVEL SUT parameter-classification
  ## loop (`dsl_parser.nim`, the single choke point every witness-rendering
  ## entry macro shares) now post-processes each parameter's `classifyType`
  ## result through `demoteUnrenderableWitnessTy`, applying the SAME
  ## renderability predicate `emitTyAndReader` itself consults
  ## (`isRenderableSeqElemTy`/`isRenderableTableTy`/`isRenderableSetElemTy`,
  ## `smt/types.nim` — one shared helper per container kind). Deliberately
  ## NOT inside `classifyType` itself: that classifier is also used for
  ## purely-internal (non-witness) types, e.g. an in-body helper call's
  ## `seq[byte]` return type — degrading those would corrupt internal type
  ## modeling for values that are never witness-rendered at all. An
  ## unrenderable TOP-LEVEL parameter shape routes to an
  ## `itUninterp("__unsupported_witness:" & s)` placeholder — mirroring
  ## CR-2b's `__unsupported:` idiom under a distinct marker. `allocateSym`
  ## raises the generic
  ## `SymexClassifiedDegradeError` carrier (CR-1c) with the new
  ## `feUnsupportedWitnessType` kind at parameter-allocation time — before
  ## the body is walked and before witness codegen is ever reached —
  ## forcing a WHOLE-RUN classified `sxUnknown` instead of a compile
  ## failure. No new exception type; this maximally reuses CR-2b's live
  ## degrade pipeline (Option A). The RFC's CR-2c entry notes "otherwise
  ## none" for the version bump; that is superseded here by the CR-2a/CR-2b
  ## precedent — converting a macro-`error()` compile-abort into a
  ## classified `sxUnknown` is always a verdict-surface change (SUTs that
  ## previously failed to COMPILE now compile and resolve to a classified
  ## `sxUnknown`), and bumping is always cache-safe (worst case rotates the
  ## cache; a compile abort has no cache entry to begin with, so this can
  ## never collide a stale entry with a newly-analysable SUT's verdict —
  ## but bumping anyway keeps the discipline uniform across all three
  ## macro-`error()` classes rather than special-casing this one).
  ##
  ## CR-2b (RFC-chapulin-hardening, Cluster 2 — Crash-totality):
  ## `classifyType`'s resolved-type-name text-match catch-all
  ## (`dsl_typebridge.nim`) no longer `error()`s at macro-expansion on an
  ## unsupported PARAMETER type — that aborted compilation before any proc
  ## body was walkable, so (unlike CR-2a) there was no statement to demote
  ## and no sound dummy `IRType`. It now classifies to an
  ## `itUninterp("__unsupported:" & s)` placeholder (mirroring the
  ## `__ownership:*` precedent); `allocateSym` raises the generic
  ## `SymexClassifiedDegradeError` carrier (CR-1c) with the new
  ## `feUnsupportedParamType` kind at parameter-allocation time — before the
  ## body is walked — forcing a WHOLE-RUN classified `sxUnknown` instead of a
  ## compile failure or a walk-time crash. No new exception type; reuses the
  ## CR-1c carrier and the `__ownership:`-style `itUninterp` idiom at a new
  ## site. Bump rotates the cache so no stale pre-CR-2b compile-failure state
  ## (there is none cached — a compile failure has no cache entry) confuses
  ## the new classified `sxUnknown` verdicts now reachable from previously
  ## uncompilable SUT param-type shapes.
  ##
  ## CR-2a (RFC-chapulin-hardening, Cluster 2 — Crash-totality): `parseExpr`'s
  ## expression-position catch-all (`dsl_parser.nim`) no longer `error()`s at
  ## macro-expansion on an unsupported NimNode `kind` — that aborted
  ## compilation outright, strictly worse than `sxUnknown`. It now registers a
  ## classified `sevError` (`feUnsupportedExprKind`), emits `mkUnsupported`
  ## into the preamble, and returns a type-correct dummy (`classifyType(n).ty`
  ## — resolvable regardless of `n.kind`), reusing the A7-S3
  ## `runeLen(symbolic)` degrade idiom. Sound via SND-1 (`of isUnsupported`
  ## taints `Path.uncertain`) — the dummy can never produce a false witness.
  ## Bump rotates the cache so no stale pre-CR-2a compile-failure state (there
  ## is none cached — a compile failure has no cache entry) confuses the new
  ## classified `sxUnknown` verdicts now reachable from previously-unreachable
  ## SUT shapes.
  ##
  ## CR-1c (RFC-chapulin-hardening, Cluster 2 — Crash-totality, ADR-0020):
  ## a final `except CatchableError` catch-all on the existing `runSymex` try
  ## now converts a genuinely UNANTICIPATED native exception — one that
  ## matched none of the specific arms (NEITHER a known construct-gap
  ## `Symex*Error` carrier, NOR `SymexClassifiedDegradeError`, NOR a
  ## `Z3Error`) and thus escaped the walker from any dispatch depth — into a
  ## classified `sxUnknown` carrying the DISTINCT `weInternalWalkerFault`
  ## kind, instead of crashing the process. Previously such a fault propagated
  ## uncaught out of `runSymex` entirely; now it resolves to a sound,
  ## classified `sxUnknown`. `Defect`-class raises (`doAssert` and friends)
  ## are NOT `CatchableError` and stay uncaught (crash-doctrine). Also adds
  ## the generic `SymexClassifiedDegradeError` carrier (for deliberate
  ## pre-classified degrades; CR-2b reuses it). Bump rotates the cache so no
  ## stale pre-CR-1c entry (from a run that would have crashed) masks the new
  ## classified verdict.
  ##
  ## CR-1b (RFC-chapulin-hardening, Cluster 2 — Crash-totality):
  ## tail-return-of-local fixed at lowering. A value-returning callee whose
  ## body binds a local `let` and implicitly returns an expression over it
  ## (`let hi = data[o] mod 256; hi + 1`) previously native-crashed with an
  ## uncaught `KeyError: key not found: hi` — the walker's `iekVar` env
  ## lookup was faithful, but the parser's `nnkStmtListExpr` arm (how
  ## semcheck presents the implicit `result = (let hi = ...; hi + 1)` RHS)
  ## took only the LAST child, silently discarding the leading `let` the
  ## tail expression depends on. The fix parses leading children into the
  ## existing `preamble` A-normalisation channel so the binding reaches the
  ## tail expression's `env` at walk time — a pure parser fix; `iekVar` is
  ## unchanged and unguarded (no soft-fail was introduced). Previously-
  ## crashing SUTs calling such a callee now resolve to a sound `sxSat`/
  ## `sxUnsat`; bump rotates the cache so no stale entry masks the
  ## newly-supported verdict.
  ## Prior (v41): CR-1a (RFC-chapulin-hardening, Cluster 2 — Crash-totality): bitwise
  ## `and`/`or`/`xor` where an operand is Z3-Int-sorted (`.len`/`.find`/
  ## `.indexOf`/`parseInt` — these are UNCONDITIONALLY svInt, never a
  ## BV-promotion choice) previously native-crashed with `ValueError:
  ## bitwise op on promoted Z3Int`. Now bridges the Int-sorted operand(s)
  ## to BV via `int2bv` (unsigned; these values are always non-negative)
  ## and dispatches through the existing BV bitwise path, producing a
  ## sound `sxSat`/`sxUnsat` instead of a crash. Previously-crashing SUTs
  ## using `and`/`or`/`xor` on a `.len`/`.find`/`.indexOf`/`parseInt`
  ## result now resolve; bump rotates the cache so no stale entry masks
  ## the newly-supported verdict. Existing `svBV*`-param bitwise tests are
  ## unaffected (that code path is untouched).
  ## Prior (v40): Phase 16 SND-2 (RFC-chapulin-hardening, Cluster 1, ADR-0019): `isAssume`
  ## distinct IR kind. `symexAssume(cond)` no longer lowers to `mkAssert`
  ## (byte-identical to `symexAssert`, which unconditionally forked an
  ## `AssertionDefect`) — it now conjoins `cond` into the path condition
  ## (filter/prune) WITHOUT forking the defect. The new `canonicalize`
  ## render tag (`St<Am:...>`, distinct from `isAssert`'s `St<At:...>`)
  ## changes cache keys for any SUT containing `symexAssume`, so the walker
  ## version rotates 39→40.
  ## A7-S3 (concrete runes/runeLen + symbolic degrade, walker v37, ADR-0017 Path B):
  ## `runeLen(lit)` → concrete numeral decoded in Nim at parse time (unicode.runeLen).
  ## `for r in lit.runes:` → static unroll: each rune bound to iterName as svInt.
  ## `runeLen(s)` / `for r in s.runes:` (symbolic s) → seZ3StringIncomplete (sxUnknown).
  ## This closes the A7 cluster and the Phase-16 RFC.
  ## (Prior: A7-S2 $r UTF-8 encoding "36"; A7-S1 Rune model "35"; A9 "34"; A8 "33".)
  ## Previously-cached results for Rune-`$`-typed SUTs are now stale; bump rotates.
  ## Path B is ADDITIVE — byte model and S-cluster tests are untouched.
  ## Prior (v35): A7-S1 (Unicode Rune codepoint model, walker v35, ADR-0017 Path B):
  ## `Rune` from std/unicode is now classified as `tInt(64, signed=true)` pinned
  ## [0, 0x10FFFF] (svInt with range constraints in initialPC). `ord(r)` is
  ## intercepted as identity; `Rune(intExpr)` coerces via nnkConv identity.
  ## Borrow comparison ops (==, !=, <, <=, >, >=) on Rune params as nnkCall
  ## are intercepted and lowered to direct Z3Int binops. Previously-cached
  ## sxUnknown results for Rune-typed SUTs are now stale; bump rotates the cache.
  ## Path B is ADDITIVE — the byte-faithful string model (ADR-0006, S-cluster) is
  ## completely untouched. Prior (v34): A9 (ASCII case-fold, walker v34): `toLowerAscii`/`toUpperAscii` now lower
  ## to a quantifier-free `seqMapBody` BV18-ITE fold (ADR-0015). `toLower`/
  ## `toUpper` (std/unicode) still degrade to sxUnknown. `iekStrToLower`/
  ## `iekStrToUpper` added to StrOpKinds; each carries the string operand in
  ## `strArgs[0]`. Previously-cached sxUnknown results for SUTs using
  ## `toLowerAscii`/`toUpperAscii` are now stale; bump rotates the cache.
  ## Prior (v33): A8 (radix formatting, walker v33): `toHex`/`toBin` on fixed-width BV int
  ## types (int8/16/32/64, uint8/16/32/64) now lower to an svString via a
  ## BV-nibble-extract + ITE digit-table encoding (quantifier-free, no hang).
  ## `toOct`, symbolic-len, and non-int operands degrade soundly to sxUnknown.
  ## `iekRadixFmt` added to StrOpKinds; strOp encodes `"<name>:<base>:<numDigits>"`.
  ## Previously-cached sxUnknown results for SUTs using toHex/toBin are now stale.
  ## Prior (v32): A3-S2a (tuple-yield inline iterators, walker v32): `for a, b in it():` now
  ## inlines when the iterator yields explicit tuple constructors `(e1, e2)`.
  ## Each loop variable binds to the corresponding positional tuple element.
  ## Non-constructor yields (indirect tuple var) and arity mismatches degrade
  ## soundly to sxUnknown (Invariant 3). Previously-cached sxUnknown results for
  ## SUTs with multi-var for-loops over direct iterators are now stale; bump
  ## rotates the cache.
  ## Prior (v31): A3 Slice 2 (augmented-assignment desugaring, walker v31): `<simpleVar>
  ## <op>= <rhs>` with `<op>=` ∈ {+=, -=, *=} now desugars to the same IR as
  ## the explicit `<var> = <var> <op> <rhs>` form. Previously these fell through
  ## to `isUnsupported` → `sxUnknown`. Previously-cached sxUnknown results for
  ## SUTs using augmented assign are now stale; bump rotates the cache.
  ## Non-simple LHS (field, index, other op) continues to degrade soundly
  ## (Invariant 3). No new IR nodes; reuses mkAssign/mkBinop.
  ## Prior (v30): A3 Slice 1 (ADR-0014): closure/inline iterator inlining. A `for x in
  ## it(args):` over a direct user-iterator call is now desugared at parse time
  ## by inlining the iterator body — exactly as Nim's own inline-iterator
  ## expansion. Produces only existing IR (isWhile/isIf/isLet/…), reuses the
  ## full walker including `isWhile` bounded-unroll. Previously-cached
  ## `sxUnknown` results for such SUTs (which routed through the `iekLambda`
  ## stub → `ceNotImplemented`) are now stale; bump rotates the cache. No new
  ## IR node; all pre-scans (return/break-continue/recursion/default-params)
  ## mechanized so no degradation is ever silent (Invariant 3).
  ## Prior (v29): A2 Slice 3 (ADR-0013): arm-specific field WRITE through a ref-to-variant
  ## pointee. `isDeref` now models `p.<armField>` on an `itVariant` pointee —
  ## materialise the disc heap, FieldDefect-fork the out-of-arm side (D1a) and
  ## bind an ite-chain over the matching arms' per-(arm,field) heaps
  ## (`__@<ord>__<field>` key, D1/D2); the witness serializer emits the active
  ## arm's observed fields (D5, `currentVariantHeaps`). Previously-cached
  ## `sxUnknown`/`heRefVariantUnsupported` results for such SUTs are now stale.
  ## Prior (v27): A2 Slice 1 (ADR-0013): discriminant read/write through a
  ## ref-to-variant pointee. `isDeref` and `isDerefWrite` handle `itVariant`
  ## pointees for the discriminant field and plain fields; `itMultiVariant`
  ## still raises (Slice 4 deferred). The disc heap `__@disc` key (@ prefix is a
  ## collision guard) and the disc-range disjunction (D4.5) were introduced.
  ## Prior (v26): R16-4 (Phase 16): signed integer arithmetic (+/-/*) on BV operands now
  ## forks an OverflowDefect raise path when the result may overflow (when
  ## `acOverflow in arithChecks`). Uses Z3 BV overflow predicates
  ## (addNoOverflow/addNoUnderflow/subNoOverflow/subNoUnderflow/mulNoOverflow/
  ## mulNoUnderflow) for exact signed-overflow detection. Unsigned BV wraps
  ## silently (no fork). svInt (unbounded) is skipped (BV predicates on Int
  ## hang Z3). The rhsHasInlineDefectFork guard in dsl_parser now also covers
  ## bAdd/bSub/bMul so `a < 100 and a+1 > 50` does not false-positive.
  ## Invalidates all "24" cache entries where acOverflow was on.
  ## R16-3 (Phase 16): div/mod-by-zero now forks a DivByZeroDefect raise path
  ## when the divisor may be zero (when `acDivByZero in arithChecks`). A short-
  ## circuit guard in dsl_parser (rhsHasInlineDefectFork, renamed from
  ## rhsHasConvFloatToInt) prevents false positives when div/mod appears in the
  ## RHS of `and`/`or` guarded by e.g. `b != 0`. Also adds DivByZeroDefect and
  ## OverflowDefect to the exception hierarchy table (exn_hierarchy.nim) so
  ## `except DivByZeroDefect:` correctly catches the raise fork. Invalidates
  ## all "23" cache entries where acDivByZero was on (the new fork would fire).
  ## R16-2b (Phase 16): float→int conv in and/or short-circuit RHS now forced
  ## to the guarded path (even when rhsPreamble is empty) via rhsHasInlineDefectFork
  ## predicate. Fixes false positive: guarded int(x) in x>3.0 and x<4.0 and
  ## int(x)==3 no longer reports sxRaised(RangeDefect). Invalidates all "22"
  ## entries that cached a wrong sxRaised verdict for such programs.
  ## R16-2 (Phase 16): float→int conversion now forks a RangeDefect raise path
  ## for out-of-range/NaN/Inf operands (when `acRange in arithChecks`). A run
  ## under "21" that used int(f)/int32(f) would NOT have this raise path; under
  ## "22" it may surface sxRaised(RangeDefect). Invalidates all "21" entries so
  ## no stale pre-R16-2 verdict is served.
  ## R16-1 (Phase 16 ADR-0011): adds `arithChecks` (set[ArithCheck]) to the
  ## cache key (`;ac=`). Two runs differing only in `arithChecks` would produce
  ## the same key under "20"; bumping to "21" ensures they diverge correctly and
  ## invalidates all "20" entries so no stale pre-R16-1 key is served.
  ## D1c (Phase 16): models `and`/`or` short-circuit; removes FieldDefect /
  ## IndexDefect / NilAccessDefect false positive on guarded RHS sub-exprs.
  ## Parser desugars `a and b` / `a or b` (when b has a non-empty preamble)
  ## into an `isLet` + `isIf` bool-temp guard so the RHS preamble only runs
  ## when the LHS value demands it. Old "19" cache entries for programs using
  ## guarded `and`/`or` had WRONG verdicts (sxRaised where sxSat is correct)
  ## and must be invalidated.
  ## D1a (Phase 16): defect targets (IndexDefect, FieldDefect, AssertionDefect,
  ## NilAccessDefect) now route through `routeRaise`, returning `sxRaised` with
  ## `raisedTypeId`/`raisedWitness` instead of `sxSat` with `witness`. Old cache
  ## entries for defect targets are INVALID (wrong status + wrong field names) and
  ## must be invalidated. "19" rotation ensures no stale sxSat entries survive.
  ## A5 (Phase 16): model `classify(f)` → `FloatClass` and `copySign(x, y)` in
  ## `lowerMathCall` (runtime_floats.nim). `classify` lowers to a `svBV64`
  ## ite-chain over the shipped FP predicates (isNaN/isInf/isZero/isSubnormal/
  ## isNegative) yielding the FloatClass ordinal; `probeProto` returns a matching
  ## svBV64 so the enum-ordinal literal in `classify(f) == fcNan` lowers BV-side
  ## (single-theory — avoids the int↔BV `int2bv(bv2int …)` F5 hang). `copySign`
  ## is `ite(isNegative(y), neg(abs(x)), abs(x))`. `nextafter` stays
  ## `feUnsupportedOp` (no SMT-LIB FP-theory primitive — documented bound).
  ## VERDICT-ADDITIVE: programs using classify/copySign were `sxUnknown` under
  ## "17" and are now `sxSat`/`sxUnsat`; stale "17" cache entries for such
  ## programs are WRONG (sxUnknown cached, now a real verdict). renderAsChoices
  ## unchanged at "4": no new witness shape (the classify result is an ordinary
  ## BV64 integer witness via the normal extraction path).
  ##
  ## Previous (17): CR-21 fix (Phase 15): `isCall` arg-lowering now drains `parseIntRaiseConds`
  ## after the argument loop. Previously, if any actual argument expression
  ## contained a `parseInt(s)` call, the accumulated raise predicates were
  ## DROPPED (never forked into ValueError raise paths). The callee dispatch
  ## proceeded as if parseInt always succeeded → false-safe for non-digit inputs.
  ## Fix: add `parseIntRaiseConds = @[]` threadvar reset + call
  ## `drainParseIntRaises(pd, w)` after `drainPendingLowerEffects`; wrap the
  ## callee dispatch in a `for p in drainParseIntRaises(pd, w):` loop so raise
  ## paths surface correctly. Stale "16" cache entries for procs that call a
  ## helper with a parseInt-containing arg are WRONG (missing raise paths).
  ## renderAsChoicesVersion: unchanged at "4" (the raise-path witness is an
  ## existing sxRaised shape; no format change).
  ##
  ## Previous (16): CR-19 fix (Phase 15): `classifyFieldType` now correctly handles `ref
  ## PRIMITIVE` fields (e.g. `p: ref int` as a field of an object param).
  ## Previously the inline `ref T` arm matched any `nnkSym` inner type —
  ## including primitive builtins like `int` — and produced a named-tuple
  ## placeholder (`tRef(tTuple([],"int"))`, sort `Ref_int__`). The deref
  ## site's `dElemTy` produced `tInt(64,true)` (sort `Ref_i64_s`); the sort
  ## mismatch caused Z3SortMismatchError → sxUnknown for all `h.p[]` /
  ## `h.p[]=v` programs where `p: ref int` is an object field. Fix: gate the
  ## placeholder arm on `isObjectTypeSym` (struct getImpl returns nnkObjectTy)
  ## so primitive pointees fall through to `classifyType(ty)` → `tRef(tInt(64,
  ## true))`, matching `dElemTy` exactly. The Z3 sort names are now
  ## byte-identical; sxUnknown → sxSat for those programs. Stale "15" cache
  ## entries for such programs are WRONG (sxUnknown cached, now sxSat).
  ## renderAsChoicesVersion: unchanged at "4" (the rendered int witness value
  ## is the same int64 via the normal BV64 extraction path).
  ##
  ## Previous (15): CR-22 fix (Phase 15): scoped assert-expansion detection in
  ## `parseStmtInner`.  Previously `findAssertFailsCond` was called on the
  ## entire enclosing `nnkStmtList`, replacing the WHOLE list with the
  ## assert-raise IR and silently dropping any sibling statements (e.g.
  ## `symexTarget` label calls).  Now the detection is scoped to the
  ## `nnkPragmaBlock` node that IS the assert expansion; sibling statements
  ## are parsed and preserved in order.  Procs mixing `symexTarget` labels
  ## with `doAssert` now surface BOTH the label's `sfSat` AND the assert's
  ## `sfRaised(AssertionDefect)` findings; previously only `sfRaised` was
  ## produced.  Stale v14 cache entries for such mixed procs are WRONG
  ## (label finding absent) — the bump to "15" invalidates them.
  ##
  ## Previous (14): Phase 15 F5-probeproto fix. `probeProto`'s
  ## `iekConvFloatToInt` arm returns a matching BV sentinel (svBV32 for
  ## convWidth==32, svBV64 otherwise).
  ## Stale "13" cache entries whose `int(f)/int32(f)`-vs-literal subterms
  ## were encoded with the bv2int wrap or the wrong-width literal are now
  ## invalid (the literal's Z3 representation changes from svInt to svBV64/
  ## svBV32). renderAsChoicesVersion unchanged at "4": the rendered Nim
  ## integer witness value is extracted by `readInt` regardless of BV width.
  ## - "13" — Phase 15 F5-hang-regression fix. `iekConvFloatToInt` int64 case now
  ## returns `svBV64` directly (symmetric with int32 → svBV32), dropping
  ## the anomalous `bvToZ3Int` wrap that produced `bv2int(fp.to.sbv f)` as
  ## a Z3Int. With the old code, `isDerefWrite`'s `svInt → BV64` coercion
  ## then wrapped it in `int2bv`, giving `int2bv(bv2int(fp.to.sbv f))` as
  ## the stored heap value — a mixed Int+BV+FP round-trip that could cause
  ## Z3 to hang on ordering goals (`q[] > k`). Stale "12" entries whose
  ## `int(f)` result was `svInt` are now invalid (the int64 witness
  ## representation changes from an unbounded-Int to a BV64 term).
  ## renderAsChoicesVersion: unchanged at "4". The float→int64 witness is
  ## extracted by `readInt`/the integer rendering path, which reads the
  ## witness value as a Nim int64 regardless of whether the internal term
  ## was svInt or svBV64 — the rendered int64 choice is identical. Only the
  ## Z3 term representation changes, not the serialised witness shape.
  ## - "12" — Phase 15 re-review bump (S-1 through S-4, NI-1, NI-2, D-3).
  ## `drainPendingLowerEffects` consolidation: every lower()/lowerBool()
  ## call site in walk now seeds caller-heap threadvars and drains both
  ## the float→int bound sink and the closure exit-heap uniformly. Arms
  ## fixed: isIf (per-branch re-seed), isWhile, isReturn, isCall, isAssert,
  ## isDerefWrite (+ BV reconciliation after svInt drain), isVariantReassignSymbolic,
  ## isIndex (seq + static-array). applyClosureGround liveRefs union-merge
  ## (true set-union replacing "take longest" heuristic). D-3: reconcileFloat
  ## helper extracted from cmpFloat. Stale "11" entries are invalid because
  ## the drain pattern changes which heap/float-bound constraints are in play
  ## for almost every walk arm — cached verdicts are unsound until rotation.
  ## Bumped by maintainers whenever the walker's semantics shift in a
  ## witness-affecting way. Participates in `symexCacheKey` so old
  ## persisted witnesses become invisible after a walker semantic
  ## change.
  ##
  ## - "1" — Phases 0-10 baseline (variants lowered to flat tuples,
  ##   default(Object) stub for variant witnesses).
  ## - "2" — Phase 11 cycles 1-12: variants as first-class itVariant,
  ##   walker forks at field access, tFieldDefect target added.
  ## - "3" — Phase 11 deferral #5 closed: plain (non-recCase) fields
  ##   shared across arms (allocated once, not per-arm prefixed),
  ##   surviving `obj.kind = X` reassignment. Witness path layout for
  ##   plain fields moved from `<base>.@<tag>.<field>` to
  ##   `<base>.<field>`.
  ## - "5" — Phase 15 Cluster F (float) close-out (cycle F8). Float
  ##   support landed across F1–F7: itFloat32/itFloat64 + svFloat32/
  ##   svFloat64 type-bridge, IEEE literals/arith/compare, int<->float
  ##   conversions (rmRNE / rmRTZ), std/math FP-native ops + predicates
  ##   (iekMathCall), and eval-side bit-exact witness extraction
  ##   (float64Vals/float32Vals). Float SUTs were parser-erroring or
  ##   producing stub witnesses under "4", so no stale "4" entry can
  ##   falsely re-hydrate; a single bump at Cluster F close-out per
  ##   v2 Invariant 1 rotates the cache for the multi-cluster session.
  ## - "6" — Phase 15 Cluster S (full strings) close-out (cycle S11).
  ##   String support landed across S1–S10a: byte-faithful Z3 String
  ##   model (≤0xFF char-range constraint), len/index/slice/high,
  ##   find/contains/startsWith/endsWith, replace/split/join, regex
  ##   match, concat, bytes, and `$int`/`parseInt` int<->string. S11
  ##   classifies the immutable-string mutations (`s[i] = c`, `s.add`)
  ##   as `seUnsupportedStringOp`. A single bump at Cluster S close-out
  ##   rotates the cache so any "5"-era string verdict re-solves under
  ##   the now-complete string semantics. (S10b — the parseInt
  ##   raises-path — is deferred to post-E1 and will carry its own bump
  ##   when it lands.)
  ## - "7" — Phase 15 Cluster E (exceptions) close-out (cycle E7).
  ##   Exception support landed across E1–E6: `raise`/`try`/`except`/
  ##   `finally` IR + walker semantics, the `sxRaised` verdict path
  ##   (`cacheKeyRaised(typeId)`), first-match handler resolution with
  ##   subtype catch over the static exn hierarchy + dynamic user-exn
  ##   hierarchy (E4/E4a), inter-procedural raise propagation, finally
  ##   composition on both exit paths (finally-raises-replaces), and
  ##   `Defect` modeling (`sxRaised{isDefect}` + `defectExclusions`).
  ##   A single bump at Cluster E close-out rotates the cache so any
  ##   "6"-era verdict re-solves under the now-complete exception
  ##   semantics. (E8 — `getCurrentException` — is additive under "7".)
  ## - "8" — Phase 15 Cluster G (generics) close-out (cycle G10).
  ##   Generics support landed across G1a–G8: parse-time monomorphization
  ##   keyed by an ADR-0008 D2 instantiation key (`instKeyFor` — fixes the
  ##   bare-name `ctx.procs` collision so two instantiations of one generic
  ##   register as distinct `ProcSig`s), an instantiation cap
  ##   (`maxInstantiationsPerProc`, default 64 → `geInstantiationCapped`),
  ##   `distinct T` as a fresh uninterpreted sort with a ground eject-pin
  ##   round-trip (G4) and SymVal-level borrow semantics (G5), concept
  ##   constraints validated parse-time against a stdlib membership table
  ##   (G6, `geConceptViolation`), `static[T]` params folded into the
  ##   instantiation key via per-instantiation bodyHash (G7), and
  ##   order-independent multi-param keys (G8). A single bump at Cluster G
  ##   close-out rotates the cache so any "7"-era verdict re-solves under
  ##   the now-complete generics semantics.
  ## - "9" — Phase 15 Cluster C (closures + procs-as-values) close-out
  ##   (cycle C6). Closure support landed across C1–C5: net-new
  ##   `iekLambda`/`iekClosureCall` IR + `svClosure` (site key + captured
  ##   `svTuple` env + per-site uninterpreted `funcSym`), closure
  ##   CONSTRUCTION (C2a env snapshot + `currentClosureSyms` funcSym memo),
  ##   closure CALL via the GROUND per-sub-path axiom `implies(branch_conds,
  ##   funcSym(env,args) == v_i)` (C2b — never a `∀env,args` quantifier, the
  ##   G4 hang lesson), top-level procs-as-values as unit-env closures (C3),
  ##   DSL `filter`/`map` HOFs over `seq[T]` (C4 — bounded inline path +
  ##   `mapArray` symbolic path), and nominal-for-site + structural-for-env
  ##   closure equality via the net-new `svTupleEq` (C5). A single bump at
  ##   Cluster C close-out rotates the cache so any "8"-era verdict re-solves
  ##   under the now-complete closure semantics.
  ## - "10" — Phase 15 Cluster R (ref/ptr aliasing via logical heap) close-out
  ##   (cycle R12 — the FINAL Phase 15 cluster bump). Heap support landed across
  ##   R1–R11b: per-pointee-type `Ref_<typeId>` uninterpreted address sort +
  ##   per-path `Z3Array[Ref_T, T]` logical heap (ADR-0010), GROUND
  ##   `select`/`store` deref reads/writes (R1/R3/R4 — never a `∀addr`
  ##   quantifier, the G4 hang lesson), fresh-`new` distinctness + non-nil
  ##   freshness (R2), the `nil_<typeId>` const + NilAccessDefect fork under
  ##   `tNilAccess()` (R5), field-split `ref object` heaps with alias-observable
  ##   field writes (R6), let-alias chains (R7), `ptr T` deref + `hePtrFamily`
  ##   hint (R8), recursive `ref object` walks halting at the heap-depth budget
  ##   (R9/R10, `heDepthExhausted`), and `cast[ptr]` classification
  ##   (`heUnsafeCast`, R11). R12 adds the heap-snapshot witness FORMAT (see the
  ##   `renderAsChoicesVersion` `"3"` note) and bumps the walker version so any
  ##   "9"-era verdict re-solves under the now-complete heap semantics. Cluster
  ##   R is the FINAL cluster.
  ## - "11" — Phase 15 CR-2 consolidated code-review fix bump. CR-1 (closure
  ##   heap write-back merge — false-UNSAT fix), CR-3 (float→int domain bounds —
  ##   unsound witness fix), CR-4 (int32 → svBV32 correct-width fix), CR-5
  ##   (closure liveRefs seeding — spurious aliasing fix), and CR-6 (mixed-float
  ##   compare crash fix) all changed the walker's verdict-producing semantics.
  ##   A single consolidated bump at CR-2 close-out rotates the cache so any
  ##   "10"-era verdict re-solves under the corrected semantics.

proc canonicalize*(t: IRType): string =
  if t.isNil:
    return "Ty<nil>"
  case t.kind
  of itInt:
    "Ty<I:" & $t.width & ":" & (if t.signed: "s" else: "u") & ">"
  of itBool:
    "Ty<B>"
  of itString:
    "Ty<S>"
  of itUninterp:
    "Ty<U:" & t.uninterpName & ">"
  of itFloat32: "Ty<F32>"
  of itFloat64: "Ty<F64>"
  of itDistinct:
    # Phase 15 G4: nominal distinct-name + recursive base encoding. The
    # name is the type wall identity; the base recurses (nested chains).
    "Ty<D:" & t.distinctName & ":" & canonicalize(t.distinctBase) & ">"
  of itRef:   ## Phase 15 R1a: ref + recursive pointee. Distinct tag from ptr.
    "Ty<Rf:" & canonicalize(t.refPointeeTy) & ">"
  of itPtr:   ## Phase 15 R1a: ptr + recursive pointee.
    "Ty<Pt:" & canonicalize(t.ptrPointeeTy) & ">"
  of itTuple:
    # Positional encoding: field order is significant; field-name
    # spelling is encoded only when present (named tuples / object
    # field accessors), since renaming an anonymous-tuple field is
    # by definition a no-op but renaming a named field changes
    # `iekField` lookups.
    var parts: seq[string]
    for i in 0 ..< t.fields.len:
      let nm = if i < t.fieldNames.len: t.fieldNames[i] else: ""
      parts.add nm & "=" & canonicalize(t.fields[i])
    "Ty<T:" & t.objectName & ":" & parts.join(";") & ">"
  of itArray:
    "Ty<A:" & $t.size & ":" & canonicalize(t.elemTy) & ">"
  of itSeq:
    "Ty<Sq:" & canonicalize(t.seqElemTy) & ">"
  of itTable:
    "Ty<Tb:" & canonicalize(t.tabKeyTy) & ";" & canonicalize(t.tabValTy) & ">"
  of itSet:
    "Ty<Se:" & canonicalize(t.setElemTy) & ">"
  of itVariant:
    var plainParts: seq[string]
    for i in 0 ..< t.vPlainFieldNames.len:
      plainParts.add t.vPlainFieldNames[i] & "=" &
                     canonicalize(t.vPlainFieldTypes[i])
    var armParts: seq[string]
    for arm in t.vArms:
      var fParts: seq[string]
      for i in 0 ..< arm.fieldNames.len:
        fParts.add arm.fieldNames[i] & "=" & canonicalize(arm.fieldTypes[i])
      armParts.add $arm.tagOrdinal & ":" & arm.tagName &
                   (if arm.isElse: ":else" else: "") &
                   ":[" & fParts.join(";") & "]"
    # Phase 14 A2: encode `vDiscTags` so two variants with the same
    # of-arms but different else-coverage hash differently.
    var ordParts: seq[string]
    for dt in t.vDiscTags: ordParts.add dt.name & "=" & $dt.ord
    "Ty<Vr:" & t.vObjectName &
      ";plain=[" & plainParts.join(";") & "]" &
      ";disc=" & t.vDiscName & "=" & canonicalize(t.vDiscTy) &
      ";dtags=[" & ordParts.join(",") & "]" &
      ";[" & armParts.join(",") & "]>"
  of itMultiVariant:
    # Phase 14 (ADR-0003 D1). Distinct prefix `MVr:` and distinct
    # axis-grouped format `;axes=[...]` ensure cache keys do not
    # collide with single-axis `itVariant` keys.
    var plainParts: seq[string]
    for i in 0 ..< t.mvPlainFieldNames.len:
      plainParts.add t.mvPlainFieldNames[i] & "=" &
                     canonicalize(t.mvPlainFieldTypes[i])
    var axisParts: seq[string]
    for ax in t.mvAxes:
      var armParts: seq[string]
      for arm in ax.arms:
        var fParts: seq[string]
        for i in 0 ..< arm.fieldNames.len:
          fParts.add arm.fieldNames[i] & "=" &
                     canonicalize(arm.fieldTypes[i])
        armParts.add $arm.tagOrdinal & ":" & arm.tagName &
                     (if arm.isElse: ":else" else: "") &
                     ":[" & fParts.join(";") & "]"
      var ordParts: seq[string]
      for dt in ax.discTags: ordParts.add dt.name & "=" & $dt.ord
      axisParts.add "axis(" & ax.discName & "=" & canonicalize(ax.discTy) &
                    ";dtags=[" & ordParts.join(",") & "]" &
                    ";[" & armParts.join(",") & "])"
    "Ty<MVr:" & t.mvObjectName &
      ";plain=[" & plainParts.join(";") & "]" &
      ";axes=[" & axisParts.join(";") & "]>"

# ---- Local-name rewriting ---------------------------------------------------
#
# Local let/assign names are encoded positionally so renames don't
# invalidate witnesses. `LocalEnv` walks the IR in declaration order
# (depth-first, syntactic) and assigns each `let` the next `$N` slot;
# every later `iekVar` that refers to a local gets rewritten through
# the same map. Free variables (params, top-level callees) are
# encoded by their original name — they're part of the program's
# external surface, not internal.
type LocalEnv = ref object
  slots: Table[string, int]   # original-name → de-Bruijn-style slot id
  next:  int

proc newLocalEnv(): LocalEnv =
  LocalEnv(slots: initTable[string, int](), next: 0)

proc bindLocal(env: LocalEnv, name: string): int =
  result = env.next
  env.slots[name] = result
  inc env.next

proc lookupLocal(env: LocalEnv, name: string): string =
  if name in env.slots:
    "$" & $env.slots[name]
  else:
    name  # free — encode by original name

# ---- IRExpr -----------------------------------------------------------------

proc binopTag(op: IRBinop): string =
  case op
  of bAdd: "+"
  of bSub: "-"
  of bMul: "*"
  of bDiv: "/"
  of bMod: "%"
  of bAnd: "&"
  of bOr:  "|"
  of bXor: "^"
  of bShl: "<<"
  of bShr: ">>"
  of bEq:  "=="
  of bNe:  "!="
  of bLt:  "<"
  of bLe:  "<="
  of bGt:  ">"
  of bGe:  ">="

proc unopTag(op: IRUnop): string =
  case op
  of uNot: "!"
  of uNeg: "~"

proc canonicalize(s: IRStmt, env: LocalEnv): string  ## fwd: Phase 15 C1
  ## (iekLambda folds its body's canonical form — mutual with the stmt arm).

proc canonicalize(e: IRExpr, env: LocalEnv): string =
  if e.isNil: return "Ex<nil>"
  case e.kind
  of iekIntLit:    "Ex<IL:" & $e.ival & ">"
  of iekFloatLit:  "Ex<FL:" & $e.fwidth & ":" & $e.fval & ">"
  of iekConvIntToFloat: "Ex<CIF:" & $e.convWidth & ":" & canonicalize(e.convOperand, env) & ">"
  of iekConvFloatToInt: "Ex<CFI:" & $e.convWidth & ":" & canonicalize(e.convOperand, env) & ">"
  of iekMathCall:
    var parts: seq[string]
    for a in e.mathArgs: parts.add canonicalize(a, env)
    "Ex<MC:" & e.mathOp & ":" & parts.join(",") & ">"
  of iekBoolLit:   "Ex<BL:" & $e.bval & ">"
  of iekVar:       "Ex<V:" & lookupLocal(env, e.vname) & ">"
  of iekBinop:
    "Ex<Bn:" & binopTag(e.bop) & ";" &
      canonicalize(e.lhs, env) & ";" & canonicalize(e.rhs, env) & ">"
  of iekUnop:
    "Ex<Un:" & unopTag(e.uop) & ";" & canonicalize(e.operand, env) & ">"
  of iekBorrowOp:   ## Phase 15 G5: the distinct name + base op + operands
                    ## content-address the borrow distinctly.
    "Ex<Bw:" & e.borrowDistinctName & ";" & binopTag(e.borrowOp) & ";" &
      $e.borrowReturnsDistinct & ";" &
      canonicalize(e.borrowLhs, env) & ";" & canonicalize(e.borrowRhs, env) & ">"
  of iekField:
    "Ex<F:" & $e.fieldIx & ";" & canonicalize(e.obj, env) & ">"
  of iekIndex:
    "Ex<Ix:" & canonicalize(e.arr, env) & ";" &
      canonicalize(e.idx, env) & ">"
  of iekArrayLit:
    var parts: seq[string]
    for x in e.lelems: parts.add canonicalize(x, env)
    "Ex<AL:" & canonicalize(e.lelemTy) & ";[" & parts.join(",") & "]>"
  of iekSeqLen:    "Ex<SL:" & canonicalize(e.lenObj, env) & ">"
  of iekStrLit:    "Ex<S:" & e.sval.escape & ">"
  of iekContains:
    "Ex<C:" & canonicalize(e.container, env) & ";" &
      canonicalize(e.key, env) & ">"
  of iekSeqAdd, iekSetIncl, iekSetExcl, iekTableDel:
    "Ex<" & $e.kind & ":" & canonicalize(e.mutRecv, env) & ";" &
      canonicalize(e.mutArg, env) & ">"
  of iekSeqDel:
    "Ex<SqD:" & canonicalize(e.delSeq, env) & ";" &
      canonicalize(e.delIdx, env) & ">"
  of iekSeqInsert:
    "Ex<SqI:" & canonicalize(e.insSeq, env) & ";" &
      canonicalize(e.insVal, env) & ";" &
      canonicalize(e.insIdx, env) & ">"
  of iekSeqPop:    "Ex<SqP:" & canonicalize(e.popSeq, env) & ">"
  of iekTableSet:
    "Ex<TS:" & canonicalize(e.tabRecv, env) & ";" &
      canonicalize(e.tabKey, env) & ";" &
      canonicalize(e.tabVal, env) & ">"
  of StrOpKinds:
    # Phase 15 Cluster S (S1). Canonical tag keys on the IR kind + op name +
    # operands so distinct string ops get distinct content-addressed cache keys.
    var parts: seq[string]
    for a in e.strArgs: parts.add canonicalize(a, env)
    "Ex<St:" & $e.kind & ":" & e.strOp & ":[" & parts.join(",") & "]>"
  of iekGetCurrentExn:    "Ex<GCE>"      ## Phase 15 E8
  of iekGetCurrentExnMsg: "Ex<GCEM>"     ## Phase 15 E8
  of iekLambda:                          ## Phase 15 C1 (ADR-0009 D3/D8): the
                                         ## site key + capture names + concrete
                                         ## param types content-address the
                                         ## lambda; the body is folded in so two
                                         ## site-colliding-but-different bodies
                                         ## (re-indented edits aside) differ.
    var caps = e.lambdaCaptures
    var ptys: seq[string]
    for p in e.lambdaParams: ptys.add canonicalize(p.ty)
    "Ex<Lam:site=" & $e.lambdaSite.siteHash & "/" & $e.lambdaSite.declOrder &
      ";caps=[" & caps.join(",") & "];params=[" & ptys.join(",") & "]" &
      ";retTy=" & canonicalize(e.lambdaRetTy) &
      ";body=" & canonicalize(e.lambdaBody, env) & ">"
  of iekClosureCall:                     ## Phase 15 C1: distinct partition from
                                         ## an isCall to the same name (Cn:) so a
                                         ## proc-valued-variable call never
                                         ## cache-collides with a named call.
    var argKeys: seq[string]
    for a in e.ccArgs: argKeys.add canonicalize(a, env)
    "Ex<CC:" & e.ccCallee & "(" & argKeys.join(",") & ")>"
  of iekSeqLit:                          ## Phase 15 C4
    var es: seq[string]
    for c in e.seqLitElems: es.add canonicalize(c, env)
    "Ex<SeqLit:" & canonicalize(e.seqLitElemTy) & ":[" & es.join(",") & "]>"
  of iekHofCall:                         ## Phase 15 C4
    let initKey = if e.hofInit != nil: canonicalize(e.hofInit, env) else: "_"
    "Ex<Hof:" & e.hofOp & ":" & canonicalize(e.hofSeq, env) & ":" &
      canonicalize(e.hofClosure, env) & ":" & initKey & ":" &
      canonicalize(e.hofRetElemTy) & ">"
  of iekNil:                             ## Phase 15 R5
    "Ex<Nil:" & canonicalize(e.nilPointee) & ">"

# ---- IRStmt -----------------------------------------------------------------

proc canonicalize(s: IRStmt, env: LocalEnv): string =
  if s.isNil: return "St<nil>"
  case s.kind
  of isBlock:
    var parts: seq[string]
    for x in s.stmts: parts.add canonicalize(x, env)
    "St<Bk:[" & parts.join(",") & "]>"
  of isIf:
    var parts: seq[string]
    for br in s.branches:
      parts.add "(" & canonicalize(br.cond, env) & "=>" &
        canonicalize(br.body, env) & ")"
    "St<If:[" & parts.join(",") & "];else=" &
      canonicalize(s.elseBody, env) & ">"
  of isLet:
    let slot = bindLocal(env, s.lname)
    "St<Lt:$" & $slot & ":" & canonicalize(s.lty) & "=" &
      canonicalize(s.lvalue, env) & ">"
  of isAssign:
    "St<As:" & lookupLocal(env, s.aname) & "=" &
      canonicalize(s.avalue, env) & ">"
  of isWhile:
    "St<W:" & canonicalize(s.wcond, env) & ";body=" &
      canonicalize(s.wbody, env) & ">"
  of isBreak:    "St<Bk>"
  of isContinue: "St<Co>"
  of isReturn:
    "St<R:" & canonicalize(s.retExpr, env) & ">"
  of isCall:
    var args: seq[string]
    for a in s.cargs: args.add canonicalize(a, env)
    let retSlot =
      if s.retName.len > 0: "$" & $bindLocal(env, s.retName)
      else: ""
    "St<Cl:" & s.callee & ";opaque=" & $s.opaque & ";ret=" & retSlot &
      ";retTy=" & canonicalize(s.retTy) & ";args=[" & args.join(",") & "]>"
  of isIndex:
    let retSlot = "$" & $bindLocal(env, s.ixRetName)
    "St<Ix:" & retSlot & "=" & canonicalize(s.ixArr, env) &
      "[" & canonicalize(s.ixIdx, env) & "];ety=" &
      canonicalize(s.ixElemTy) & ">"
  of isVariantField:
    let retSlot = "$" & $bindLocal(env, s.vfRetName)
    var tags = ""
    for t in s.vfMatchingTags: tags.add $t & ","
    "St<VF:" & retSlot & "=" & canonicalize(s.vfRecv, env) & "." &
      s.vfFieldName & ";fty=" & canonicalize(s.vfFieldTy) &
      ";tags=[" & tags & "]>"
  of isVariantReassign:
    "St<VR:" & lookupLocal(env, s.vrObjName) & ".kind=" &
      $s.vrNewTag & ":" & s.vrTagName & ">"
  of isVariantReassignSymbolic:
    # Phase 14 A4a: distinct prefix `VRS:` so cache keys can't
    # collide with static-tag `VR:` entries.
    "St<VRS:" & lookupLocal(env, s.vrsObjName) & "." &
      (if s.vrsDiscName.len == 0: "kind" else: s.vrsDiscName) &
      "=" & canonicalize(s.vrsRhs, env) & ">"
  of isAssert:
    "St<At:" & canonicalize(s.acond, env) & ">"
  of isAssume:
    # Phase 16 SND-2 (round-2 finding): MUST be a distinct tag from `isAssert`
    # (`At:`) — `symexAssert(c)` and `symexAssume(c)` on the same `c` have
    # DIFFERENT verdict semantics (assert forks an AssertionDefect search;
    # assume never does), so sharing a cache-key tag would let one serve a
    # stale/wrong verdict for the other. Mirrors the `VR:`/`VRS:` and `Nw:`/
    # `Dr:` distinct-tag discipline above.
    "St<Am:" & canonicalize(s.acond, env) & ">"
  of isTargetLabel:
    "St<Tg:" & s.tname.escape & ">"
  of isRaise:
    # Phase 15 E1. Content-address by type + reraise flag + message.
    "St<Rs:" & s.raiseTypeId.escape & ";rr=" & $s.raiseIsReraise & ";msg=" &
      canonicalize(s.raiseMsg, env) & ">"
  of isTry:
    var hs: seq[string]
    for h in s.tryHandlers:
      hs.add "(" & h.typeIds.join("|").escape & "=>" &
        canonicalize(h.body, env) & ")"
    "St<Ty:body=" & canonicalize(s.tryBody, env) & ";h=[" & hs.join(",") &
      "];fin=" & canonicalize(s.tryFinally, env) & ">"
  of isDeref:
    # Phase 15 R1a. Content-address by family + pointee type + ptr expr; the
    # fresh let-name binds a new slot. Distinct tag from `isNew` (Nw).
    let slot = bindLocal(env, s.dRetName)
    "St<Dr:$" & $slot & ";fam=" & (if s.dPtrFamily: "ptr" else: "ref") &
      ";fld=" & s.dField & ";ety=" & canonicalize(s.dElemTy) &
      ";p=" & canonicalize(s.dPtr, env) & ">"
  of isNew:
    let slot = bindLocal(env, s.nRetName)
    "St<Nw:$" & $slot & ";ty=" & canonicalize(s.nRefTy) & ">"
  of isDerefWrite:
    # Phase 15 R3. Content-address by family + pointee type + ptr expr + RHS.
    # No fresh let-name is bound (a write, not a read).
    "St<Dw:fam=" & (if s.dwPtrFamily: "ptr" else: "ref") &
      ";fld=" & s.dwField & ";ety=" & canonicalize(s.dwElemTy) &
      ";p=" & canonicalize(s.dwPtr, env) &
      ";v=" & canonicalize(s.dwValue, env) & ">"
  of isUnsupported:
    "St<Un:" & s.reason.escape & ">"
  of isUnsafeCast:
    # Phase 15 R11. Content-address by the routed pointer-materialisation reason.
    "St<Uc:" & s.ucReason.escape & ">"

# ---- Top-level overloads ---------------------------------------------------

proc canonicalize*(e: IRExpr): string =
  canonicalize(e, newLocalEnv())

proc canonicalize*(s: IRStmt): string =
  canonicalize(s, newLocalEnv())

# ---- IRParam ---------------------------------------------------------------

proc canonicalize*(p: IRParam): string =
  # Params live at the program's external boundary — their *position*
  # is the witness's identity (witness[0], witness[1], …), and their
  # *type* matters for encoding. The name is part of the program's
  # source-level surface; renaming a param doesn't affect the
  # witness's structural validity, so it's excluded from the canonical
  # form. `isVar` matters because it affects mutation propagation.
  # Range hints (rangeLo/rangeHi from Natural / range[...]) DO matter
  # because they're consumed by the abstraction layer.
  var range = ""
  if p.hasRange:
    range = ";range=[" & $p.rangeLo & "," & $p.rangeHi & "]"
  "Pm<" & canonicalize(p.ty) & ";isVar=" & $p.isVar & range & ">"

# ---- ProcSig ---------------------------------------------------------------

proc canonicalize*(sig: ProcSig): string =
  var params: seq[string]
  let env = newLocalEnv()
  for p in sig.params:
    discard bindLocal(env, p.name)  # so body's iekVar refs to params
                                    # resolve as locals positionally
    params.add canonicalize(p)
  "Pr<" & sig.name & ";retTy=" & canonicalize(sig.retTy) &
    ";isVoid=" & $sig.isVoid &
    ";cc=[" & sig.conceptConstraints.join(",") & "]" &   ## Phase 15 G6
    ";params=[" & params.join(",") & "]" &
    ";body=" & canonicalize(sig.body, env) & ">"

# ---- SymexProgram ----------------------------------------------------------

proc canonicalize*(prog: SymexProgram): string =
  # Top-level body sees params as bound locals (positionally).
  let env = newLocalEnv()
  var paramParts: seq[string]
  for p in prog.params:
    discard bindLocal(env, p.name)
    paramParts.add canonicalize(p)
  # Callees sorted by name — `Table` iteration order isn't stable.
  var keys: seq[string]
  for k in prog.procs.keys: keys.add k
  sort(keys)
  var procParts: seq[string]
  for k in keys:
    procParts.add canonicalize(prog.procs[k])
  "Pg<params=[" & paramParts.join(",") & "];body=" &
    canonicalize(prog.body, env) &
    ";procs=[" & procParts.join(",") & "]>"

# ---- SymexTarget -----------------------------------------------------------

proc canonicalize*(t: SymexTarget): string =
  case t.kind
  of stkLabel:              "Tg<L:" & t.label.escape & ">"
  of stkAssertionViolation: "Tg<AV>"
  of stkIndexError:         "Tg<IE>"
  of stkFieldDefect:        "Tg<FD>"
  of stkRaisedExn:          "Tg<RX:" & t.typeFilter.escape & ">"   ## Phase 15 E2a
  of stkNilAccess:          "Tg<NA>"                                ## Phase 15 R5

# ---- SymexSettings ---------------------------------------------------------

proc canonicalize*(s: SymexSettings): string =
  ## Audited inclusion/exclusion list (CR-2 close-out). Every field that
  ## provably changes the walker's verdict or the persisted witness shape is
  ## INCLUDED; fields that are verdict-neutral are EXCLUDED with a reason.
  ##
  ## INCLUDED (changing the field changes what the walker computes):
  ##   integerSemantics   — governs BV vs Z3Int encoding; changes sat/unsat.
  ##   queryRLimit        — changes when Z3 gives up (sxUnknown vs sat/unsat).
  ##   maxFrontierSize    — caps path exploration; changes coverage.
  ##   maxCallDepth       — caps call-stack depth; sxUnknown vs sat/unsat.
  ##   maxHeapDepth       — caps ref/ptr deref depth (R9/R10); sxUnknown vs sat.
  ##   maxLoopUnwind      — caps loop unrolling; sxUnknown vs sat/unsat.
  ##   inlinePolicy       — inline vs axiom for HOF; changes sat/unsat.
  ##   seqInlineThreshold — HOF unroll count under ipHybrid; changes sat/unsat.
  ##   defectExclusions   — which defect raises become sxRaised vs suppressed
  ##                        (runtime.nim typeIdToDefectKind + membership test);
  ##                        changes sxRaised↔suppressed. CR-2 (was missing).
  ##   arithChecks        — which arithmetic defect forks are EMITTED; an
  ##                        unchecked kind is never forked so verdicts differ.
  ##                        R16-1 (ADR-0011 F2). Rendered as `;ac=`.
  ##   maxClosureInlineCount — cap on closure descent depth; triggers
  ##                        ceInlineBudgetExceeded → sxUnknown if hit.
  ##                        CR-2 (was missing).
  ##   maxBytesEncodingLen   — cap on bytes(s) materialisation length; triggers
  ##                        seBytesLengthTooLarge → sxUnknown if exceeded.
  ##                        CR-2 (was missing).
  ##   maxFreshnessAssertions — cap on `newRef != prior` inequalities; when hit,
  ##                        dropped constraints allow Z3 to alias refs it
  ##                        otherwise could not → false-SAT direction.
  ##                        CR-2 (was missing).
  ##
  ## EXCLUDED (provably verdict-neutral):
  ##   acceptUnknownAsCovered — governs assertCoveredBy's raise/pass decision
  ##                        AFTER the walker returns; zero influence on what
  ##                        symex returns or what witness is persisted.
  ##   maxInstantiationsPerProc — self-protected: cap changes which procs are
  ##                        registered in prog.procs, which is ALREADY part of
  ##                        the program canonical key (canonicalize(prog)).
  ##                        Adding it here is harmless but unnecessary; omitted
  ##                        to avoid implying it was a cache-key hole.
  ##   maxSplitParts      — WIRED as of CR-11/CR-18: the concrete-inline split
  ##                        paths (empty-sep and both-literal) now check this
  ##                        cap and classify sxUnknown when parts.len > cap
  ##                        (if cap > 0). A settings change here changes whether
  ##                        a large-literal split yields sxSat or sxUnknown, so
  ##                        it MUST participate in the cache key (previously
  ##                        excluded because it was unwired — CR-2 audit comment
  ##                        at that time was correct; now updated).
  "St<is=" & $s.integerSemantics &
    ";rl=" & $s.budget.queryRLimit &
    ";fr=" & $s.budget.maxFrontierSize &
    ";cd=" & $s.budget.maxCallDepth &
    ";hd=" & (if s.budget.maxHeapDepth == 0: "heapDepth=unlimited"   ## Phase 15 R10
              else: $s.budget.maxHeapDepth) &
    ";lu=" & $s.budget.maxLoopUnwind &
    ";ip=" & $s.inlinePolicy &          ## Phase 15 C4: HOF inline/axiom choice
    ";sit=" & $s.budget.seqInlineThreshold &   ## Phase 15 C4: HOF unroll bound
    ";de=" & $s.defectExclusions &      ## CR-2: set[DefectKind] renders as stable
                                        ## bitmask (ordinal order); deterministic
                                        ## across runs and both backends.
    ";ac=" & $s.arithChecks &           ## R16-1: set[ArithCheck]; same ordinal-
                                        ## stable rendering as defectExclusions.
    ";mcic=" & $s.budget.maxClosureInlineCount &  ## CR-2
    ";mbel=" & $s.budget.maxBytesEncodingLen &    ## CR-2
    ";mfa=" & $s.budget.maxFreshnessAssertions &  ## CR-2
    ";msp=" & $s.budget.maxSplitParts &           ## CR-11/CR-18: now wired
    ">"

# ---- Cache key -------------------------------------------------------------

proc symexCacheKey*(prog: SymexProgram, target: SymexTarget,
                    settings: SymexSettings,
                    z3Version, nimVersion, walkerVersion,
                    renderingVersion: string): string =
  ## Content-addressed key over every input that determines a
  ## witness's validity. Stable across builds (no source locations,
  ## no map-iteration order, no compiler-specific hashes). Returns
  ## `"sx:" & <40-char SHA-1 hex>`.
  ##
  ## `walkerVersion` covers walker semantics (what the walker
  ## computes from a given IR). `renderingVersion` covers the
  ## serialisation of sat witnesses to the choice-IR. Bumping one
  ## must not silently invalidate witnesses whose semantics under
  ## the other axis are unchanged.
  let canon =
    "K|" & canonicalize(prog) &
    "|" & canonicalize(target) &
    "|" & canonicalize(settings) &
    "|z3=" & z3Version &
    "|nim=" & nimVersion &
    "|w=" & walkerVersion &
    "|r=" & renderingVersion
  "sx:" & $secureHash(canon)
