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

const renderAsChoicesVersion* = "11"
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
  ## - "6" — Cluster H Step C (ADR-0022): a bare named-ref-object PARAMETER
  ##   now classifies `itRef` (heap identity) instead of value-modelling as
  ##   `itTuple` — such a param is now `svRef` at witness-extraction time,
  ##   making it eligible for `buildHeapSnapshot`/alias-group witness
  ##   rendering (`runtime.nim:3788`, gated purely on the runtime `svRef`
  ##   kind — no new code there, but a genuinely NEW witness SHAPE reaches it:
  ##   a `heapSnapshot` entry for a param class that never produced one
  ##   before). Bump in lockstep with the walker bump (55→56).
  ## - "7" — Cluster H H_witness (ADR-0022, ADR-0010 invariant #4): the
  ##   RECURSIVE heap-snapshot witness. `buildHeapSnapshot`/`pointeeRendering`
  ##   now descend recursively into ref-typed OBJECT FIELDS and CONTAINER
  ##   (seq/array/tuple) elements — bounded by the effective heap-depth
  ##   budget, cycle-safe via a `visited` address set — replacing the flat
  ##   `"<object>"` placeholder a composite (`ref object`) pointee used to
  ##   render. `pointsTo`/`aliasRef` now populate for the WHOLE reachable
  ##   graph (one `HeapSnapshotEntry` per reachable cell, named by access
  ##   path — `p.next`, `s[0]` — not just top-level params). This is a
  ##   WITNESS-SHAPE-ONLY change (post-solve rendering of an already-decided
  ##   model): no verdict changes, so `symexWalkerVersion` does NOT bump this
  ##   cycle — contrast "6", which bumped in lockstep because a NEW SVal
  ##   kind reached the snapshot for the first time; here the same
  ##   `svRef`/`svPtr` params/cells were already eligible, only the rendered
  ##   STRING shape of a composite pointee's `pointsTo` changes.
  ## - "8" — Round-6 B4: `readSeqUInt8`'s string-backed-param fix
  ##   (`runtime.nim`). A `seq[byte]` param B1 marked `isStringBacked` models
  ##   as `svString`, so its solved value previously landed in
  ##   `RawWitness.strVals` while the generated reader glue (picked off the
  ##   DECLARED `seq[byte]` type) called `readSeqUInt8`, which only ever
  ##   read `seqLens`/`uintVals` — a representation mismatch that silently
  ##   degraded every such param's witness to an empty seq regardless of the
  ##   solved model. `readSeqUInt8` now reads `strVals` first (byte-per-char)
  ##   when present. This is a genuinely NEW/CHANGED witness CONTENT for the
  ##   affected param class (previously-empty seq -> real bytes) reaching
  ##   `renderAsChoices` via the same generated-reader path "5"'s M1 bullet
  ##   established — bump in lockstep with the walker bump (81->82) per that
  ##   precedent: no new `iek*`/`sv*` kind is introduced, but a pre-existing
  ##   reader's CONTENT for an already-reachable shape changes, the same
  ##   class of cache-unsafety "5" itself was written to close.
  ## - "9" — Round-6 B4-rider (embedded-NUL witness fix, `runtime.nim`).
  ##   `extractLeaf`'s `svString` arm switched from nim-z3's `evalStr`
  ##   (`Z3_get_lstring`-backed) to a new `evalStrBytes` helper built on
  ##   `getStringLength`/`getStringContents` (`Z3_get_string_length`/
  ##   `Z3_get_string_contents`, a separate already-bound Z3 API returning
  ##   raw codepoints). Isolated repro proved `Z3_get_lstring` itself
  ##   mis-renders any string containing a byte it treats as needing
  ##   SMT-LIB escaping (embedded NUL confirmed; also backslash, quote,
  ##   and bytes < 0x20 / >= 0x7f) — it returns the LITERAL TEXT of the
  ##   escape spelling (`\u{0}`, 5 chars) in place of the 1 real byte,
  ##   with the reported length growing to match. This is a genuinely NEW
  ##   witness CONTENT for every affected string (previously-corrupted
  ##   escape text -> real bytes) reaching `renderAsChoices` through the
  ##   same string-witness path "8"'s bullet already established as
  ##   cache-relevant — bump per that precedent. Verdicts (sxSat/sxUnsat/
  ##   sxUnknown/sxRaised) are UNCHANGED for every affected SUT — only
  ##   already-SAT witness CONTENT differs — so `symexWalkerVersion` does
  ##   NOT bump this rider.
  ## - "10" — Round-6 A6-rider (implicit-result-fallthrough call-boundary
  ##   soundness fix, `runtime.nim`'s `isCall` arm). Unlike the "8"/"9"
  ##   riders above, THIS bump is NOT extraction-only: `symexWalkerVersion`
  ##   bumps in lockstep (85→86, see below) because the fix corrects a
  ##   verdict-affecting soundness gap, not just witness rendering — the
  ##   root cause left `retSym` unconstrained at certain call sites, so a
  ##   previously-reported `sxSat` could be a FALSE POSITIVE (see the "86"
  ##   walker-version note). Bumped here anyway, per the established
  ##   lockstep-bump precedent ("4"/"6"/"8": a walker bump that changes
  ##   witness-relevant content always rotates the render version too), so a
  ##   stale cache entry keyed under "9" is never replayed as if it still
  ##   reflects the corrected extraction path.
  ## - "11" — Round-6 B7-rider (LEG 2, char-widening witness-corruption
  ##   companion bug). Same lockstep-bump precedent as "10" above:
  ##   `normalizeIntTyName` (`dsl_parser.nim`) now maps `char` to `"uint8"`
  ##   (see that proc's own doc comment for the full root-cause writeup) —
  ##   a `uint16(<charExpr>)`/similar widening conversion off a STRING
  ##   receiver's char read now genuinely zero-extends via `iekConvIntWidth`
  ##   instead of silently dropping the conversion, so an already-`sxSat`
  ##   witness for a SUT combining two such widened values (chapulin's own
  ##   opcode-dispatch shape, `uint16(s[0]) shl 8 or uint16(s[1])`) reports
  ##   the value the property ACTUALLY depends on instead of Z3's free
  ##   (don't-care) choice for the now-correctly-constrained high byte.
  ##   Bumped in lockstep with `symexWalkerVersion` (86→87, see below) — the
  ##   fix is not extraction-only, it corrects an under-constrained property
  ##   at PARSE time, a genuine verdict-class gap, not merely a rendering
  ##   change.

const symexWalkerVersion* = "118"
  ## N46-followup-4 (round-6 raise-class-audit follow-on: ref-to-multi-variant
  ## witness-rendering fix), walker v118: fixes the pre-existing, unrelated
  ## crash `tsymex_r6_heap_raise_totality.nim`'s header documented (found
  ## during the heap-raise-totality slice, v113) -- rendering a witness for a
  ## `ref`-to-multi-axis-variant PARAMETER crashed with an unhandled
  ## `KeyError` (`readUInt8`: "key not found: p.kindA") even with ZERO
  ## heap-deref/field-access involved (a bare `if p != nil: symexTarget(...)`
  ## reproduces it). Root cause: `extractFromSymVal`'s `svRef`/`svPtr`
  ## "no observed pointee" arm (`runtime.nim`) has a `case pointee.kind`
  ## covering `itInt`/`itBool`/`itFloat32`/`itFloat64`/`itTuple`/`itVariant`
  ## explicitly, falling through to a generic `else: discard` for everything
  ## else -- `itMultiVariant` landed in that `else`, so NO witness leaf was
  ## ever written for any of the pointee's sub-paths (not even the per-axis
  ## discriminators), while `emitTyAndReader`'s `itMultiVariant` arm
  ## (`symex.nim`) unconditionally reads every axis's discriminator when
  ## rendering ANY SAT witness for the param, regardless of whether the
  ## pointee was ever dereferenced (mirroring how the `itTuple`/`itVariant`
  ## arms beside it always reconstruct the full pointee). Fixed by adding an
  ## `of itMultiVariant:` arm that mirrors the `itTuple` arm's default-only
  ## treatment: materialise a proto multi-variant via `allocateSym` and
  ## extract its default leaves, so every sub-path the reader might query
  ## exists. No observed-value override is possible here (unlike the
  ## `itVariant` arm's own override step) because the walker's own heap-deref
  ## support for a ref-to-multi-variant pointee is itself still declined
  ## (`heRefVariantUnsupported`, N46-followup-2) -- `currentHeapDerefVals`
  ## never carries an entry for this shape, so a replayable default is
  ## exact, not an approximation. WITNESS-CONTENT-AFFECTING (a crash becomes
  ## a render): no verdict changes for any previously-non-crashing SUT.
  ## 117->118.
  ##
  ## N46-followup-3 (round-6 raise-class-audit category-d closure), walker
  ## v117: closes the LAST 6 category-d ("uncertain reachability") entries
  ## `tsymex_r6_n36_raise_class_audit.nim`'s N46 slice (v111) left as an
  ## honest backlog -- `rawAnyAstOf` (1), `coerceIntLit` (3), `lower`'s
  ## `iekField` final `else` (1), `storeSeqElem`'s val-kind mismatch (1), all
  ## `runtime.nim`. Per-site adjudication:
  ##
  ## 1. `rawAnyAstOf`'s `else` (composite `SymVal` kinds -- svSeq/svArray/
  ##    svTuple/svVariant/svMultiVariant/svClosure/svUninterpRef -- with no
  ##    single-leaf Z3 sort): CONFIRMED LIVE by a direct container probe --
  ##    an ordinary `type SeqId = distinct seq[int]` PARAMETER (zero heap/ref
  ##    involvement) reaches `allocDistinctSym`'s composite-base branch
  ##    (`baseIsDecidable` is false for `itSeq`), which calls
  ##    `rawAnyAstOf(baseRep)` on the `svSeq` base representative to derive
  ##    its Z3 sort for the (bijectivity-skipped) inject/eject func-decls --
  ##    pre-fix, `symexFind` on the probe crashed the whole run to
  ##    `weInternalWalkerFault` (`ValueError: rawAnyAstOf: unsupported
  ##    distinct base kind svSeq`) instead of the honest per-path `sxUnknown`
  ##    this class of gap should report. Folded into the SAME `allocDegrade`
  ##    arm `svTable`/`svSet` (N41) already use -- identical "compound value,
  ##    no single-leaf sort" shape, just reached from a different caller
  ##    (`allocDistinctSym` rather than `sortOfTuple`/`heapValueSort`).
  ##    VERDICT-AFFECTING: a `distinct <composite>` value (param, field, or
  ##    return) previously masked EVERY path in the run behind a whole-run
  ##    `weInternalWalkerFault`; now only the path(s) actually touching it
  ##    degrade to `sxUnknown`, and unrelated sibling paths (e.g. an
  ##    unconditional target on a hazard-free branch) resolve correctly.
  ##
  ## 2. `coerceIntLit`'s three non-numeric `proto.kind` arms (svUninterpRef,
  ##    svBool, the composite list): RECLASSIFIED category-c, not converted.
  ##    `symexFind`/`symexFindAllWitnesses` declare their SUT parameter
  ##    `fn: typed` -- Nim fully sem-checks the procedure BEFORE the macro
  ##    body runs, so this DSL only ever classifies an ALREADY TYPE-CHECKED
  ##    AST. Every one of `coerceIntLit`'s 4 call sites supplies a `proto`
  ##    that is the SymVal of whatever Nim expression sits in the SAME
  ##    static position as the integer literal being shaped -- for Nim to
  ##    have accepted that program, the position's type must implicitly
  ##    unify with a bare int literal, which Nim's own conversion rules
  ##    restrict to {int8..int64, uint8..uint64, float32, float64} (floats
  ##    never reach this proc -- they route to `iekFloatLit`) plus a
  ##    `distinct` type whose base resolves through that same family. `bool`,
  ##    any composite, and an uninterpreted-ref value are excluded by the
  ##    compiler pass that runs before this DSL ever sees the AST -- not
  ##    "unobserved", structurally impossible. Full argument on
  ##    `coerceIntLit`'s own doc comment.
  ##
  ## 3. `lower`'s `iekField` final `else` (`recv.kind` outside svTuple/
  ##    svVariant/svMultiVariant) and `storeSeqElem`'s itRef/itPtr val-kind
  ##    mismatch: CONVERTED, defense-in-depth, no independently constructed
  ##    repro for either (matching the precedent N46-followup-2 already set
  ##    for its own four unreproduced `refSV.kind`-mismatch conversions,
  ##    v113). Both sites' STATIC-TYPE argument for unreachability was traced
  ##    and holds (the parser only ever emits `iekField` for a tuple/variant/
  ##    multi-variant-classified receiver; every traced producer of a ref/ptr
  ##    seq element -- env lookup, `allocateSym`'s itRef/itPtr arm, and
  ##    `applyClosureGround`'s N46-hardened `allocateSym` fallback -- is
  ##    kind-consistent by construction) but neither closes off a
  ##    walk-time-only `iteSV`-merge-of-a-degraded-placeholder divergence
  ##    from a variable's STATIC kind, the exact mechanism left open for
  ##    N46-followup-2's own four sites. In-band degrade either way costs
  ##    nothing if truly dead and closes the hazard if not.
  ##
  ## Zero pattern-(B) `runtime.nim` markers remain `category-d`: 78 -> 75
  ## marked (rawAnyAstOf/iekField/storeSeqElem no longer raw raises, not
  ## re-marked), all 75 now `category-c`. 116->117.
  ##
  ## A1 adjudication slice (round-2 seed: S3_strindex/S10b_strconv/A1_bitwise
  ## first-principles review), walker v116, three independent engine fixes:
  ##
  ## 1. S3 `.high` on a string (`dsl_parser.nim`'s `nnkCall` arm): round-6's
  ##    A0 `low(T)`/`high(T)` type-magic fold intercepted ANY `high`/`low`
  ##    call with 2 args, including a VALUE argument (`s.high` desugars to
  ##    `high(s)`) — `typeNodeName(n[1])` on a value symbol returns the
  ##    VARIABLE's name, which is trivially "non-int-family", so A0 always
  ##    `return`ed a classified decline before the S3-specific `.high`
  ##    lowering (`len(s)-1` via `iekStrLen`) further down the same proc
  ##    could ever run — permanent dead code. Carved out exactly the shape
  ##    S3 already models (string receiver, `high`) via a `classifyType`
  ##    check on the ARGUMENT (not the callee), leaving A0's original
  ##    fault-prevention scope (type arguments, and every other value type)
  ##    untouched. VERDICT-AFFECTING: a genuinely-provable `sxSat` was
  ##    reporting `sxUnknown` then crashing (`FieldDefect` on `.witness`).
  ##
  ## 2. S10b `parseFloat` classification (`runtime.nim`'s `degradeStrArm`):
  ##    `iekStrUnsupported`'s degrade placeholder was unconditionally
  ##    `svString` — correct for its string-shaped callers (toOct/toHex/
  ##    $float/case-fold-miss/mutation) but wrong for `parseFloat`, whose
  ##    successful path is a `float`. The mismatch was silent until a
  ##    downstream op touched the placeholder: `parseFloat(s) == 1.5`
  ##    compared the fabricated svString against an svFloat64 RHS, crashing
  ##    inside `cmpString` and escaping to the whole-run catch-all as
  ##    `weInternalWalkerFault` — masking the classified
  ##    `seUnsupportedStringOp` already recorded two lines earlier in the
  ##    same proc. Keyed the placeholder's type on `e.strOp` so `parseFloat`
  ##    gets a float-typed placeholder; every other caller unaffected.
  ##    VERDICT-AFFECTING (error classification): `sxUnknown` now carries
  ##    the intended classified kind instead of an internal-fault kind.
  ##
  ## 3. A1 cell 6 same-width int reinterpret (`iekConvIntReinterpret`, new
  ##    IR kind — `types.nim`/`dsl_parser.nim`/`runtime.nim`): round-6 B2
  ##    recorded `uint32(x)`-from-`int32`-style same-width signedness
  ##    reinterprets as a classified decline ("no reinterpret primitive is
  ##    modeled"), but this was mis-scoped — B2's actual soundness finding
  ##    was that the pre-B2 identity pass-through left a STALE `signed` flag
  ##    on the result, not that the conversion was unrepresentable. Every
  ##    fixed-width Nim int already allocates as an svBV* whose raw Z3 bit
  ##    pattern is signedness-agnostic (only the `signed` tag steers which
  ##    downstream comparison/shift-right variant a later op picks), so a
  ##    same-width reinterpret needs no new Z3 primitive — just a `signed`
  ##    tag correction on the SAME bits, sound for every input (not just the
  ##    cell that found the gap). This was occluding the chronos-faithful
  ##    `slotIndex(pos, cap) = pos and capMask(cap)` twin cell's genuinely
  ##    provable `sxUnsat` (`capMaskD2`'s `uint(cap - 1)`) — reported
  ##    `sxUnknown` instead. `tsymex_r6_b2_intwidth.nim`'s former B2-10
  ##    decline pin retired and replaced with a SAT + soundness-UNSAT proof
  ##    pair (B2-14/B2-15). VERDICT-AFFECTING (the whole reason for the
  ##    bump): a genuinely-provable `sxUnsat` cell reported `sxUnknown`.
  ##
  ## renderAsChoicesVersion unchanged: none of the three fixes change any
  ## already-SAT witness's rendered shape/content (fix 1 adds a new provable
  ## SAT witness on a previously-unreachable-verdict path; fix 2 only
  ## changes an sxUnknown's error CLASSIFICATION, never a witness; fix 3
  ## only affects sxUnsat/sxUnknown-vs-sxUnsat verdicts, never a rendered
  ## witness).
  ##
  ## Round-6 re-review closing slice (iteSV merge-degrade follow-ups),
  ## walker v115:
  ##
  ## Item 1 (re-opened): the v114 entry below claims `svSeq`'s genuine-
  ## (non-placeholder-)merge branch was included in that round's fix — it
  ## was not. `iteSV`'s `svSeq` arm still fell through a shared `t` after
  ## `allocDegrade(...)` for a genuine element merge, the exact collapsed-
  ## concrete-value class v114 closed for every OTHER composite kind. Now
  ## genuinely fixed with the same idiom (`allocateSym(tyOf(t), ...)`);
  ## `tyOf` is faithful for `svSeq` (`tSeq(sv.seqElemTy)` round-trips the
  ## stored elemTy field directly, unlike `svVariant`/`svMultiVariant`'s
  ## live-value reconstruction — see item 2). VERDICT-AFFECTING for the
  ## same reason as v114's fix: a symbolic-index ite-fold over an array of
  ## seq-typed elements could otherwise collapse to the last element,
  ## independent of the index.
  ##
  ## Item 2: `tyOf`'s `svVariant`/`svMultiVariant` arms rebuild the
  ## placeholder `IRType` from the live SymVal but omitted the PLAIN
  ## (shared, always-present) field names/types — even though the SymVal
  ## fully carries them (`vPlainFields`/`vPlainFieldNames`). A degrade-
  ## placeholder allocated from the resulting empty-plain-fields type then
  ## made a later ordinary plain-field read (`iekField`) fall through to a
  ## `raise ValueError` blaming a nonexistent parser bug (caught at top
  ## level as `sxUnknown`, but with a misleading diagnostic). Fixed by
  ## threading `vPlainFields`/`vPlainFieldNames` (and the multi-variant
  ## equivalents) through to `tVariant`/`mkMultiVariant`. Per-arm tag names
  ## and the disc's full ordinal domain remain unrecoverable (never stored
  ## on `SymVal`) but are confirmed inert for `allocateSym`'s own
  ## round-trip. VERDICT-AFFECTING: closes a false-raise path that could
  ## previously fire on an ordinary plain-field read of a merge-degraded
  ## variant.
  ##
  ## Item 3: uniquified `iteSV`'s `__iteSVMergeDegrade`/
  ## `__iteSVUninterpDegrade` fresh-const names (Z3 interns by
  ## `(name, sort)`, so two distinct merge occurrences of the same kind
  ## previously shared one symbol) and `eqBV`/`neBV`'s `__eqBVDegrade`/
  ## `__neBVDegrade` for the same reason, via the established
  ## `currentBorrowReboxCounter`/`currentExnRefCounter` per-run-counter
  ## idiom. Extraction-only (no verdict class changes — a degraded run's
  ## fresh placeholder was always untrusted; this only rules out one fresh
  ## placeholder accidentally aliasing another's Z3 symbol).
  ##
  ## Round-6 re-review (items 1-2), walker v114:
  ##
  ## Item 1 (the priority, #High): `iteSV`'s composite-merge arms
  ## (`svString`/`svTable`/`svSet`/`svVariant`/`svMultiVariant`/
  ## `svUninterpRef`, plus `svSeq`'s genuine-non-placeholder branch) used to
  ## `allocDegrade(...); t` -- returning ONE OPERAND'S CONCRETE VALUE
  ## unconditionally, ignoring both `cond` and the accumulator `e`, so the
  ## symbolic-index ite-fold (`res = arrElems[0]; for k: res = iteSV(cond_k,
  ## arrElems[k], res)`) always collapsed to the LAST array element
  ## regardless of the index. VERIFIED (adversarial container probes, see
  ## `iteSV`'s own doc comment for the full writeup): the expression-level
  ## `iekIndex` call site is dead code (the parser never emits it for
  ## `arr[i]` -- always A-normalises to the `isIndex` statement); the one
  ## live route (`isIndex`) reached `isTargetLabel` with `uncertain == true`
  ## in every constructed probe, so today's collapse is sound in practice
  ## but only via a caller-shape coincidence (a leaked, undrained
  ## `loweringDidDegrade` threadvar racing whatever `lower()`/
  ## `lowerBoolInExpr` call happens to run next on the SAME path), not by
  ## construction. Fixed regardless: the group arm now returns a genuinely
  ## FRESH, unconstrained placeholder of the operand's own kind
  ## (`allocateSym(tyOf(t), ...)`, the `eqBV`/`neBV` idiom); `svUninterpRef`
  ## returns a fresh same-sort const (mirrors the `svRef`/`svPtr` arm,
  ## since `allocateSym`'s `itUninterp` arm hard-raises for a genuine
  ## cluster-E sort name); `svClosure` is left unchanged (a closure's
  ## `closureSite` is not a Z3-modelled value at all, so no fresh
  ## placeholder can be expressed) but is confirmed unreachable from either
  ## live fold today (there is no `itClosure` IRType, so neither an
  ## `array[N, T]` element type nor a variant arm-field type can BE a
  ## closure). VERDICT-AFFECTING: closes a soundness gap that depended on a
  ## coincidence rather than a guarantee -- a future batched-multi-path
  ## caller (e.g. a HOF/closure fold merging several call-return paths)
  ## could otherwise have lost that race and let a collapsed value size a
  ## verdict.
  ##
  ## Item 2: `defaultZero`'s `itSeq` placeholder arm claimed to mirror
  ## `allocateSym`'s `itSeq` placeholder arm EXACTLY but omitted
  ## `seqUnsupportedFieldReason`/`seqUnsupportedFieldKind`; now threads both,
  ## closing a latent (no live SUT yet exercised a read through a
  ## `defaultZero`-sourced placeholder) mismatch. 113->114.
  ##
  ## N46-followup-2 (round-6 re-review, heap-raise totality slice), walker
  ## v113: closes the `runtime_heap.nim` LEDGERED-LIVE backlog N46 (v111)
  ## opened when it widened the raw-raise-in-lower CLASS audit's file
  ## coverage to this file for the first time and found 13 unmarked
  ## `raise (ref Symex*)` sites in the heap-deref/ref-variant-field
  ## machinery, deliberately left unconverted pending dedicated scoping.
  ## This slice adjudicates all 13:
  ##   - 7 CONVERTED to the in-band degrade idiom (`allocDegrade` +
  ##     `forkPathTainted`/a fresh `allocateSym` placeholder, matching the
  ##     established `seqElemAt`/`isUnsupported` idioms): `liftHeapValue`'s
  ##     unsupported-pointee-kind `else` (string/table/set/distinct read
  ##     values), the `itMultiVariant` field-deref/field-write declines (an
  ##     INLINE `ref`/`ptr`-to-multi-variant parameter — the classifier
  ##     wraps such a pointee in `itRef`/`itPtr` unchanged; only the
  ##     NAMED-alias and field-typed-ref paths exempt variant pointees from
  ##     heap routing, ADR-0022 sub-decision #1), and the four
  ##     `refSV.kind`-not-`svRef`/`svPtr` mismatches (general + arm-field,
  ##     read + write). CONFIRMED live by a dedicated RED/GREEN probe: a
  ##     `ref`-to-`string`-field SUT with the hazard on one branch and an
  ##     unconditional target on a SIBLING, hazard-free branch reported a
  ##     false `sxUnknown` pre-fix (the raw raise unwound through
  ##     `walkHeapArm`/`walk`/`walkBlock` to `runSymexImpl`'s top-level
  ##     catch, a WHOLE-RUN abort masking the sibling's true `sxSat`) and
  ##     the correct `sxSat` post-fix — the N31/ADR-0023 SND-3 silent-loss
  ##     class, same mechanism, newly found in this file.
  ##   - 6 RECLASSIFIED to `verified-unreachable` (left as raw raises, now
  ##     marked): the two "arm declared by no arm of the variant" sites
  ##     (`dField`/`dwField` are parser-resolved against the SUT's own real
  ##     field names before the scan runs; an undeclared field reference
  ##     does not compile), the two "else-only variant, no non-else arm"
  ##     sites (Nim's `case` syntax requires >= 1 `of` branch before an
  ##     optional `else`), and the two disc-kind `else` arms in `discEq`/
  ##     `discEqW` (`VariantAxis.vDiscTy` is always `itInt` by construction,
  ##     `types.nim`, and `liftHeapValue`'s `itInt` arm is width-exhaustive,
  ##     so a disc `SymVal` read through `heapSelect` can only ever be
  ##     `svBV8`/`16`/`32`/`64`).
  ## VERDICT-AFFECTING: the 7 conversions change a WHOLE-RUN abort (a
  ## `sxUnknown`/crash that could mask an unrelated sibling path) into a
  ## per-path/per-statement degrade (an honest `sxUnknown` ONLY when no
  ## other path succeeds) — a strictly MORE complete (never less sound)
  ## verdict for any SUT that reaches one of these sites alongside an
  ## independently-reachable target. 112->113.
  ##
  ## N46-followup (round-6 re-review), walker v112: R1's placeholder-decline
  ## discipline is extended to the equality/comparison machinery N46 (v111,
  ## below) converted to in-band degrades. N46's conversion of `eqBV`/`neBV`/
  ## `cmpBV`/`svLeafEq`/`iteSV`'s catch-all raw-raise sites to `allocDegrade`
  ## was correct on its own SND-3/ADR-0023 terms, but it treated an
  ## `isUnsupportedFieldPlaceholder`-flagged `svSeq` operand identically to a
  ## genuinely-unsupported (non-placeholder) kind — a generic
  ## `feUnsupportedOp`/"non-BV SymVal" degrade rather than the classified
  ## `seNestedSeqUnsupported` decline every OTHER placeholder access
  ## (S1/N1/iekSeqAdd) already gives. Root-caused via `R1-eq`
  ## (`tsymex_r6_r1_placeholder_totality.nim`), which regressed from
  ## `sxUnknown` to `sxRaised` at v111: the regression was NOT a soundness
  ## hole in the degrade itself (the fresh unconstrained bool it returns
  ## correctly taints the path `uncertain`, and the tainted path correctly
  ## never reports a false `sxSat`) — it was that a WHOLE-RUN-aborting raw
  ## raise (pre-v111) had been silently masking an unrelated, genuinely
  ## reachable `OverflowDefect` in the test SUT's own `n + 1` helper
  ## arithmetic. Once eqBV stopped raising (v111), the walk no longer
  ## aborted, so that pre-existing latent defect surfaced and WON the
  ## verdict over the (correctly) undecided target reachability — per E6,
  ## a reachable Defect always surfaces regardless of search target, and
  ## nothing at the comparison-guard level can suppress a defect finding
  ## recorded by an earlier, unrelated statement. Fixed at both ends: (1)
  ## `eqBV`/`neBV`/`cmpBV`/`svLeafEq`/`iteSV`'s `svSeq` arms now GUARD-BEFORE
  ## (B7r2 precedent) — an `isUnsupportedFieldPlaceholder` operand routes
  ## through `declinePlaceholderInLower`/`placeholderReadDeclineMsg` for a
  ## classified `seNestedSeqUnsupported` decline, matching S1/N1's own
  ## message quality, BEFORE ever reaching the generic non-placeholder
  ## catch-all; (2) the test SUT's own accidental, test-irrelevant integer
  ## overflow was closed by bounding its `n` parameter to `range[0 .. 1000]`
  ## (mirroring this same file's own `sutUntouchedUnsat` precedent), so the
  ## test again exercises ONLY the placeholder-equality decline it names.
  ## `refEq`/`retBindEq`/`lowerCmp`'s bool-ordering arm were audited for the
  ## same hazard and found NOT applicable: `isUnsupportedFieldPlaceholder`
  ## is an `svSeq`-only field (never set on `svRef`/`svPtr`/`svBool`), and
  ## `retBindEq`'s `svSeq` arm already carried the placeholder guard before
  ## this slice. VERDICT-AFFECTING (message/classification only for the
  ## guarded sites — no new false sat/unsat; the taint/soundness properties
  ## `allocDegrade` already provides are unchanged). 111->112.
  ##
  ## N46 (round-6 re-review), walker v111: the raw-raise-in-lower CLASS audit
  ## (`tests/tsymex_r6_n36_raise_class_audit.nim`) was widened to also scan
  ## for bare `raise newException(<AnyExceptionType>, ...)` (not just `raise
  ## (ref Symex*)`) across `runtime.nim`/`runtime_strings.nim`/
  ## `runtime_heap.nim` (the last of which the audit never scanned at all
  ## before this slice). Of the 81 bare `raise newException(` sites the
  ## widened scan found, 15 were confirmed category-(a) LIVE hazards
  ## (walk-reachable from a plausible user SUT shape, no local catch) and
  ## converted to the in-band degrade idiom this slice:
  ##   - `iteSV` (3): the `svUninterpRef`/composite (`svString`/`svSeq`/
  ##     `svTable`/`svSet`/`svVariant`/`svMultiVariant`)/`svClosure` merge
  ##     arms -- reached via the symbolic array-index ite-fold
  ##     (`isIndex`/`iekIndex`) over an `array[N, T]` of one of these element
  ##     kinds. One operand now stands in as the degraded value.
  ##   - `cmpBV`/`eqBV`/`neBV` (3): the non-BV-kind else arms, reached
  ##     unguarded from `lowerCmp`'s catch-all dispatch for any operand kind
  ##     not already peeled off (ordinary Nim structural `==`/`!=`/`<` on
  ##     tuples/objects/seqs). A fresh unconstrained bool stands in.
  ##   - `refEq` (1): the ordering-op (`</<=/>/>=`) mismatch arm on ref/ptr
  ##     operands.
  ##   - `lowerCmp`'s bool-ordering else (1): `flag1 < flag2` (Nim defines
  ##     bool ordering).
  ##   - `svLeafEq` (1): a composite (seq/table/set/variant/ref/etc.)
  ##     closure-environment field reached via `closureEq`'s structural
  ##     comparison.
  ##   - `retBindEq` (2): a genuine (non-placeholder) `svSeq` return, and the
  ##     final composite-kind else (array/table/set/multi-variant/ref/ptr/
  ##     distinct return types) -- both now bind `mkBool(true)` (a sound
  ##     vacuous binding), mirroring the SAME placeholder idiom the
  ##     `isUnsupportedFieldPlaceholder` branch immediately above already
  ##     uses.
  ##   - `iekTableSet` (1): an unsupported `Table[string, V]` value type on
  ##     write -- returns the receiver unchanged (inert no-op write).
  ##   - `iekSeqDel`/`iekSeqInsert`/`iekSeqPop` (1 combined arm): zero prior
  ##     implementation -- now lowers and returns the receiver unchanged.
  ##   - `iekContains` (1): the final else (`x in mySeq`/`myArray`/`myString`)
  ##     -- mirrors the `svSet` arm's own degrade idiom two cases above.
  ##   - `iekBorrowOp` (1): an unsupported `{.borrow.}` base operator (e.g.
  ##     bitwise ops on a `distinct int`) -- returns the ejected base value
  ##     unchanged.
  ##   - `seqElemAt` (1): a genuine read-side/write-side asymmetry --
  ##     `storeSeqElem` (the write side) handles `itRef`/`itPtr` elements,
  ##     `seqElemAt` (the read side) did not, even though `isBackedSeqElemTy`
  ##     (the shared guard both sides' callers use) considers them backed.
  ##     Degrades to a fresh placeholder of the receiver's own element type
  ##     pending a proper read-side implementation.
  ##   - `applyClosureGround`'s unguarded `defaultZero` fallback call (not a
  ##     `raise newException(` site itself, but the ONE of `defaultZero`'s
  ##     four call sites that did not wrap it in try/except, reachable for a
  ##     closure/HOF lambda returning an unsupported composite type):
  ##     replaced the `defaultZero` call with `allocateSym`, proven TOTAL
  ##     (never raises) for any classifiable type since N40 -- no try/except
  ##     needed at all.
  ## Every remaining bare `raise newException(` site is tagged
  ## `category-c: <reason>` (documented/provable invariant) or `category-d:
  ## <reason>` (uncertain, LEDGERED) in the audit file itself -- see that
  ## file's own doc comment for the full breakdown (75 category-c, 6
  ## category-d). Separately, widening the audit's FILE COVERAGE to include
  ## `runtime_heap.nim` (never scanned before this slice, despite being
  ## `include`d into `runtime.nim` and walk-reachable via `walkHeapArm`)
  ## surfaced 13 pre-existing, unmarked `raise (ref Symex...)` sites in its
  ## heap-deref/ref-variant-field machinery -- marked `LEDGERED-LIVE`
  ## (plausibly live, NOT converted this slice; a careful conversion needs
  ## its own dedicated scoping) rather than forced through a rushed
  ## conversion. VERDICT-AFFECTING: the 15 conversions above change which
  ## paths degrade to `sxUnknown` (with a classified `SymexErrorInfo`)
  ## instead of the walk silently losing the raise and computing a verdict
  ## from a corrupted exploration (the ADR-0023/SND-3 hazard class) -- for
  ## SUT shapes that reach one of these 15 sites, a previously-possible false
  ## `sxUnsat`/`sxSat` now correctly reports `sxUnknown`. 110->111.
  ##
  ## Round-6 re-test round (diagnosis follow-up to N47), walker v110:
  ## N47 (v109, below) converted `iekSeqAdd`'s two raw raises into in-band
  ## `allocateSym`-based degrades, but the degraded receiver REBOUND `data`
  ## to a placeholder that was indistinguishable, downstream, from a
  ## genuinely-unbacked-element-type placeholder (e.g. `seq[(string,string)]`)
  ## -- a BENIGN read of the SAME receiver after the degrade (`data.len`,
  ## `data[0]`) fell into the R1 chokepoint (`iekSeqLen`/`isIndex`) and
  ## fabricated a NEW, misclassified `seNestedSeqUnsupported` ("nested seq
  ## element type is not supported") error, even though the receiver's
  ## element type IS backed in general -- only THIS ONE mutation's
  ## implementation declined. The cascade could bury (or, across multiple
  ## explored paths, outright displace) the original, honestly-classified
  ## `weInternalWalkerFault` width/elem/kind-mismatch decline.
  ##
  ## Fix: `tUnsupportedFieldSeq` (types.nim) now threads a `kind:
  ## SymexErrorKind` alongside its existing `reason` string (default
  ## `seNestedSeqUnsupported`, unchanged for every pre-existing
  ## declared-field-type-gap caller); `iekSeqAdd`'s three placeholder sites
  ## (kind-mismatch, unsupported-width, unsupported-elem) pass
  ## `weInternalWalkerFault` explicitly. Both are mirrored onto the runtime
  ## `SymVal` (`seqUnsupportedFieldReason`/`seqUnsupportedFieldKind`,
  ## runtime.nim) so `placeholderReadDeclineMsg`/`declinePlaceholderInLower`
  ## and `isIndex`'s walk-time arm can report the ORIGINAL decline's own
  ## reason and kind for a downstream read, instead of fabricating the
  ## generic (and here FALSE) nested-seq-unsupported claim. A bare-value
  ## placeholder (no `tUnsupportedFieldSeq` reason to carry) is completely
  ## unaffected -- it still reports the legacy generic message/kind.
  ##
  ## VERDICT-AFFECTING: a downstream read of an `iekSeqAdd`-degraded
  ## receiver now surfaces `weInternalWalkerFault` (referencing the add
  ## decline) instead of a fabricated `seNestedSeqUnsupported`; the
  ## drain-time message dedup (`loweringDegradeErrors`) also collapses
  ## repeated downstream reads of the same tainted receiver across the
  ## explored paths into far fewer distinct entries. 109->110.
  ##
  ## Round-6 re-test round, N47 (walker v109): two `iekSeqAdd` value
  ## declines (unsupported width, unsupported elem kind -- `runtime.nim`)
  ## converted from raw `raise newException(ValueError, ...)` to N36's
  ## in-band `allocateSym`-based degrade idiom -- these two raw raises sat
  ## OUTSIDE N36's (walker v101) own audit tool scope (it greps only for
  ## `raise (ref Symex*)`, never a bare `ValueError`), but shared the EXACT
  ## SAME C-backend goto-exception hazard (ADR-0023/SND-3) that audit closed
  ## elsewhere: an unrelated try/except N36 added inside the SAME
  ## recursively-invoked `walk` proc (`isVariantReassign`'s `defaultZero`
  ## guard) was, by itself, sufficient to flip the `iekSeqAdd` width raise
  ## from benign to LIVE -- confirmed by bisecting `tsymex_r6_r4_collector_
  ## scoping.nim`'s R4-W2b pin to c50b50f (N36) and then, empirically,
  ## by reverting each of N36's runtime.nim hunks one at a time on top of
  ## HEAD until isolating that exact hunk as sufficient to restore the pin
  ## green with NO OTHER change. Pre-fix, R4-W2b's two-hop var-aliased-
  ## mutation shape silently lost the width decline and fell back to
  ## exhausting the enclosing scan loop's k-unroll budget (`beBudgetExhausted`)
  ## instead -- same `sxUnknown` status, but the SPECIFIC classified decline
  ## proving the receiver stayed array-modeled (not string-backed) never
  ## fired. VERDICT-AFFECTING: a `.add` mutation of a non-width-64 int (or
  ## other unsupported elem kind) seq reached from inside a nested
  ## `walkBlock` frame now reliably reaches the classified
  ## `weInternalWalkerFault` decline instead of nondeterministically
  ## falling back to a budget-exhaustion decline (or, in principle, being
  ## lost entirely on a deeper nesting shape). 108->109.
  ##
  ## Round-6 re-test round, N48 (same v109 -- no further bump): closes the
  ## matching `allocateSym` itTable value-type gap N43-H2 pinned as a
  ## KNOWN-DISPARITY -- the `of itInt:` arm (runtime.nim ~2210)
  ## unconditionally `doAssert`ed `width == 64 and signed`, a live
  ## AssertionDefect escape from N40's (walker v104) `allocDegrade`
  ## totality chokepoint for a `Table[string, int32]` (or any other
  ## non-canonical-width/unsigned int) value type, caught only generically
  ## as `weInternalWalkerFault` instead of the classified
  ## `seUnsupportedTableValType` `unallocatableFieldIssue` already promised
  ## for that exact shape. Folded the width/signedness check into the
  ## `itInt` guard itself (mirroring the key-type and `itSet` arms, which
  ## already combine kind+shape into one condition) so every unsupported
  ## table value type reaches the SAME `allocDegrade` idiom. Sibling audit
  ## of the same arm family (itTable key dispatch, itSet elem dispatch)
  ## found no other surviving `doAssert`/raw-raise on a type property the
  ## predicate flags -- both already combine their guard correctly. Two
  ## other raw raises nearby (`itUninterp`'s cluster-E sentinel,
  ## `itMultiVariant`'s disc-kind sentinel) are genuine walker-invariant
  ## Defect-class checks, not unmodeled SUT constructs, and are already
  ## documented as deliberately out of the raw-raise-in-lower class's scope.
  ## VERDICT-AFFECTING: a `Table[string, V]`-typed field/param with `V` an
  ## unsupported (non-int64) numeric width now reaches the classified
  ## `seUnsupportedTableValType` decline instead of the generic
  ## `weInternalWalkerFault` catch-all.
  ##
  ## Round-6 lows slice (fix round 10, walker v108): four Low-severity
  ## decline-quality findings. N15: a field-sourced placeholder consumed
  ## through INDEXING (or the call-form slice) built a real `isIndex`/
  ## `mkSeqSlice` walk-time node over the fake empty-seq stand-in
  ## `declineUnsupportedFieldRead` already returned, crashing
  ## `lowerLeafInExpr`'s side-effect-free-container assertion
  ## (`weInternalWalkerFault`) instead of the `seNestedSeqUnsupported` kind
  ## every other placeholder-consuming form (`.len`) reports; `dsl_parser.nim`
  ## now detects the receiver's already-recorded decline and stops before
  ## building that node. N30: `symValFromRawAst` (`runtime.nim`) had no
  ## `itString` arm for a closure RETURN type, raising an untagged
  ## `ValueError` that escaped `applyClosureGround` uncaught
  ## (`weInternalWalkerFault`); now caught and classified (`feUnsupportedOp`,
  ## matching N16's own decline style), falling back to
  ## `defaultZero(cb.retTy, ...)`. N41: `rawAnyAstOf` (`runtime.nim`) had no
  ## `svTable`/`svSet` arms — a compound value has no single-leaf Z3 sort, so
  ## `sortOfTuple` (lambda param/return sort derivation) and `heapValueSort`
  ## (`runtime_heap.nim`, heap-deref value-sort derivation) both crashed
  ## uncaught to the top-level catch-all, a WHOLE-RUN `weInternalWalkerFault`
  ## masking the itTable/itSet family (N40's own family 4/5 finding,
  ## `tsymex_r6_n40_alloc_totality.nim`, flagged this status-only); now calls
  ## `allocDegrade` (N40's own chokepoint, new kind
  ## `seUnsupportedCompoundSortLeaf`) and returns a safe BV64-zero filler ast
  ## instead of raising — the N42 taint drain (walker v105) already routes
  ## this same chokepoint's taint into per-path `uncertain`, so unmasking the
  ## specific kind never lets a tainted path report `sxSat` (soundness
  ## pinned alongside the kind change, `tests/tsymex_r6_lows_declines.nim`).
  ## N12 is message-rendering only (no IR-vocabulary leak in user-facing
  ## decline text) — no walker-behavior change, but bumped in lockstep since
  ## this is one combined slice. Verdict-affecting for N15/N30/N41 (a
  ## previously-crashing shape now reports its correct classified decline
  ## kind instead of the generic internal-fault one). 107->108.
  ## Round-6 lows slice (fix round 9, walker v107): N34/N38, a shared
  ## lone-statement mis-parse in `parseStmtInner`'s block arm
  ## (`dsl_parser.nim`). The combined `nnkStmtList, nnkStmtListExpr,
  ## nnkBlockStmt` arm assumed a block's body node was always
  ## `nnkStmtList`-shaped and iterated its CHILDREN; the typed AST does not
  ## always wrap a single-statement block body that way, so a lone
  ## statement's own children (e.g. an `nnkAsgn`'s LHS/RHS) were walked as
  ## bogus sibling top-level statements, each landing the
  ## unrecognised-node-kind catch-all (`mkUnsupported`) -- a consistent
  ## mis-parse/decline to a spurious, unclassified `sxUnknown` for every
  ## one-statement `block:` body (N34), including a block-wrapped
  ## case-object discriminator reassignment on a fully-backed arm (N38).
  ## Fixed by itemizing block/stmt-list bodies through a shared
  ## `stmtListItems` helper. Verdict-affecting: a single-statement `block:`
  ## body now gets its genuine sxSat/sxUnsat verdict instead of an
  ## unclassified decline. 106->107.
  ## Round-6 lows slice (fix round 8, walker v106) carries it forward again,
  ## 105->106: five Low-severity review findings in the collector/recognizer
  ## family, `dsl_parser.nim` (plus one `runtime.nim` companion). N11: the
  ## cross-proc collector CYCLE GUARDS (`collectStringBackedByteSeqParamsImpl`/
  ## `collectIntOffsetParamsImpl`'s `visiting` parameter) were keyed by BARE
  ## PROC NAME even though the collectors themselves were already migrated to
  ## symbol identity in R4 -- two overloads sharing a name collided on one
  ## shared guard entry, silently under-classifying (degrade-only, never
  ## unsound) whichever overload's call the guard skipped. N17:
  ## `collectIntOffsetLiteralLocals` gained the one-level call-boundary trace
  ## its param sibling already had -- a literal-seeded local passed as an
  ## argument to a callee whose own formal is offset-traced now gets marked
  ## too, closing a missed-svInt-promotion gap one call hop further out than
  ## the collector previously reached. N23: `collectIntOffsetParamsImpl`'s
  ## own `walkCalls` resolved callees via raw `getImpl` + an inline
  ## `symKind in {nskProc, nskFunc}` gate -- the exact pre-N2 pattern the
  ## permanent N2 audit bans -- now routed through the shared audited
  ## `resolveRoutineImpl` core, like every other post-R4 call-boundary trace
  ## in this file. N25: `scanShapeReceiverMutated`'s mutation-veto matched a
  ## var-mode call argument by bare `strVal` instead of true symbol identity
  ## -- a nested-scope shadow sharing the real formal's name could wrongly
  ## veto that formal's string-backed classification (false-positive-only:
  ## an over-cautious decline that falls back to the pre-existing sound
  ## k-unroll path, never a wrong verdict) -- now `sameSym`-based, consuming
  ## the formal's own `nnkSym` node instead of its printed name. N3
  ## (defensive hardening, no live repro): `retBindEq` (`runtime.nim`) gained
  ## a `reconcileInt` bridge at its own top, mirroring `lowerArith`/
  ## `lowerCmp`'s established idiom (its tuple/variant arms already did this
  ## per-field), and its bare kind-mismatch `doAssert` was converted to a
  ## classified `raise newException(ValueError, ...)` decline consistent with
  ## its neighboring arms -- proven unreachable in valid Nim today (the
  ## scan-offset counter feeding a bare-scalar return is always int-typed and
  ## the collectors that trace it never introduce a representation mismatch
  ## on their own), added purely for symmetry and future-proofing.
  ## VERDICT-AFFECTING for N11/N17/N25 (classification changes can flip a
  ## missed `sxUnknown` degrade to a genuine closed-form proof); N23/N3 are
  ## hardening only, no observable behavior change for any currently-valid
  ## Nim program.
  ##
  ## N42 (round-6 fix round 7, walker v105) carries it forward again,
  ## 104->105: N40 made `allocateSym` TOTAL (no more raw raises), but
  ## totality alone is not per-path SOUND -- `allocDegrade`'s two sinks
  ## (`loweringDegradeErrors`/`loweringDidDegrade`, drained into a caller's
  ## `Path.uncertain` ONLY by that caller's own subsequent `lower()`/
  ## `lowerInExpr` call; and the immediate global `w.sawUnknown` sync) never
  ## by themselves taint the PATH whose OWN allocation degraded. Verdict
  ## assembly (`runSymexImpl`, ADR-0012 D2, ~line 10498) lets a winning
  ## `sxSat` in `w.found` beat `w.sawUnknown` -- correct when the degrade
  ## happened on a DIFFERENT, disjoint path, but unsound for a path that
  ## reaches a target/assert without ever having its OWN mid-flight degrade
  ## converted into `Path.uncertain`. The heap-deref READ arm (`isDeref`,
  ## `runtime_heap.nim`) had exactly this gap: it calls `mkHeapArrayVar` ->
  ## `heapValueSort` -> `allocateSym` (a throwaway prototype allocation, used
  ## only to read the pointee's value SORT) to materialise the per-path heap
  ## array, then proceeds straight to `heapSelect` + `forkPath` (implicit
  ## taint-propagate, never introduces new taint) -- with NO drain in
  ## between. All THREE `mkHeapArrayVar` call sites inside `isDeref` (the
  ## bare/plain-field path, the variant disc-heap path, the variant
  ## arm-field path) now call `drainPendingLowerEffects` immediately after
  ## materialising the array (fresh or cache-hit), folding any pending
  ## degrade into the reading path's own `uncertain = true` before the value
  ## is ever used -- the SAME "seed(implicit)/lower(implicit)/drain" shape
  ## `lowerInExpr` already uses for every OTHER walk-time consumer, applied
  ## here for the first time to a call site that bypasses `lower()`
  ## entirely. A SECOND, independent instance of the identical shape was
  ## found and fixed in `isDerefWrite`'s variant ARM-FIELD write sub-arm:
  ## its own `armHeap` `mkHeapArrayVar` calls happen AFTER the RHS value's
  ## `lowerInExpr` (which already drained once, for the RHS's OWN degrade
  ## surface) -- an arm-field type degrade discovered only while building
  ## the STORE target was left undrained past `survivors.add`; now drained
  ## again immediately before that add. The disc-heap materialisation on
  ## both the read and write arm-field paths also gained a defensive drain
  ## for call-site-audit completeness (a variant discriminant type is always
  ## a primitive ordinal by construction, so this never actually fires
  ## today -- kept so no `mkHeapArrayVar` call site on this cluster is left
  ## unaudited).
  ##
  ## COMPANION FIX, required to make the above reachable at all rather than
  ## pre-empted: `liftHeapValue` (`runtime_heap.nim`, lifts a heap `select`'s
  ## raw ast back into a `SymVal`) had NO `itUninterp` arm -- ANY heap-deref
  ## read of a field/pointee whose type is the ownership/unsupported-param/
  ## unsupported-witness placeholder family crashed with an uncaught
  ## `SymexRefUnresolvedError` immediately after `heapSelect`, one call past
  ## `mkHeapArrayVar`'s own successful (non-raising) degrade. This crash was
  ## ACCIDENTALLY masking exactly the gap this slice closes (a crash aborts
  ## the whole walk -> top-level catch -> `sxUnknown`, so no per-path taint
  ## was ever needed to stay sound for this specific kind) -- added the arm
  ## (mirrors `itBool`'s own lift, since `allocateSym`'s ownership-degrade
  ## arm always allocates the placeholder VALUE as `svBool`) so the READ
  ## path taint fix has an actual effect for this kind instead of being
  ## permanently pre-empted by an unrelated crash. `itTable`/`itSet`
  ## deliberately UNTOUCHED this slice (N41, `rawAnyAstOf` has no
  ## `svTable`/`svSet` arm, crashes one call earlier inside `heapValueSort`
  ## itself, before `mkHeapArrayVar` even returns) -- masked-sound exactly
  ## as before, per the RFC's own explicit taint-only / N41-stays-open
  ## decision; fixing N41 without ALSO shipping this taint fix would have
  ## REGRESSED soundness (confirmed by isolated probe: `liftHeapValue`'s
  ## `itUninterp` arm alone, without the drain, is a live crash-removal that
  ## un-masks the pre-existing gap -- shipping both together is load-bearing).
  ##
  ## EMPIRICAL NOTE: no black-box SUT construction (opaque-call-sourced ref,
  ## `new`-constructed ref, top-level ref PARAM, two-hop ref-chain PARAM --
  ## roughly a dozen shapes tried) reproduces an OBSERVABLE false `sxSat`
  ## for this gap in the current tree: `{.symexOpaque.}` calls and `new T`
  ## (when `T` has an unclean-zero field) already unconditionally taint
  ## their own call/allocation site for unrelated, pre-existing reasons; a
  ## top-level PARAM whose pointee has an unallocatable field is independently
  ## caught by CR-2c's witness-demotion (`itTable`/`itSet`) or crashes
  ## `emitTyAndReader` at macro-expansion time (`itUninterp`) before
  ## `symexFind` ever runs; and in every reachable two-hop-chain shape tried,
  ## the very next `lower()`-calling statement that consumes the dereffed
  ## value (a `discard`'s own `isLet` binding, an `if` condition) happens to
  ## drain the still-pending degrade onto the SAME unforked path before any
  ## target is reached -- sound by COINCIDENCE, not by construction, exactly
  ## the "misattributed... or lost entirely" hazard `allocDegrade`'s own doc
  ## comment (`runtime.nim`) warns sink (a) carries for any caller that never
  ## drains it directly. Direct runtime instrumentation (added temporarily,
  ## confirmed, then removed) verified the mechanism gap precisely:
  ## `loweringDidDegrade` flips `true` during `isDeref`'s heap-array
  ## materialisation and `child.uncertain` stays `false` immediately after,
  ## for every shape tried -- this fix closes that window unconditionally,
  ## as defense-in-depth against ANY future change (an optimisation eliding
  ## a redundant `discard`/`let`, a new consuming-statement shape) removing
  ## the accidental drain and turning the LATENT gap into a live one, the
  ## same "fix even though today's observable behaviour already degrades via
  ## some blunter mechanism" pattern N36-N40 each established in turn.
  ## `renderAsChoicesVersion` does NOT bump (stays "11") -- no NEW witness
  ## shape is ever solved-for or rendered; a tainted path only ever produces
  ## `sxUnknown`, never a witness.
  ##
  ## N40 (round-6 fix round 6, walker v104) carries it forward again,
  ## 103->104: `allocateSym` (`runtime.nim`) is now TOTAL for every
  ## classifiable input -- the raw-raise-in-lower CLASS's LAST five sites
  ## (`itUninterp` x3, `itTable`, `itSet` -- N36/N37/N39's "category-2"
  ## markers) no longer raise at all, at any call site, walk-time or
  ## otherwise; every classified-decline arm now calls the new `allocDegrade`
  ## helper (in-band, writes BOTH `loweringDegradeErrors`/`loweringDidDegrade`
  ## AND `currentWalkCtxPtr[].sawUnknown` directly and unconditionally) and
  ## returns a fresh, type-plausible placeholder instead of unwinding. Three
  ## successive per-caller-guarding slices (N36/N37/N39) each found a FURTHER
  ## unguarded caller; N40 retires that strategy and fixes totality at the
  ## allocator itself, the one place that can guarantee it for all ~70 call
  ## sites at once (see `allocDegrade`'s own doc comment, `runtime.nim`, for
  ## the full sink-choice design writeup).
  ##
  ## Also closes a FALSE NEGATIVE `unallocatableFieldIssue` (`types.nim`)
  ## carried since N39: a non-string-key `Table[int, string]` (ordinary,
  ## unrestricted Nim syntax) was not flagged, even though `allocateSym`'s
  ## `itTable` arm could not back it (previously an UNTAGGED
  ## `raise newException(ValueError, ...)` crash — not even a classified
  ## carrier). New `seUnsupportedTableKeyType` kind, distinct from the
  ## pre-existing `seUnsupportedTableValType` sibling.
  ##
  ## The pre-walk PARAMETER-entry boundary (`runSymexImpl`) keeps its
  ## pre-N40 WHOLE-RUN raise semantics BY DESIGN: a new pre-check
  ## (`unallocatableFieldIssue` over every top-level param type, before any
  ## walk state exists) raises the SAME classified carrier, `kind`, and
  ## message text `allocateSym` itself used to raise for the identical
  ## shape (`raiseParamAllocIssue`, `runtime.nim`) — every pre-N40 pin on a
  ## param-level classified decline is unaffected.
  ##
  ## Newly-found unguarded walk-time `allocateSym` callers this slice's
  ## totality fix covers WITHOUT any per-caller change (the whole point of
  ## fixing this at the allocator): `runtime_heap.nim`'s heap-deref-read
  ## (`heapValueSort`) and heap-deref-write (`derefWriteProto` x2) prototype
  ## allocations; `runtime_closures.nim`'s lambda param/return sort
  ## allocation (`paramSorts`/`buildClosure`); `freshRetSym`'s five
  ## call-return sites; `lowerHofCall`'s fold-accumulator decline. Confirmed
  ## via TDD (`tests/tsymex_r6_n40_alloc_totality.nim`): the N39-gap
  ## Table-arm-field shape reaches an honest, SPECIFIC `sxUnknown`
  ## (`seUnsupportedTableKeyType`) via N39's own existing guards, now that
  ## the predicate fix closes their false negative. A block-nested heap-deref
  ## READ/WRITE through an unallocatable field type PRE-N40 produced a WRONG
  ## verdict (still `sxUnknown`, but MISATTRIBUTED to an unrelated
  ## `beBudgetExhausted` loop-unwind finding — the raw raise's classified
  ## content was silently discarded under the nesting, not merely uncaught);
  ## POST-N40 it carries the correct, specific `seUnsupportedTableKeyType`.
  ## `lowerHofCall`'s fold-accumulator and `freshRetSym`'s call-return sites
  ## are covered structurally by the SAME `allocateSym` change (no dedicated
  ## per-site pin — the mechanism argument N36/N37/N39 already established
  ## for un-independently-pinnable sites applies). FLAGGED (found, NOT
  ## fixed, out of this slice's scope): a closure PARAM/RETURN type that is
  ## itself compound (`Table`/`Set`/`Seq`/`Variant`) still crashes downstream
  ## in `sortOfTuple`/`rawAnyAstOf` (no arm for any compound `sv*` kind,
  ## valid OR unsupported — a closure with a perfectly VALID
  ## `Table[string, int]` param hits the identical crash) — caught by the
  ## top-level net (`weInternalWalkerFault` -> `sxUnknown`, Invariant 3
  ## intact) but not with N40's own specific kind; N40 does not itself
  ## unlock this family. See the test file's own family-4/5 comment for the
  ## full writeup; a follow-up slice extending `sortOfTuple`/`rawAnyAstOf`
  ## to compound leaves is the natural next step.
  ##
  ## `isVariantConstructSym`/`lowerVariantLit`'s own N39 per-caller guards
  ## are KEPT (not retired) as fast-paths with their own nicer, more
  ## specific messages ("variant constructor field allocation unmodeled —
  ## ...") — they short-circuit BEFORE the (now-redundant, since
  ## `allocateSym` itself is total) fork/allocation loop, which is strictly
  ## cheaper than letting the total allocator run to completion on every
  ## fork just to discover the same degrade. Both guards benefit from this
  ## slice's `unallocatableFieldIssue` predicate fix automatically (the
  ## Table-key-type gap they shared with the allocator is now closed for
  ## them too, with no code change at either guard site).
  ##
  ## `renderAsChoicesVersion` does NOT bump (stays "11") — a degraded
  ## fork/allocation always demotes to `sxUnknown`; the placeholder value is
  ## never solved-for or rendered, the same precedent N39/SND-3's own
  ## landing established.
  ##
  ## N39 (round-6 fix round 5, closing a mis-scoped safety certification in
  ## the raw-raise CLASS) carries it forward again, 102->103. N36's own
  ## `category-2` marker on `allocateSym`'s five itUninterp/itTable/itSet
  ## raise sites (runtime.nim :1680/:1694/:1721/:2005/:2019) claimed they
  ## are "reached only during pre-walk parameter allocation, zero
  ## intervening `walkBlock` frames" — TRUE for every PARAMETER-allocation
  ## caller (matches ADR-0023's own explicit carve-out for these five
  ## sites), but FALSE for two WALK-TIME callers the original N36 spot-
  ## check missed entirely: `isVariantConstructSym` (fork-per-tag symbolic-
  ## discriminant variant CONSTRUCTION — allocates EVERY declared arm's
  ## fields in EVERY fork, unconditionally) and `lowerVariantLit` (variant
  ## LITERAL construction — allocates every INACTIVE arm's fields fresh).
  ## `classifyFieldType` (dsl_typebridge.nim) legitimately classifies a
  ## variant ARM field as one of these five unsupported shapes (e.g. a
  ## `Table[string, string]`/`HashSet[string]` arm field) —
  ## `scopedDeclineFieldTy`'s Bug #2 scoped decline only special-cases
  ## `itSeq`, so nothing intercepts these five kinds before they reach the
  ## arm's `fieldTypes`.
  ##
  ## Empirically probed BOTH routes this slice (stash method): a symbolic-
  ## discriminant construction (`isVariantConstructSym`) reaching an
  ## unsupported arm-field type CONFIRMED the exact C-backend goto-exception
  ## hazard ADR-0023/SND-3 exists to ban — block-nested, PRE-FIX `sxUnsat`
  ## with ZERO errors (WRONG, silently lost) vs. the SAME shape unblocked,
  ## honest `sxUnknown` — for BOTH the `itTable` and `itSet` unsupported
  ## shapes. A variant LITERAL reaching the identical unsupported type on an
  ## INACTIVE arm (`lowerVariantLit`) was probed across eight distinct
  ## nesting shapes (bare block, `for`, `while`, nested blocks, the
  ## statement-after-the-loop shape, and — matching ADR-0023's own tracer-
  ## bullet structure — embedded directly in a `while` GUARD expression) and
  ## never reproduced the loss; every shape already yielded honest
  ## `sxUnknown`. Both call sites were nonetheless GUARDED (the unguarded
  ## raw-raise reachability was a certification error either way, per the
  ## class description's own framing) via GUARD-BEFORE-CALL: a new
  ## `unallocatableFieldIssue` (types.nim) mirrors `allocateSym`'s dispatch
  ## kind-for-kind (like `allocCostOf`'s own precedent) to predict, WITHOUT
  ## calling `allocateSym`, whether a field type would raise — recursing
  ## through every composite kind `allocateSym` itself recurses through, so
  ## an arbitrarily-nested unsupported leaf (e.g.
  ## `array[3, Table[string, string]]`) is caught too, not just a bare
  ## top-level field. `isVariantConstructSym` degrades the whole
  ## construction via its own existing `w.sawUnknown`/`walkDegradeErrors`/
  ## `forkPathTainted` idiom (hoisted above the fork loops, alongside its
  ## two existing budget checks — every fork allocates every arm regardless
  ## of tag, so a per-tag distinction is not available anyway).
  ## `lowerVariantLit` degrades via the `loweringDegradeErrors`/
  ## `loweringDidDegrade` sink ADR-0023 established for exactly this
  ## "`lower()`-reachable, no `Path`/`WalkCtx` in scope" shape, substituting
  ## a bare fresh `svBool` for the declined field (sound: an inactive arm's
  ## field is reachable ONLY through `isVariantField`'s out-of-arm
  ## `FieldDefect` fork, so no live SAT path ever reads its value or kind —
  ## the same tolerance `tyOf`'s own "diagnostics only" svVariant arm
  ## already relies on).
  ##
  ## Bumped because `isVariantConstructSym`'s conversion is a genuine
  ## verdict-surface change (a false `sxUnsat` under block nesting -> honest
  ## `sxUnknown`), empirically confirmed via the stash method — the same
  ## bar N36/N37 set. `lowerVariantLit`'s conversion is a certification-
  ## accuracy / hardening fix applied by the class-description mechanism
  ## argument (N36/N37 precedent for un-independently-pinnable sites): the
  ## raw raise was never observed lost in any probed shape, so this half is
  ## not itself an isolable RED->GREEN flip, but ships in the SAME slice
  ## and commit as the confirmed half. `renderAsChoicesVersion` does NOT
  ## bump (stays "11") — a degraded fork/lowering always demotes to
  ## `sxUnknown`, the fresh degrade symbol is never solved-for or rendered,
  ## same precedent SND-3's own original landing established.
  ##
  ## N37 (round-6 fix round 4, adjudication slice) carries it forward again,
  ## 101->102: closes the LAST enumerated residue of the raw-raise-in-lower
  ## CLASS N36 left as `known-open` backlog, plus one caller N36 didn't
  ## enumerate. Adjudicated per site: `iekSeqSlice`'s two raw declines
  ## (base-kind mismatch, CR-17-style bound mismatch) and `isRaise`'s bare-
  ## reraise-with-nothing-to-reraise decline (a WALK-level site, not a
  ## lowering-level one — generalizing the class beyond `lower()`) were all
  ## CONFIRMED REACHABLE from valid DSL surface and empirically CONFIRMED
  ## (stash method) to produce a FALSE `sxUnsat` with ZERO errors when the
  ## raise fires inside a nested `walkBlock` frame, vs. an honest classified
  ## `sxUnknown` for the identical shape without the nesting — the same
  ## silent-loss hazard N36 closed elsewhere, now generalized to a
  ## walk-level (not merely lowering-level) site for the first time. All
  ## three converted to the established in-band degrade idiom
  ## (`loweringDegradeErrors`/`loweringDidDegrade` for the two lowering-level
  ## `iekSeqSlice` sites; `w.walkDegradeErrors`/`w.sawUnknown` for the
  ## walk-level `isRaise` site, mirroring `isVariantReassign`/`isIndex`'s own
  ## N36 conversions). `lowerHofCall`'s inline `map`/`filter` calling
  ## `allocateSeqDataRaw` unguarded was likewise CONFIRMED reachable (N36's
  ## own doc note already established this) and, empirically, its raw-raise
  ## effects were CORRUPTED rather than cleanly lost — a spurious `ekZ3Error`
  ## surfaced instead of the correct `seNestedSeqUnsupported` classification.
  ## A THIRD, previously-unenumerated unguarded caller of the same raise was
  ## found (`lowerSeqLit`'s non-empty-literal branch). All three were fixed
  ## by GUARDING with `isBackedSeqElemTy` before ever calling the unsafe
  ## function (mirroring `allocateSym`/`defaultZero`'s own itSeq-arm
  ## discipline) rather than catching after the raise — every caller of
  ## `allocateSeqDataRaw` in this file now guards first, so ITS OWN raw raise
  ## is VERIFIED UNREACHABLE (upgraded from N36's `known-open`, kept as a
  ## defensive backstop). `iekSeqLen`'s unsupported-receiver-kind decline was
  ## adjudicated VERIFIED UNREACHABLE (not converted): the parser only ever
  ## emits an `iekSeqLen` node for an `itSeq`/`itTable`/`itSet`-classified
  ## receiver, and the one cross-representation mismatch reachable at a
  ## walk-time (a call-boundary string-backed `seq[byte]` argument bound
  ## into a non-string-backed callee param) already lands on the `svString`
  ## arm immediately above it, empirically confirmed this slice via the same
  ## call-boundary construction used for `iekSeqSlice`. Bumped because three
  ## of the five audit-marked sites, plus the HOF/seq-literal bypass, are
  ## genuine verdict-surface fixes (false `sxUnsat` -> honest `sxUnknown` /
  ## correctly-classified `sxUnknown`), not mere marker bookkeeping.
  ##
  ## N36 (round-6 fix round 4, confirmed High soundness) carries it forward
  ## again, 100->101: closes the raw-raise-in-lower CLASS N31 fixed only ONE
  ## instance of (`iekStrSubstr`'s CR-17 guard). A spot-check confirmed 14+
  ## further raw raises of classified-decline error carriers reachable from
  ## inside nested `walkBlock` frames — the identical C-backend
  ## goto-exception-unwind hazard (ADR-0023/SND-3): `requireStr`/
  ## `needleAsStr` (used by ~13 `lowerStrArm` arms), `join`/`split`, `match`/
  ## `findRe`/`replaceRe`, `bytes`, `radixFmt`, `toLower`/`toUpper`, the
  ## `iekStrInOptionRegion` guard (a documented copy of the PRE-fix CR-17
  ## form), and the "not modeled" string-op catch-all (all
  ## `runtime_strings.nim`); `isVariantReassign`'s UNGUARDED `defaultZero`
  ## call (`runtime.nim`, raw-raises `ValueError`/`SymexRefUnresolvedError`
  ## for float/ref/ptr/Table/HashSet/nested-variant/distinct new-arm
  ## fields); and `isIndex`'s Table-value-type and unsupported-receiver-kind
  ## declines (`runtime.nim`, both raw `raise`s inside the walk loop).
  ##
  ## FIX (string family): rather than hand-convert `lowerStrArm`'s ~18
  ## individual raw-raise sites, a single CHOKEPOINT wrap at `lower`'s
  ## `lowerStrArm(env, e)` call site (`runtime.nim`) catches every
  ## classified carrier `lowerStrArm` can raise
  ## (`SymexUnsupportedStringOpError`/`SymexZ3VersionMissingError`/
  ## `SymexZ3StringIncompleteError`/`SymexUnsupportedRegexError`/
  ## `SymexBytesSymbolicLengthError`/`SymexBytesLengthTooLargeError`) and
  ## converts to the SAME in-band degrade idiom `iekStrSubstr`'s N31 fix
  ## established: `loweringDegradeErrors.add` + `loweringDidDegrade = true`
  ## + a fresh unconstrained symbol of the arm's intended result kind
  ## (`degradeStrArm`, keyed on `e.kind` since the caught exception carries
  ## no static result-type information). SOUND because the unwind from ANY
  ## raise inside `lowerStrArm` to this catch crosses ONLY plain proc frames
  ## (`lowerStrArm` itself, `requireStr`, `needleAsStr`, …) — `lowerStrArm`
  ## never calls `walk`/`walkBlock` — so the hazard cannot occur between the
  ## raise and this catch regardless of how many `walkBlock` frames sit
  ## ABOVE this `lower()` call in the walker's own chain. Confirmed
  ## empirically: block-nested repros for the `iekStrInOptionRegion` guard,
  ## a `requireStr`-family shape, and an oversize-`split` shape all showed
  ## the pre-fix silent-completion/false-verdict RED, post-fix honest
  ## `sxUnknown` GREEN (see `tests/tsymex_r6_n36_raise_degrade.nim`).
  ##
  ## FIX (`isVariantReassign`/`isIndex`): each converted at its OWN call
  ## site to the walk-level in-band degrade idiom its already-correct
  ## siblings use (`w.walkDegradeErrors.add` + `w.sawUnknown = true` +
  ## `forkPathTainted`, mirroring the `isCall`/`applyClosureGround`
  ## `defaultZero` fallthrough guards and the `isUnsupportedFieldPlaceholder`
  ## sibling decline in `isIndex` itself).
  ##
  ## VERDICT-SURFACE change: any SUT shape that previously hit ONE of these
  ## raw raises from inside a `block:`/nested-loop context and silently
  ## defaulted to a false `sxUnsat` now correctly reports the honest
  ## classified `sxUnknown` (or, where a legitimate sibling path survives
  ## independently of the degraded branch, may upgrade all the way to
  ## `sxSat` — the SAME incidental-upgrade shape N31 documented). A shape
  ## that already reached the shallow, unnested `runSymex`-boundary `except`
  ## handler is UNCHANGED (same classified `sxUnknown`, same `SymexErrorKind`
  ## — the improvement is under-`walkBlock` honesty, not a new decline
  ## surface). See `tests/tsymex_r6_n36_raise_degrade.nim` and
  ## `tests/tsymex_r6_n36_raise_class_audit.nim` (the permanent regression
  ## guard closing the class, mirroring N27's audit precedent).
  ##
  ## N31 (round-6 fix round 3, confirmed High soundness) carries it forward
  ## again, 99->100: `iekStrSubstr`'s CR-17 slice-bound decline
  ## (`runtime_strings.nim`) used a raw `raise (ref
  ## SymexUnsupportedStringOpError)` -- exactly the C-backend
  ## goto-exception-unwind hazard ADR-0023/SND-3 exists to ban from
  ## `lower()` ("a raise here would unwind through the enclosing loop's live
  ## `seq[Path]` and be silently lost on the C backend's goto-exception
  ## model", b7258f7/CR-1c class -- the identical comment already present at
  ## the sibling CR-17(a) ordering-comparison guard a few hundred lines away
  ## in `runtime.nim`, which was already fixed for this exact reason and
  ## never raises). Reached from inside two or more nested `walkBlock`
  ## frames (e.g. a recognized accumulating-scan closed form -- B4,
  ## `tryRecognizeAccumulatingScan` -- built for a loop whose counter is a
  ## TWO-HOP literal-seeded local, `var i = localOffset` where `localOffset`
  ## itself is `var localOffset = <intlit>`, wrapped in an explicit `block:`
  ## inside the proc body), the `raise` executes but is never caught: `walk()`
  ## returns as though it completed normally, no error is recorded, and the
  ## walker's default-to-UNSAT fallback fires for a concretely reachable
  ## target -- container-confirmed by direct instrumentation this slice
  ## (probe reverted before landing). Fixed by degrading IN-BAND like every
  ## other `lower()` site in this class: `loweringDegradeErrors.add` +
  ## `loweringDidDegrade = true` + a fresh unconstrained `svString`: the
  ## mandatory per-`lower()`-call drain (`drainPendingLowerEffects`, already
  ## invoked unconditionally by `lowerInExpr`) forks the path `uncertain`
  ## and sets `w.sawUnknown` regardless of nesting depth, so the decline is
  ## honest at ANY nesting depth. VERDICT-SURFACE change: the two-hop-in-
  ## block shape's false `sxUnsat` now correctly reports `sxSat`; the SAME
  ## shape WITHOUT the `block:` wrapper (previously an honest `sxUnknown`
  ## decline, since the raise reached `runSymex`'s specific `except` handler
  ## one nesting level shallower) is INCIDENTALLY upgraded `sxUnknown` ->
  ## `sxSat` too, since the mechanism fix is not block-shape-specific — a
  ## legitimate sibling path (loop never entered) is no longer discarded by
  ## an all-or-nothing raise. See `tests/tsymex_r6_n31_block_counter.nim`
  ## for the full RED/GREEN derivation (six pins: the exact repro, a
  ## target-before-block companion, a direct-literal-seed companion, the
  ## no-block upgrade, an UNSAT companion proving no over-correction, and a
  ## raise-path companion).
  ## D2 (round-6 review remediation, confirmed Medium resource-budget
  ## undercount) carries it forward again, 98->99: N9's
  ## `maxVariantConstructorFieldAllocs` check (`isVariantConstructSym`,
  ## `runtime.nim`) computed its per-fork cost as the FLAT
  ## `arm.fieldTypes.len` sum -- a plain field COUNT, not what each field
  ## actually costs to allocate. `allocateSym` itself recurses (an
  ## `array[N, T]` field allocates `N` copies of `T`, a nested tuple/variant
  ## field allocates ITS OWN fields, ...), so a composite arm-field type let
  ## the real allocation cost amplify far past what the flat count
  ## suggested while staying UNDER the flat budget (an 8-arm variant with
  ## one `array[1_000_000, int]` field per arm counts as `8x8=64` flat
  ## fields -- exactly at the default budget, passing -- while actually
  ## performing 64,000,000 leaf Z3 allocations). Fixed by a new
  ## `allocCostOf` helper (`smt/types.nim`) that mirrors `allocateSym`'s own
  ## recursive dispatch kind-for-kind (array: size x element cost; tuple:
  ## sum of field costs; variant/multi-variant: disc + plain fields + every
  ## arm's fields, recursively; seq/table/set: O(1), matching
  ## `allocateSeqDataRaw`'s single-array-const allocation regardless of
  ## element type) and replaces the flat field-count sum with the recursive
  ## leaf-allocation cost. VERDICT-SURFACE change: a composite-arm-field
  ## shape that previously constructed (flat count under budget) may now
  ## classify `beBudgetExhausted` (recursive leaf-allocation cost over
  ## budget) -- the intended, documented behavior change; the default
  ## budget value (64) is unchanged, only its UNIT (fields -> leaf
  ## allocations). See `allocCostOf`'s own doc comment (`smt/types.nim`) for
  ## the full recursion writeup.
  ## N28 (round-6 fix round 3, verifier-confirmed LIVE bug, MEDIUM
  ## soundness) carries it forward again, 97->98: `markSymOrRootParam`
  ## (`dsl_parser.nim`, shared by `collectStringBackedByteSeqParamsImpl` and
  ## `collectIntOffsetParamsImpl`) accepted a candidate symbol -- or the
  ## root a local rebind traced to, via `findRootParam` -- as one of the
  ## proc's own formal parameters by comparing PRINTED NAMES
  ## (`sym.strVal in paramNames`), even though both are true `nnkSym` nodes
  ## with real binding identity available. A nested-scope SHADOW local
  ## sharing a formal's name defeats this: a scan's loop-index local rebound
  ## from `var i = offset` where `offset` is a SHADOW (not the formal of the
  ## same name) resolves, via `findRootParam`, to the shadow's own symbol --
  ## which then wrongly reads as the UNRELATED formal by name. Confirmed
  ## LIVE for `collectIntOffsetParamsImpl`: the formal ends up
  ## unconditionally `isIntOffset`-promoted to `svInt`
  ## (`runtime.nim`'s top-level param loop) with NO declared range and --
  ## per R3 (S2)'s own deliberate scope note -- NO `ziWidth`/`ziSigned`
  ## stamp at that specific site, so `overflowCondInt`'s fork never fires:
  ## a real int64 overflow the formal's UNRELATED, honest arithmetic
  ## actually raises reports a false `sxUnsat` instead of `sxRaised`.
  ## Also empirically confirmed to affect (as a decline, not a verdict
  ## flip) the parallel `considerCandidate` direct-name check in the
  ## string-backed collector: a shadow-collision `seq[byte]` formal wrongly
  ## classified string-backed produces a `seUnsupportedStringOp` decline
  ## (`iekStrLen` parsed against a symbol whose runtime allocation disagrees)
  ## instead of the honest `sxSat` an ordinary array read of an unrelated,
  ## never-scanned formal should get. Fixed by testing true symbol identity
  ## (`containsSym`/`sameSym`, the house R4/R6 primitives) against the
  ## proc's own formal SYMBOLS in both collectors' acceptance checks. See
  ## `tests/tsymex_r6_n28_shadow_collision.nim` for the RED/GREEN
  ## derivation (its header also records why the string-backed sibling,
  ## while empirically observable as a decline, never produced a wrong
  ## SAT/UNSAT/witness verdict in the constructed shapes -- narrower in
  ## practice than the int-offset collector's flip, but still fixed
  ## identically, same helper, same class of bug).
  ## N27 (round-6 fix round 2, D1-verifier-confirmed LIVE bug, HIGH
  ## soundness) carries it forward again, 96->97: `lowerHofCall`
  ## (`runtime.nim`, backs `.map`/`.filter`/`.fold`) called `concreteSeqLen`
  ## on its receiver with NO `isUnsupportedFieldPlaceholder` check anywhere
  ## in the proc -- the R1 chokepoint (`declinePlaceholderInLower`) every
  ## OTHER svSeq-consuming `lower()` arm calls first. A placeholder-ized
  ## receiver (e.g. a `seq[(string,string)]` param `allocateSym` cannot
  ## back) has its `seqLen` HARD-FORCED `== 0`; `concreteSeqLen` folded that
  ## fabricated 0, `canInline` picked n=0, and the result `SymVal` was built
  ## WITHOUT the taint flag -- the exact S1 false-verdict class R1 fixed,
  ## escaped via the HOF path (e.g. `xs.map(g).len > 0` silently proven
  ## `sxUnsat` against a fabricated empty length). Fixed by guarding
  ## `lowerHofCall` at its single receiver-lowering point, before any
  ## length/element/axiom read, and declining through the chokepoint with a
  ## type-correct flagged stub per op (`map`/`filter` propagate the
  ## already-forced-0 `seqLen`/inert `seqDataRaw`; `fold`'s accumulator type
  ## degrades via a fresh unconstrained stub, mirroring its own axiom-path
  ## decline). See `tests/tsymex_r6_n27_hof_placeholder.nim` for the
  ## RED/GREEN derivation and `tests/tsymex_r6_n27_placeholder_read_audit.nim`
  ## for the class-closing grep audit (bans a future bare `.seqLen`/
  ## `.seqDataRaw`/`.isUnsupportedFieldPlaceholder` read outside the
  ## chokepoint procs, allocation sites, or an explicit
  ## `# [placeholder-audited]` marker).
  ## N16 (round-6 re-review fix slice, closure/lambda zero-default result
  ## binding, MEDIUM soundness): `applyClosureGround` (`runtime.nim`, the
  ## SHARED implementation for direct closure/lambda calls -- `lowerClosure-
  ## Call` -- AND the C4 HOF inline path, map/filter/fold) descends a closure
  ## body and, for each fall-through sub-path, asserted a ground axiom
  ## binding `funcApp` only when the sub-path's env contained "result" --
  ## with NO `else` twin for a fall-through path that never touches `result`
  ## at all (legal Nim -- `result` holds the return type's zero value on
  ## such a path). Pre-fix, `funcApp` stayed completely UNCONSTRAINED on
  ## such a path, so the solver could pick any value there: a false `sxSat`
  ## with a non-replaying witness. This is the EXACT shape R2 (walker v90,
  ## below) fixed for the `isCall` arm's own fallthrough -- a prior commit's
  ## comment claiming `applyClosureGround` "already handles this exact shape
  ## correctly" was FALSE; it never had an else-twin at all. Fixed by
  ## mirroring R2's else-twin idiom exactly: bind `funcApp` to
  ## `defaultZero(cb.retTy, ...)` via the same `retBindEq`, reusing the
  ## module-level `defaultZero` constructor; a closure retTy that hits one
  ## of `defaultZero`'s unsupported kinds classified-declines (sxUnknown),
  ## never binds a wrong value, never crashes. See
  ## `tests/tsymex_r6_n16_closure_zerodefault.nim` for the full RED/GREEN
  ## derivation, including two honestly-pinned PRE-EXISTING orthogonal
  ## declines this slice does NOT fix: the C4 HOF inline map/filter path's
  ## Z3 sort-mismatch on a conditional-body closure (matches that suite's
  ## own C4-1/C4-1b), and closures returning `string` (`symValFromRawAst`
  ## has no `itString` arm at all, independent of this slice's fallThrough
  ## fix).
  ## N21 (round-6 re-review fix slice, pair-loop member-branch region-
  ## grammar correction, CRITICAL soundness, 2026-08-22): the B6 pair-loop
  ## closed form's member branch (`tryRecognizePairLoopIdiom`, `dsl_parser.nim`)
  ## replaces the WHOLE `readOptions` loop with an empty block whenever
  ## `iekStrInOptionRegion(s, i, bound)` holds, asserting "no defect
  ## possible on any member string". The region grammar it certified
  ## against (`runtime_strings.nim`) was bare NUL-delimited segment-star,
  ## `((nonzero)* "\0")*`, with NO parity constraint tying it to how the
  ## real loop actually consumes the region two segments (key, value) at a
  ## time. An odd number of segments with a non-empty final segment (e.g.
  ## `"aa\x00bb\x00cc\x00"`, container-confirmed) was wrongly certified a
  ## member even though the real SUT raises `ScanError` reading the
  ## incomplete final pair's value — a genuine FALSE-SAT / false-decline
  ## pair (`symexFind(done)` reported sxSat with a non-replaying witness;
  ## `symexFind(tRaisedExn(ScanError))` reported sxUnknown where ground
  ## truth is the raise). Fix: the grammar is strengthened to
  ## `PAIR* ("\0" anybyte*)?` where `PAIR = (nonzero)+ "\0" (nonzero)* "\0"`
  ## — zero or more complete non-empty-key pairs, optionally followed by a
  ## lone empty-key terminator NUL with the unconsumed remainder (never
  ## read by the real loop) left unconstrained. Both real clean-exit shapes
  ## are represented (counter lands exactly on `bound` after N whole pairs;
  ## OR an empty-key segment triggers `break` before `bound`). See
  ## `tests/tsymex_r6_n21_pairloop_member.nim` and `runtime_strings.nim`'s
  ## `iekStrInOptionRegion` arm for the full derivation and ground-truth
  ## verification. Verdict-changing for exactly the odd/incomplete-final-
  ## segment shape class (previously wrongly-member -> now correctly
  ## non-member, routing to the pre-existing sound k-unroll fallback);
  ## every genuinely-member shape (whole pairs, with or without a trailing
  ## terminator) keeps its prior sxSat verdict — the existing B6/N10 corpus
  ## sweep confirmed clean (see `tests/tsymex_r6_b6_optionregion.nim` and
  ## `tests/tsymex_r6_n10_coverage_matrix.nim`'s own N10d-5 pins, whose
  ## doc comments record why their literals already agreed with the
  ## stricter grammar).
  ##
  ## N9 (round-6 review remediation slice, variant-constructor field-
  ## allocation budget, 2026-08-22): `isVariantConstructSym`'s
  ## `maxVariantConstructorForks` budget (Round-6 A3) is a STRUCTURAL cap
  ## against `vcsTagSet.len` ONLY — the outer per-tag fork count. The
  ## per-fork field-allocation loop, however, walks EVERY declared arm of
  ## `vcsVariantTy` (not just the fork's own tag — construction has no
  ## "active arm" to narrow to, see that stmt kind's own doc comment), so
  ## the REAL per-construct cost is `vcsTagSet.len` (bounded) times the
  ## total field count across ALL arms (UNbounded) — a wide variant with
  ## many fields per arm amplifies allocation work with no accounting at
  ## all, even when the fork count itself sits comfortably under budget
  ## (e.g. a fork count of 8 with 8 fields per arm across 8 arms performs
  ## 512 fresh Z3 allocations where the fork budget alone suggests 8).
  ## Fix: a new `maxVariantConstructorFieldAllocs` budget (default `64`,
  ## `ResourceBudget`) checked STRUCTURALLY (before any solver work,
  ## same style as the existing fork-count check) against
  ## `vcsTagSet.len * (sum of fieldTypes.len across vcsVariantTy.vArms)`;
  ## past it, the SAME `beBudgetExhausted` classified decline kind the
  ## fork-count budget already uses (SND-4 "mirror, don't reinvent" —
  ## not a parallel mechanism), with a message distinguishing the two
  ## budgets by name. The existing fork-count check runs FIRST and is
  ## unchanged, so every already-pinned A3 shape (including the
  ## narrowed-wide `WideObj` case, 2 forks x 10 declared-arm fields = 20
  ## allocations, comfortably under the new default) resolves to the
  ## IDENTICAL verdict as before this slice. Verdict-changing ONLY for a
  ## shape whose fork count is within `maxVariantConstructorForks` but
  ## whose total per-fork field-allocation count exceeds
  ## `maxVariantConstructorFieldAllocs`: previously such a shape would
  ## proceed to unbounded allocation work (real verdict, just
  ## unaccounted-for cost); it now classifies the same honest
  ## `beBudgetExhausted` decline a too-wide fork count already gets — so
  ## the cache key rotates (`Ver: SW`). See
  ## `tests/tsymex_r6_n9_variant_budget.nim`.
  ##
  ## R5 (post-0.4.0 remediation slice, B6 pair-loop counter advance, S4,
  ## 2026-08-22): `tryRecognizePairLoopIdiom`'s (B6, `dsl_parser.nim`)
  ## MEMBER-branch closed form replaces the whole pair-loop with an EMPTY
  ## block — the loop counter (e.g. `i`) is never advanced. Real Nim
  ## `readOptions` semantics do NOT guarantee the counter equals `bound` on
  ## exit: the canonical shape (a trailing double-NUL terminator) exits via
  ## `break` on the empty-key terminator segment, leaving the counter at
  ## the START of that segment (`bound - 1`), NOT `bound` — while a region
  ## with no embedded empty-key segment before `bound` genuinely does exit
  ## with counter == `bound` (the loop guard, not a `break`, ends it). The
  ## two sub-cases disagree and no single formula covers both — hand-
  ## derived and confirmed via a concrete counter-example
  ## (`collectPairLoopCounterConsumedAfter`'s own doc comment,
  ## `dsl_parser.nim`) that an unconditional `i = bound` binding (the
  ## naive fix candidate) would be UNSOUND for exactly the canonical,
  ## already-pinned terminated shape. Any code AFTER the loop reading the
  ## counter would therefore see either a STALE (pre-loop, unfixed) or an
  ## UNSOUND (naive-binding) value; currently theoretical (no chapulin
  ## shape consumes the exit counter), but the recognizer never gated on
  ## it either. Fix: a new parse-time pre-pass,
  ## `collectPairLoopCounterConsumedAfter` (mirrors
  ## `collectIntOffsetLiteralLocals`'s own single-pass, no-call-boundary-
  ## trace style), finds every pair-loop whose counter is referenced
  ## anywhere AFTER the loop in the SUT's own source (`ctx.pairLoopCounterConsumedAfter`,
  ## `containsSym`-consulted, same `seq[NimNode]`/save-clear-restore
  ## discipline R4 established for `stringBackedParams`/
  ## `intOffsetLiteralLocals`, applied here from the start); `tryRecognizePairLoopIdiom`
  ## skips the region-membership fast-path fork ENTIRELY for those, using
  ## the SAME fold-omitted `mkShortCircuitWhile` k-unroll the non-member
  ## arm already builds as the loop's WHOLE replacement — genuinely
  ## per-iteration-correct, and NOT the same as falling through to the
  ## generic unrecognized-loop path (that path re-includes the fold
  ## statement, `<pairs>.add(...)`, which is unconditionally unwalkable
  ## this cycle — `itSeq[itTuple[string,string]]` has no
  ## `allocateSeqDataRaw` backing — and would degrade every such query to
  ## `sxUnknown` the instant a real iteration reached it; confirmed via an
  ## isolated repro while landing this slice). This is the RFC's own
  ## fallback option (b): "gate on counter-not-read-after-loop", chosen
  ## over option (a) ("bind counter = bound") because (a) is demonstrably
  ## unsound, not merely more invasive. VERDICT-AFFECTING: a pair-loop
  ## whose counter is consumed downstream now correctly falls back to
  ## k-unroll (real per-iteration semantics) instead of silently exposing
  ## the loop's own stale entry value to that downstream code.
  ## `renderAsChoicesVersion` stays UNCHANGED (11) — no new witness shape;
  ## the k-unroll fallback path was already fully wired and rendered.
  ## AUDIT (this slice, per its own DoD): the three sibling recognizers —
  ## Q1/B0 (`tryRecognizeScanIdiom`), B3 (`tryRecognizeScanPairIdiom`), B4
  ## (`tryRecognizeAccumulatingScan`) — each ALREADY bind their loop's
  ## counter to `boundIR` in their own not-found/OOB branch
  ## (`mkAssign(iNode.strVal, boundIR)`) — the real Nim semantics for
  ## THEIR shapes (a plain `while i < bound: ... inc i` skip-scan, or an
  ## early-`return`-on-match scan) genuinely do exhaust to `i == bound` on
  ## the not-found path, with no `break`-without-advance alternative the
  ## way B6's pair-loop has — so B6 was confirmed the ONLY one of the four
  ## with this gap. See `tests/tsymex_r6_r5_pairloop_counter.nim` for the
  ## RED/GREEN pins.
  ##
  ## R4 (post-0.4.0 remediation slice, collector scoping + guard hardening,
  ## W1/N8/N2/W2/W3, 2026-08-21): `ctx.stringBackedParams`/
  ## `ctx.intOffsetLiteralLocals` (`dsl_parser.nim`) were name-keyed
  ## `HashSet[string]` fields, populated ONCE for the top-level entry proc
  ## and consulted throughout the ENTIRE parse with no proc-boundary
  ## scoping — an unrelated callee whose param happened to share a name
  ## with the entry's own qualifying param/local (W1, e.g. `data`)
  ## inherited its classification by bare name collision, bypassing the
  ## callee's own vetting (including the mutation veto); a same-proc,
  ## different-scope colliding binding could do the same (N2's confirmed
  ## narrow variant, N8's general design diagnosis). VERDICT-AFFECTING:
  ## these misclassifications changed which representation
  ## (`svString`/`svInt` vs the type-driven default) a receiver/local
  ## allocated under, changing verdicts for name-collision shapes. Fix:
  ## both fields RE-KEYED to `seq[NimNode]` of the qualifying symbol's own
  ## Sym node, consulted via a new symbol-identity `containsSym` (built on
  ## the codebase's own established `sameSym`, R6) instead of bare `strVal`
  ## membership, PLUS proc-boundary save/clear/restore around
  ## `ensureProcRegistered`'s recursive callee parse (mirrors `caseNarrow`'s
  ## own ADR-0029 discipline) so neither field's ambient value survives
  ## into a callee's own body walk at all. Companion crash-hardening in the
  ## same slice, non-verdict-affecting on their own but riding this bump:
  ## (W2) `scanShapeReceiverMutated` widened to treat a `paramName` passed
  ## at a var-mode argument position of ANY call in the proc body as
  ## mutation too (previously only direct bracket-assign/`.add`/`.del`/
  ## `.insert` forms were caught — a `var`-aliased helper-call mutation
  ## slipped through, misclassifying the receiver string-backed and
  ## reaching `iekSeqAdd`'s receiver arm with an `svString` value); the
  ## raw `doAssert recv.kind == svSeq` there is now a classified
  ## `weInternalWalkerFault` decline (defense in depth, mirrors `lowerBool`'s
  ## v64 doAssert->decline idiom) instead of a native crash. (W3)
  ## `considerCandidate` (the B1a classifier's candidate walk) gained the
  ## standing DoD's `typeKind != ntyNone` guard before its `classifyType`
  ## call, and the one-level call trace's callee resolution switched from
  ## raw `getImpl` to the shared `resolveRoutineImpl` core — the exact A5
  ## hard-crash class (non-catchable compile error on unsemchecked AST),
  ## latent until a monomorphized/generic callee reached this path.
  ##
  ## R3 (post-0.4.0 remediation slice, svInt overflow honesty, S2,
  ## 2026-08-21/22): `overflowCond` (`runtime.nim`) forked an
  ## `OverflowDefect` path ONLY for signed BV operands — a `svInt`-
  ## represented value (this round's int-offset machinery,
  ## `IRParam.isIntOffset`/`IRStmt.isLet.lIsIntOffsetLocal`, deliberately
  ## promotes typed Nim int counters to `svInt` so Sequence-theory ops
  ## accept them) NEVER forked, a false-`sxUnsat` hole for any
  ## defect-reachability search touching a promoted counter's arithmetic.
  ## Fix: `SymVal.svInt` gains `ziWidth`/`ziSigned` (the promoted value's
  ## static Nim type, populated at every promotion/reconciliation site — see
  ## `SymVal.ziWidth`'s own doc comment for the full list), and a new
  ## `overflowCondInt` (`lowerArith`'s svInt sibling to `overflowCond`) forks
  ## on the plain Int-arithmetic range check `result < low(T) or result >
  ## high(T)` for `bAdd`/`bSub`/`bMul` — parity with the BV path's own op
  ## restriction (div/mod are never overflow-forked on either side).
  ## SCOPE NOTE (found empirically landing this slice): the top-level param
  ## promotion site (`runSymexImpl`, `promoteLoose`/`promoteSound`/
  ## `isIntOffset`) deliberately does NOT stamp `ziWidth`/`ziSigned` — doing
  ## so caused a severe runtime regression across the B4/B5/B6 corpus (an
  ## ordinary `isIntOffset`-traced param like `start` is used directly in
  ## comparison arithmetic throughout, e.g. `q == start + 3`; stamping it
  ## turned every such site into a fresh fork, compounding across the many
  ## sites one query touches). See `runSymexImpl`'s own comment at that site
  ## for the full writeup; `SymVal.ziWidth`'s doc comment lists the sites
  ## that DO stamp it.
  ## R2 (post-0.4.0 remediation slice, zero-default result binding, S3,
  ## 2026-08-21/22): v86 fixed one false-`sxSat` generator — a callee
  ## reaching an IMPLICIT fallthrough (no explicit `return`) after
  ## CONDITIONALLY assigning `result` left `retSym` totally unconstrained at
  ## the call site — by binding `retSym` via `retBindEq` whenever
  ## `cp.env.hasKey("result")`, i.e. whenever the path actually ASSIGNED
  ## `result` somewhere along the way. But a callee path that never touches
  ## `result` AT ALL is equally legal Nim — `result` starts life zero-valued
  ## (Nim zero-initializes every `result` slot before the body runs: `0`,
  ## `""`, `false`, a zero-tuple, …) and stays that way if the path's own
  ## branch never assigns it (e.g. `proc f(x: int): int = (if x > 0: result =
  ## x)` — the `x <= 0` path returns `0`, never touching `result`). v86's
  ## `cp.env.hasKey("result")` guard routed such a path straight to the
  ## UNCHANGED `else: fallThrough.add cp` — `retSym` stayed exactly as free
  ## as it was before v86 existed, reintroducing v86's own false-`sxSat`
  ## shape for the never-touched case. Fix (`runtime.nim`'s `isCall` arm,
  ## the `else` twin of v86's `if cp.env.hasKey("result")` branch): bind
  ## `retSym` to `defaultZero(stmt.retTy, ...)` — Phase 14 A5's (ADR-0003
  ## D5) recursive type-driven zero-init, HOISTED this slice from its former
  ## `isVariantReassign`-local scope to module scope (just below
  ## `retBindEq`) so both call sites share the one constructor, per the "no
  ## parallel zero constructor" discipline — via the SAME `retBindEq` the
  ## assigned branch already uses. `defaultZero`'s `itSeq` arm gained ONE
  ## behavioral change while hoisting: an unbacked-element-type zero seq
  ## (e.g. a zero-valued `seq[(string,string)]` field nested inside a
  ## zero-bound tuple return) now builds an `isUnsupportedFieldPlaceholder:
  ## true` value via the SAME shape `allocateSym`'s `itSeq` placeholder arm
  ## uses, instead of calling `allocateSeqDataRaw` (which raises
  ## `SymexNestedSeqUnsupportedError` unconditionally for such an element
  ## type) — `retBindEq`'s `svSeq` arm already treats a placeholder value on
  ## either side as a sound no-op bind, so this composes correctly instead of
  ## crashing the whole walk over an untouched sibling path's zero value.
  ## `defaultZero`/`retBindEq` both still raise for a handful of composite
  ## kinds neither is wired for (float, nested variant, distinct, ref/ptr,
  ## non-string-keyed table, non-int64 hash set, and a genuinely-backed
  ## top-level `itSeq` return — `retBindEq`'s `svSeq` arm only binds a
  ## PLACEHOLDER value soundly, the same pre-existing scope limit the v86
  ## ASSIGNED branch already has) — the `isCall` arm catches these and
  ## degrades to the SAME classified `sxUnknown`
  ## ("composite-typed implicit-result fallthrough ... not yet wired",
  ## `feUnsupportedOp`) the assigned branch's `retVal.kind notin {...}` check
  ## already uses, never binding a value the walker cannot back soundly.
  ## Verdict-surface change: a previously-false `sxSat` for a query reachable
  ## only via an untouched-result path's free `retSym` now correctly reports
  ## `sxUnsat`; a query satisfied EXACTLY by the zero default now correctly
  ## reports `sxSat` instead of failing to distinguish it from any other
  ## value. `renderAsChoicesVersion` stays UNCHANGED (11) — no new
  ## witness-rendering shape; a zero-default witness renders through the
  ## exact same scalar/tuple/variant leaf renderers an assigned witness
  ## already uses. See `tests/tsymex_r6_r2_zerodefault_result.nim` for the
  ## RED/GREEN pins.
  ##
  ## R1 (post-0.4.0 remediation slice, placeholder read-totality
  ## chokepoint, 2026-08-21/22): v85-v88 introduced
  ## `isUnsupportedFieldPlaceholder` (a `svSeq` whose element type has no
  ## allocation backing, e.g. `seq[(string,string)]` — allocated with
  ## `seqLen` HARD-FORCED `== 0` and an inert data array, never legitimately
  ## selected from). A read of such a value must always CLASSIFIED-DECLINE
  ## (`seNestedSeqUnsupported`), never compute a verdict from the fake
  ## length/content — but the read-side guard set was hand-placed and
  ## incomplete, confirmed via two Critical soundness gaps:
  ##   S1 — `iekSeqLen`'s `of svSeq:` arm (the `.len` read, and every
  ##   for-loop's own bound check via the `for x in seq:` desugar, which
  ##   compiles to exactly this same `.len` read) returned
  ##   `SymVal(kind: svInt, zi: recv.seqLen)` with NO placeholder check —
  ##   a `p.options.len > 0`-style query was silently PROVEN against the
  ##   forced length 0 (a false `sxUnsat`).
  ##   N1 — `iekSeqSlice` read `recv.seqLen`/`recv.seqDataRaw` with no
  ##   check — a `ps[0 .. 0]`-style slice's own OOB bound was tautologically
  ##   violated under the forced `lenSym == 0` path condition, forking a
  ##   guaranteed-spurious `IndexDefect` and pruning the real continuation
  ##   (another false `sxUnsat`/`sxRaised`); WORSE, the returned slice
  ##   `SymVal` omitted the flag, so the taint was LOST and every downstream
  ##   consumer of the slice result was blinded to it.
  ## Both are now routed through a shared CHOKEPOINT
  ## (`placeholderReadDeclineMsg` + `declinePlaceholderInLower`, `runtime.nim`,
  ## just above `freshRetSym`) instead of two more hand-placed checks — the
  ## structural fix `isIndex`'s v88 guard alone did not provide. The
  ## `isIndex` guard itself is fixed too (Q2): its decline message omitted
  ## the `<loc>: ` prefix the SAME handler's non-seq-receiver decline 60
  ## lines below already uses, despite the parser already populating
  ## `stmt.ixLoc` — now shares `placeholderReadDeclineMsg` so both the
  ## walk-time (`isIndex`) and in-`lower()` (`iekSeqLen`/`iekSeqSlice`/
  ## `iekSeqAdd`) halves report one identical message/kind shape.
  ## `iekSeqAdd`'s mutation arm is ALSO routed through the chokepoint this
  ## slice (audited per the design requirement): pre-fix, `.add` on a
  ## placeholder (parsed unconditionally — `dsl_parser.nim`'s `.add` arm
  ## dispatches on receiver KIND only, not element backedness) fell through
  ## to a bare `raise ValueError` for the unbacked element kind, unwinding
  ## past every enclosing `seq[Path]` fork loop to `runSymexImpl`'s
  ## catch-all and poisoning the WHOLE run (`weInternalWalkerFault`) —
  ## exactly Bug #2's original failure mode. Every OTHER `seqDataRaw`/
  ## `seqLen`-touching site in `runtime.nim` was individually audited this
  ## slice and confirmed either already-safe (`retBindEq`'s `svSeq` arm,
  ## `extractFromSymVal`) or structurally unreachable for a placeholder
  ## receiver (e.g. `lowerHofCall`'s inline path requires a CONCRETE folded
  ## length, which a placeholder's fresh, un-narrowed `seqLen` var never
  ## folds to; its axiom `map` path declines on element-KIND mismatch before
  ## ever touching `seqDataRaw`; `renderContainerElemCell`'s witness arm
  ## early-returns on element kind, and a placeholder's `seqElemTy` is by
  ## construction never `itRef`/`itPtr`) — see the R1 slice's test file and
  ## handoff notes for the full audited-site table. Verdict-surface change:
  ## every one of these access forms over a placeholder moves from a false
  ## `sxUnsat`/`sxRaised` (S1/N1) or a whole-run-poisoning crash (`iekSeqAdd`)
  ## to an honest, branch-scoped `sxUnknown` carrying `seNestedSeqUnsupported`
  ## — hence the walker bump. `renderAsChoicesVersion` stays UNCHANGED (11):
  ## no new witness-rendering shape, only previously-false verdicts
  ## tightening to honest declines (a placeholder never contributed a
  ## witness leaf either side of this fix).
  ##
  ## Round-6 B7r2 (path-scope rider, 2026-08-16/17). B7's SECOND ATTEMPT
  ## isolated two of its three "readOptions doesn't compose" breakers
  ## (BLOCKER B7-1's if-wrap and downstream-construction shapes) to a
  ## SPECIFIC, narrower root cause than the RFC's own framing assumed
  ## (branch-scoped classified degrade): B6's pair-loop closed form
  ## (`iekStrInOptionRegion`) requires its start/bound operands `svInt`-
  ## represented (CR-17 discipline); `collectIntOffsetParams`'s existing
  ## promotion (`dsl_parser.nim`) only traces a loop counter back to a
  ## FORMAL PARAM through a bare-symbol rebind chain — a counter seeded
  ## directly from an INT LITERAL (`var pos = 2`, chapulin's own
  ## `decodeOackTwin`/`readOptions` real shape, header-length-checked then
  ## called at a fixed offset) has no param to trace to, so it stayed
  ## BV-allocated and failed the CR-17 check regardless of whether the loop
  ## was wrapped in a dispatch `if` or followed by construction — BOTH
  ## breakers, one cause. Fixed via a companion parse-time collector,
  ## `collectIntOffsetLiteralLocals` (`dsl_parser.nim`): a literal's value
  ## is already known at parse time, so re-representing it `svInt` instead
  ## of the type-driven BV default carries none of a param's def-use
  ## tracing risk — new `IRStmt.isLet.lIsIntOffsetLocal` field (parse-time,
  ## via `ctx.intOffsetLiteralLocals`), consulted by the `isLet` walker arm
  ## to select an `svInt` proto for a literal RHS. BLOCKER B7-1's THIRD
  ## breaker (call boundary: a helper proc RETURNING `seq[(string,string)]`,
  ## e.g. `readOptions` itself, poisons any caller merely BINDING the call's
  ## result, even when immediately discarded) was a DIFFERENT, independent
  ## gap: Bug #2's per-field scoped-decline placeholder
  ## (`isUnsupportedFieldPlaceholder`) was scoped to declared OBJECT/VARIANT
  ## RECORD FIELDS only (`classifyObjectRecordFields`) — a BARE
  ## local/param/call-return of an unsupported-element seq type (not
  ## embedded in a record field) still hit `allocateSeqDataRaw`'s
  ## unconditional raise. Generalized: `allocateSym`'s `itSeq` arm now
  ## takes the SAME placeholder branch whenever `not
  ## isBackedSeqElemTy(ty.seqElemTy)`, regardless of whether
  ## `seqUnsupportedFieldReason` was pre-set by the field-specific
  ## classifier; a NEW walk-time guard at `isIndex`'s `svSeq` case (the
  ## generalization's own read-safety companion, since a bare value has no
  ## static field-access site for `dsl_parser.nim`'s existing
  ## `nnkDotExpr`-based read-interception to catch) deposits the SAME
  ## SND-1 taint on an ACTUAL indexed read of such a placeholder instead of
  ## selecting from its arbitrary-sort inert backing array. Both fixes are
  ## real CAPABILITY upgrades (confirmed via isolated probes: a
  ## literal-seeded, if-wrapped pair-loop past the 5-iteration k-unroll
  ## horizon now proves via the closed form; a call-boundary
  ## `seq[(string,string)]`-returning helper's caller now reaches a target
  ## past the call without degrading), not merely crash-avoidance — pinned
  ## in `tests/tsymex_r6_b7r2_pathscope.nim`. BLOCKER B7-2 (a case-match
  ## over scanned content with an `else: raise` arm poisoning a DISJOINT
  ## sibling branch) is a THIRD, GENUINELY DIFFERENT mechanism (CR-2a's
  ## `feUnsupportedExprKind` on case-as-expression, unrelated to int
  ## representation or seq backing) that the RFC's own "branch-scoped
  ## classified degrade" architecture would address ARCHITECTURALLY — that
  ## approach (catching the classified-degrade exception family at the
  ## `isIf`/`isWhile`/`isCall` walk boundary and converting it to a
  ## per-path SND-1 taint, letting sibling branches keep exploring) was
  ## PROTOTYPED and found UNSOUND on this engine's C backend: wrapping any
  ## of those recursive `walk()` calls (which return `seq[Path]`, holding
  ## refcounted Z3-AST fields) in `try`/`except` — even a single,
  ## non-re-raising catch, at just one of the four sites — causes the
  ## underlying classified-degrade exception to never be raised at all
  ## (not corrupted-but-visible: `w.sawUnknown`/`w.walkDegradeErrors`
  ## verifiably never get set, confirmed via an in-band print immediately
  ## before `runSymexImpl`'s own verdict computation, reproduced identically
  ## whether catching the new common base type or catching one of the 19
  ## existing concrete types directly, and independent of `--forceBuild`/
  ## nimcache state) — silently flipping an honest `sxUnknown` to an
  ## UNSOUND `sxUnsat`. This is a NEW, more severe manifestation of the
  ## SAME pre-existing ADR-0020/CR-1c finding ("a per-`walk`-frame
  ## catch/re-raise... corrupted memory... a C-backend-only SIGSEGV") this
  ## codebase already recorded and architected AROUND (the single top-level
  ## `runSymexImpl` catch) — not a new discovery from scratch, but a
  ## confirmation that the constraint is stricter than "don't catch at
  ## EVERY frame": even ONE non-top-level catch around a `seq[Path]`-
  ## returning recursive call is unsafe on this toolchain (Nim 2.2.10-
  ## patched, C backend, ORC, `--exceptions:goto`, `--threads:on`).
  ## BLOCKER B7-2 and the fully-general "sibling survives an unmodeled
  ## branch" architecture therefore remain UNFIXED this slice — see the
  ## handoff's BLOCKER entry for the minimal repro and the escalation.
  ## `tests/tsymex_r6_b7r2_pathscope.nim` pins B7-2's shape as an
  ## UNCHANGED, honest classified decline (a regression trip-wire, not a
  ## claimed fix). `renderAsChoicesVersion` is UNCHANGED (11) — no witness
  ## CONTENT changes; both landed fixes are proof/reachability capability
  ## upgrades over previously-crashing/poisoning shapes, not extraction
  ## changes.
  ## Round-6 A6-rider (2026-08-16, required precursor to Track B's B7).
  ## Chapulin's BLOCKER #12 ("`seq[byte]` witness extraction loses fidelity
  ## through a helper-proc read — an otherwise-genuine `sxSat` reports an
  ## all-zero witness") turned out, on isolated bisection
  ## (`tests/tsymex_r6_a6r_callwitness.nim`), to be the visible SYMPTOM of a
  ## deeper SOUNDNESS gap, not a pure witness-extraction/rendering issue:
  ## `runtime.nim`'s `isCall` arm allocates a fresh, unconstrained `retSym`
  ## for every call and binds it to the caller's `stmt.retName` for BOTH
  ## kinds of callee exit — an explicit `return expr` (correctly tied to
  ## `retSym` via `retBindEq`, in the `isReturn` arm) and an IMPLICIT
  ## fallthrough after a CONDITIONAL, multi-statement `result = expr`
  ## assignment (`parseCalleeImpl`'s own documented "general parser path" —
  ## a proc whose Nim-source body isn't a single bare `result = expr`
  ## expression lands there, per its comment: "Procs with conditional /
  ## multi-step result-assignment ... need cycle-2 work to model `result` as
  ## a mutable binding"). The fallthrough case was NEVER given the
  ## equivalent binding — `retSym` reached the caller totally free, so Z3
  ## was free to satisfy any downstream comparison against it independent of
  ## what the callee's body actually computed from its arguments. Confirmed
  ## as a genuine false-positive generator, not merely cosmetic: a
  ## deliberately-UNREACHABLE target (whose impossibility depends
  ## structurally on the callee's own `seq[byte]` argument read) proved a
  ## false `sxSat` pre-fix. The closure-call path
  ## (`applyClosureGround`/`assertArm`) already binds this exact shape
  ## correctly via `retBindEq(funcApp, cp.env["result"])`; the fix mirrors
  ## that established idiom into the ordinary call-inlining `isCall` arm —
  ## every implicit-fallthrough exit path with a bound `result` now asserts
  ## `retSym == result` (through the same `reconcileInt` cross-representation
  ## bridge `isReturn` uses) before joining the call's survivors; a
  ## composite (non-scalar-wired) `result` kind degrades in-band to a
  ## classified `sxUnknown`, mirroring `isReturn`'s own existing degrade net,
  ## rather than crashing. Verdict-surface change: any SUT whose provable
  ## outcome depended (knowingly or not) on this gap can change — most
  ## visibly, a previously-reported `sxSat` for a target only reachable
  ## through the unconstrained `retSym` now correctly reports `sxUnsat`
  ## (confirmed sound: no case observed where a genuinely-reachable target
  ## flips away from `sxSat`). The regression sweep (mandated for this
  ## slice) is the authoritative check that no other corpus entry relied on
  ## the gap. `renderAsChoicesVersion` bumps in lockstep, 9→10 (see above) —
  ## content for every affected already-`sxSat` witness changes from
  ## solver-free garbage to the value the (now-sound) proof actually
  ## depends on.
  ## Round-6 Bug #2 (scoped decline with read-taint, ADR/RFC fork-resolution
  ## 2026-08-15). `classifyObjectRecordFields` (`dsl_typebridge.nim`) was
  ## EAGER and WHOLE-TYPE: a declared object/variant field whose type is
  ## structurally unsupported for allocation backing (`seq[T]` with an
  ## unbacked element kind, e.g. `seq[(string,string)]`, mirroring
  ## `allocateSeqDataRaw`'s backed set) made `allocateSym` raise
  ## unconditionally whenever the TYPE was merely allocated — a parameter, a
  ## call-return placeholder, a local — regardless of whether the offending
  ## field/arm was ever touched, discarding any already-found `sxSat`/
  ## `sxUnsat` verdict for the WHOLE run (confirmed minimally: an unused
  ## variant arm carrying `seq[(string,string)]` alone flipped a clean
  ## `sxUnsat` to `sxUnknown`). Fixed with a per-field SCOPED DECLINE: such a
  ## field now classifies to a KIND-MARKED placeholder
  ## (`isUnsupportedFieldPlaceholder`, `types.nim` — extends R8's
  ## `unsupportedFieldPlaceholder` precedent from "omitted constructor field"
  ## to "declared field type" scope); `allocateSym`'s `itUninterp` arm
  ## (`runtime.nim`) allocates it as a FRESH OPAQUE value (never raises);
  ## `dsl_parser.nim`'s `nnkDotExpr` field-read arms detect the placeholder
  ## and deposit an SND-1 `isUnsupported` taint on THAT READ's own statement
  ## instead of building a real accessor, so only paths that actually READ
  ## the poisoned field degrade to a classified `sxUnknown` — untouched arms/
  ## fields prove exactly as before; `retBindEq`'s new `svUninterpRef` arm
  ## SKIPS the eq constraint on such a field (no-constraint is a sound
  ## over-approximation, the read-taint owns honesty). Verdict-surface
  ## change: previously-degraded `sxUnknown` verdicts for procs allocating
  ## (but not reading) such a field can now honestly TIGHTEN to their real
  ## `sxSat`/`sxUnsat` — cached pre-85 `sxUnknown` entries for these SUTs must
  ## not be reused, hence the bump. `renderAsChoicesVersion` stays unchanged
  ## — no new witness shape (the placeholder never contributes a witness
  ## leaf; a read of it forces `sxUnknown` before any witness would be
  ## extracted). Modeling `seq[(string,string)]` CONTENT remains the
  ## recorded non-goal; lazy per-arm classification was considered and
  ## rejected (strictly dominated by the scoped-decline design).
  ##
  ## Round-6 B6 (ADR-0028 leg, option-region membership — the `readOptions`
  ## pair-loop). New `tryRecognizePairLoopIdiom`/`tryMatchPairLoopIdiomShape`
  ## (`dsl_parser.nim`) — a FOURTH sibling of Q1/B0's `tryRecognizeScanIdiom`,
  ## B3's `tryRecognizeScanPairIdiom`, and B4's `tryRecognizeAccumulatingScan`:
  ## recognizes chapulin's `readOptions` idiom, a while loop that re-invokes a
  ## B4-recognized (`readCString`-shaped) helper TWICE per iteration, CHAINED
  ## (the second call's start is the first call's own returned offset, B5's
  ## own chaining machinery), breaking on an empty key and accumulating
  ## `(key, val)` pairs into a `seq[(string,string)]`. Rather than k-unrolling
  ## this cross-iteration-state loop (the ADR-0028 Q2 residue class — no
  ## finite k decides a query over an unconstrained trip count), the whole
  ## loop is replaced with a two-way fork on a NEW region-membership
  ## predicate (`iekStrInOptionRegion`, `types.nim`/`runtime_strings.nim`):
  ## `s[i .. bound-1] ∈ ((nonzero)* "\0")*`, built directly from nim-z3's
  ## sequence-regex primitives (`range`/`star`/`concat`/`matches` — the SAME
  ## machinery `iekStrStrip` already uses for `(union chars)*`). STAR inner
  ## segments, not plus (round-2 depth correction, RFC-chapulin-hardening
  ## B6): the real `readCString` returns "" freely and `readOptions` accepts
  ## mid-region empty keys and all-empty values, with the canonical
  ## double-NUL terminator itself an empty segment — `plus` would reject
  ## exactly the well-formed inputs a property search generates. Membership
  ## is the LOOP-SAFETY invariant, not a per-pair functional-correctness
  ## claim: the MEMBER branch is a no-op (certified defect-free by
  ## construction — `itSeq[itTuple[string,string]]` has no backing in
  ## `allocateSeqDataRaw` this cycle, a recorded non-goal mirroring the A6
  ## exit-gate's own `seq[(string,string)]`-as-formal-param note, so `pairs`
  ## is never claimed to be anything in particular post-loop — sound per the
  ## RFC's own "no verdict depends on them" clause); the NON-member branch is
  ## the SAME `mkShortCircuitWhile` k-unroll fallback every unrecognized loop
  ## shape already takes — no new degrade machinery, so a truncated/
  ## non-member region reaches the pre-existing modeled ScanError raise arm
  ## (the inner B4 closed form, unchanged) via ordinary per-iteration
  ## walking. `renderAsChoicesVersion` stays unchanged — no new witness
  ## shape (the member branch touches no witness-bearing binding).
  ##
  ## Round-6 B5 (ADR-0028 Leg 1, chained scan composition — retires catalog
  ## finding #6). A SECOND lifted scan (B3/B4) whose start offset is a FIRST
  ## scan's own RETURNED result (`let (_, p1) = readCStringHelper(s, 0);
  ## discard readCStringHelper(s, p1)` — the catalog-#6 shape) degraded to
  ## `sxUnknown` even after B3+B4 landed: `retBindEq`'s fresh call-return
  ## placeholder (`freshRetSym` → `allocateSym`) allocates every `itInt`
  ## tuple field at its TYPE-DRIVEN BV default regardless of what the callee
  ## actually computes — `reconcileInt` (CR-9(c)) only widens the pair used
  ## IN THE EQUALITY CONSTRAINT itself, it never changes the caller's own
  ## env binding for the destructured local, so `p1` stayed BV-represented
  ## and failed `iekStrSubstr`'s CR-17 Int-sortedness check the moment it
  ## was passed on as a SECOND scan's offset argument. New
  ## `calleeIntOffsetReturnPositions`/`scanOffsetReturnPositions`/
  ## `offsetShapedElem` (`dsl_parser.nim`) trace which tuple positions (or a
  ## bare scalar) of a callee's OWN recognized B3/B4 closed form are
  ## genuinely Sequence-theory Int (`iekStrFind`'s own result), threaded
  ## onto the `isCall` IR statement (`IRStmt.retIntOffsetPositions`, new
  ## field — round-trips through `emitStmt`'s NimNode-literal
  ## reconstruction) so `allocateSym`'s `itTuple`/`itInt` arms allocate
  ## `svInt` directly at call-RETURN time, mirroring `IRParam.isIntOffset`'s
  ## existing TOP-LEVEL-param promotion at the other end of the data flow.
  ## Two companion gaps surfaced and closed in the same cycle: (1)
  ## `parseCalleeImpl` never set `IRParam.isIntOffset` for a CALLEE's own
  ## params (only `parseProc*`'s top-level entry loop did), so a LITERAL
  ## scan-offset argument (`readCStringHelper(s, 0)`) still shaped BV via
  ## `intLitProto`'s type-driven default even once the callee's own
  ## `collectIntOffsetParams` trace was available — `parseCalleeImpl` now
  ## computes the same trace for its own params, and the call-argument
  ## lowering site (`runtime.nim`) consults `formal.isIntOffset` to pick an
  ## svInt proto over `intLitProto`'s BV one; (2) purely additive — an
  ## untraced position keeps the pre-existing BV default unchanged, so this
  ## is a soundness-neutral precision gain, never a new degrade or a
  ## changed verdict for any already-decided shape. `renderAsChoicesVersion`
  ## stays unchanged — no new witness-serialization shape (a chained scan's
  ## `string`/`int` witnesses render exactly as any other already-modeled
  ## `string`/`int` param).
  ##
  ## Round-6 B4 (ADR-0028 Leg 1, accumulating-string scan sibling) — the
  ## `readCString` family closed form. New
  ## `tryRecognizeAccumulatingScan`/`tryMatchAccumulatingScanIdiomShape`
  ## (`dsl_parser.nim`), a THIRD sibling of Q1/B0's `tryRecognizeScanIdiom`
  ## and B3's `tryRecognizeScanPairIdiom` — B3's early-return-on-match shape
  ## with a third body statement that accumulates the pre-terminator bytes
  ## into a string as the loop advances (`while i < s.len: (if s[i] == lit:
  ## return <expr>); acc.add(char(s[i])); inc i`). Lowers to the SAME
  ## `iekStrFind` 3-arg closed form (symbolic start), reusing B0's
  ## not-found/OOB split verbatim, plus one new binding for the accumulated
  ## payload: `<acc> = <acc's entry value> & iekStrSubstr(<s>, <i>, p - 1)`
  ## — the RFC's pinned inclusive-hi formula
  ## (`iekStrSubstr(s, offset, terminatorIx - 1)`), generalized with a
  ## leading concat of `<acc>`'s own entry value so the closed form stays
  ## sound without inspecting the loop's preceding statements (every corpus
  ## shape starts the accumulator empty, making the concat a no-op in
  ## practice). The found branch RE-PARSES the SUT's own `return <expr>`
  ## against BOTH an `i := p` and an `acc := payload` rebinding (B3's
  ## rebind-then-reparse technique, extended to a second variable), and only
  ## a bound that is syntactically the scanned string's own `.len` is
  ## accepted, mirroring Q1/B3's boundIsScannedLen discipline. Body
  ## statement count (1 vs 2 vs 3) makes the three recognizers mutually
  ## exclusive by construction — no cross-firing possible. Also fixes B1's
  ## flagged witness-reader gap: `readSeqUInt8` (`runtime.nim`) now routes a
  ## string-backed `seq[byte]` param's model value through `RawWitness.
  ## strVals` (where `svString`-allocated params actually land) before
  ## falling back to the `seqLens`/`uintVals` array representation, so a
  ## string-backed param's witness renders real byte content instead of
  ## silently degrading to an empty seq. Also adds `collectIntOffsetParams`
  ## (`dsl_parser.nim`, ADR-0027's recorded lift): the closed form's
  ## `iekStrSubstr` LOW bound must be `svInt` (its own runtime arm declines
  ## a BV-represented bound — the CR-17 non-termination class), so a top-
  ## level int param whose def-use reaches an accumulating-scan's index now
  ## allocates `svInt` instead of the `itInt` default (`bvVar`), traced
  ## through at most one local rebind AND one direct call boundary
  ## (`readCString`-shaped helpers are naturally called through a wrapper).
  ## This exposed a live CRASH the new per-param promotion made reachable
  ## for the first time — `overflowCond` (`runtime.nim`) reads a
  ## `svBV*`-only field off BOTH arithmetic operands once its caller
  ## confirms only the FIRST operand's kind/signedness, so a MIXED `svInt`/
  ## `svBV*` pair (a single promoted param's value combined with an
  ## ordinary BV-allocated sibling, e.g. a call's own BV-allocated return
  ## placeholder) hit `FieldDefect: field 'bv64' is not accessible ...`
  ## before this cycle — `lowerArith` now calls `reconcileInt` at its top,
  ## mirroring `lowerCmp`'s own existing call, closing the gap the same way.
  ##
  ## Round-6 B3 (ADR-0028 Leg 1, int-result scan sibling) — the `scanPair`
  ## shape. New `tryRecognizeScanPairIdiom`/`tryMatchScanPairIdiomShape`
  ## (`dsl_parser.nim`), a sibling of Q1/B0's `tryRecognizeScanIdiom` for
  ## the OTHER canonical scan idiom chapulin's twins use — an
  ## early-return-on-match scan (`while i < s.len: (if s[i] == lit: return
  ## <expr>); inc i`) rather than Q1's skip-while-and-clamp shape. Lowers to
  ## the SAME `iekStrFind` 3-arg closed form (symbolic start), with B0's
  ## not-found/OOB split reused verbatim: the whole form is guarded by loop
  ## entry (a zero-iteration loop leaves `i` untouched), an entry-read probe
  ## deposits the real IndexDefect fork a negative start raises, and only a
  ## bound that is syntactically the scanned string's own `.len` is
  ## accepted. The found branch RE-PARSES the SUT's own `return <expr>`
  ## against an `i := p` rebinding (not a syntactic substitution) so a
  ## `return (i, i+1)`-shaped result correctly reports the FOUND position;
  ## the not-found branch sets `i := bound` and falls through to whatever
  ## the caller placed after the loop (typically a `raise`), unaffected —
  ## no cross-statement recognition needed. Same two type gates as Q1
  ## (itString receiver, char-literal delimiter); NOT widened to a
  ## `seq[byte]` string-backed receiver this slice (B1 scoped that
  ## explicitly out — "scan-lift NOT widened to seq[byte] receivers").
  ## Upgrades `tsymex_retest_c6_tuple_chain`'s `destructurePair` pin from
  ## `beBudgetExhausted` (k-unroll residue) to a real `sxUnsat` proof — no
  ## IndexDefect is reachable through the closed form at all. Verdict-
  ## changing for any SUT matching the new shape, so the cache key rotates
  ## (`Ver: SW`). Standing-DoD clause (d) applied at all three new
  ## `classifyType` call sites (`typeKind != ntyNone` guard) — caught DURING
  ## this slice's own regression sweep, not left latent: the shape's plain
  ## `<` guard (not and-shaped, unlike Q1's) matches an iterator's own `while
  ## i < n: yield ...; inc i` too, and `classifyType` on that guard's
  ## operands crashed with the exact "node has no type" class A5 fixed
  ## (`tsymex_phase15_N3_scan_boundary`'s `iterLambdaReturn`); fixed by
  ## reordering the purely-structural body-shape checks BEFORE any
  ## `classifyType` call (narrows to genuine candidates first) plus the
  ## guard itself, belt-and-suspenders.
  ##
  ## "80" — Round-6 B2 rider (control-loop review, same day) — the `byte` alias.
  ## `byte` is a plain (non-distinct) alias for `uint8` in `system`, but
  ## Nim's typed AST preserves the ALIAS SPELLING (`classifyType` already
  ## carries its own dedicated `"byte"` text-match arm, `dsl_typebridge.nim`,
  ## for the identical reason), so B2's `intTyNames`-based recognizer missed
  ## it — including the RFC's own PRIMARY consumer shape, `uint16(b) shl 8`
  ## with `b: byte` (chapulin `protocol.nim:93`, `b` off a `seq[byte]`),
  ## which fell through to the untouched pre-B2 identity pass-through. New
  ## `normalizeIntTyName` (`dsl_parser.nim`) maps `"byte"` -> `"uint8"`
  ## before every `intTyNames`-driven lookup in the `nnkConv` B2 arm
  ## (membership via the new `isIntFamilyName`, width/signedness via the
  ## existing `intTyWidth`/`intTySigned`); no other stdlib alias resolves
  ## into the int family this way (`Natural`/`Positive` are RANGE types, not
  ## plain aliases, and keep their existing unrelated `classifyType`
  ## handling). Also adds the standing-DoD clause-(d) `typeKind != ntyNone`
  ## guard around `declineIntWidthConv`'s `classifyType(n)` call (harmless
  ## when the assumption holds, as it does for every `nnkConv` node reached
  ## here today — added defensively per the A5 precedent, not because a
  ## live gap was found). Verdict-changing: a `byte`-typed source in a
  ## widening conversion now resolves to a real verdict (was the pre-B2
  ## identity pass-through, wrong width); a `byte`-typed NARROWING target
  ## now declines cleanly (was the same silent-unsound pass-through) instead
  ## of the classified decline every OTHER int-family narrowing already got
  ## at v79 — so the cache key rotates (`Ver: SW`).
  ##
  ## "79" — Round-6 B2 (ADR-0028 Leg 2) — int-family WIDTH-CONVERSION modeling,
  ## WIDENING ONLY (`iekConvIntWidth`). `parseExpr`'s `nnkConv` arm
  ## (`dsl_parser.nim`) now recognizes a conversion between two DIFFERENT
  ## `intTyNames` members (`uint16(b)` call syntax and `b.uint16` method
  ## syntax both desugar to the identical shape) and dispatches on
  ## width/signedness: WIDENING (`ciwTgtWidth > ciwSrcWidth`) lowers to a
  ## `zeroExtend`/`signExtend` keyed on the SOURCE value's OWN signedness
  ## (`ciwSrcSigned` — `uint8→int32` zero-extends, a signed source
  ## sign-extends) at plain `binBV` in the widened width; the result
  ## SymVal's `signed` flag takes the TARGET type's signedness
  ## (`ciwTgtSigned`), so downstream arithmetic/compares on the converted
  ## value are correct. `probeProto` returns a matching BV sentinel at the
  ## WIDENED width/signedness (the exact `iekConvFloatToInt` stale-proto
  ## crash class this mirrors defensively — see "14" below). CR-1a's
  ## `svIntToBV` bridge is untouched. NARROWING (`uint8(x)` truncation) and
  ## SAME-WIDTH signedness REINTERPRET (`uint32(x)` from an `int32`) are
  ## RECORDED DECLINES (classified `feUnsupportedExprKind`, never a crash
  ## and never the old silent-unsound identity pass-through): the pre-B2
  ## pass-through left the value unmasked / a stale `signed` flag steering
  ## signed-vs-unsigned compares. `nnkHiddenStdConv` is untouched (stays a
  ## blind pass-through — out of scope, zero corpus need). Verdict-changing
  ## for any SUT converting between two differently-widthed fixed-width int
  ## types: a previously wrong-verdict-risking (widening) or previously
  ## silently-unsound (narrowing/reinterpret) construct now resolves to a
  ## real verdict or a classified decline respectively, so the cache key
  ## rotates (`Ver: SW`).
  ##
  ## "78" — Round-6 B1 (+B1a, ADR-0028 Leg 1) — string-backed `seq[byte]` params.
  ## `ParseCtx.stringBackedParams` (populated by
  ## `collectStringBackedByteSeqParams`, `dsl_parser.nim`, a parse-time
  ## pre-pass run BEFORE the body walk per Leg 1's round-2 correction)
  ## recognizes a `seq[byte]` PARAM as string-backed when some loop in the
  ## proc body matches the SAME scan-idiom shape check
  ## `tryRecognizeScanIdiom` uses (`tryMatchScanIdiomShape`, extracted so
  ## the classifier and the closed-form recognizer share one predicate by
  ## construction) with a byte-range literal delimiter, minus any param
  ## with a mutation site (`data[i] = x` / `.add`/`.del`/`.insert` — Z3
  ## String is immutable, so a mutated param stays array-modeled). A new
  ## `IRParam.isStringBacked` field (the `isVar` idiom) carries the choice
  ## to `allocateSym`, which allocates such a param via the itString
  ## machinery (ADR-0006 byte-range constraint) plus the itSeq arm's own
  ## `[0,1024]` length ceiling. `parseExpr`'s bracket-expr/call-form `[]`
  ## and `.len` dispatch for an `itSeq` receiver (previously two DUPLICATE
  ## sites each for slice/index and for `.len` — bracket-expr vs
  ## call-form) collapse into one shared helper each
  ## (`parseSeqBracketAccess`/`parseSeqLenAccess`) so the string-backed
  ## dispatch cannot diverge between spellings: a string-backed receiver's
  ## `data[a..b]` routes to `iekStrSubstr`, `data[i]` to `iekStrAt`,
  ## `data.len`/`len(data)` to `iekStrLen`. Walker totality backstops
  ## (live crash gaps, independent of dispatch correctness): the `isIndex`
  ## walker arm's hard `doAssert arrSV.kind == svArray` and `iekSeqLen`'s
  ## bare `ValueError` on a non-container receiver both gain an `svString`
  ## arm (routing to the same OOB-probe/read logic `iekStrAt`/`iekStrLen`
  ## use — this is what makes `data[i]`/`data.len` WORK, not merely not
  ## crash, through a call-chain hop whose own parse never routed the
  ## dispatch) plus a classified decline (`feUnsupportedExprKind` via the
  ## existing `SymexClassifiedDegradeError` carrier) for any other
  ## unexpected kind, so a mis-classified receiver can never crash.
  ## Verdict-changing for any SUT with a `seq[byte]` param consumed by a
  ## qualifying scan loop: previously-crashing `data[4 .. ^1]`/`data.len`
  ## shapes on such a param now resolve to real verdicts, so the cache key
  ## rotates (`Ver: SW`).
  ##
  ## "77" — Round-6 A3 (ADR-0029) — `isVariantConstructSym`: fork-per-tag
  ## SYMBOLIC-discriminant variant CONSTRUCTION, cloning
  ## `isVariantReassignSymbolic`'s fork-per-tag shape with the deliberate
  ## divergence that every declared arm's fields allocate FRESH per fork
  ## (construction has no "active arm" data — Nim itself only accepts a
  ## non-constant discriminant in constructor syntax when no arm-specific
  ## field is set). Parse-time `case`-branch tag-set narrowing (lexical,
  ## per-proc-body, never crossing a call boundary); a new
  ## `maxVariantConstructorForks` structural budget (default 8) classifies
  ## a `beBudgetExhausted` decline past it, carrying a parse-time-captured
  ## `vcsLoc` (file:line:col + `n.repr`) rendered verbatim into the
  ## walk-time message. Verdict-changing: A1's prior symbolic-disc decline
  ## pin (`tsymex_r6_a1_variantlit.nim` A1-6) now constructs — a sound
  ## capability upgrade, migrated deliberately (mirrors the SND-4
  ## migration precedent). Previously-`sxUnknown` symbolic-disc
  ## constructions now resolve to real `sxSat`/`sxUnsat` (below budget) or
  ## a classified decline (at/above it), so the cache key rotates (`Ver: SW`).
  ##
  ## Round-6 A2 (ADR-0029) — `retBindEq` gains an `svVariant` arm: the
  ## GENERAL encoding `discEq ∧ (⋀ declared arms: disc==tag → per-field
  ## eq) ∧ plain-field eq`. Wires a variant-returning callee (previously
  ## fell through `retBindEq`'s composite catch-all, degrading the
  ## caller's path to classified `sxUnknown` via the isReturn scalar-raise
  ## drain's kind allow-list) — sound for BOTH a freshly-pinned literal
  ## construction (A1's `iekVariantLit`) and a pass-through return of a
  ## variant-typed PARAMETER (genuinely symbolic discriminant; the per-arm
  ## IMPLICATION guard, not a bare conjunction, is what keeps that case
  ## sound). Verdict-changing for any SUT whose target proc returns a
  ## variant object: previously-`sxUnknown` callers now resolve to real
  ## `sxSat`/`sxUnsat`, so the cache key rotates (`Ver: SW`).
  ##
  ## "75" — Round-6 A1 (ADR-0029) — `iekVariantLit`: literal-discriminant variant
  ## object construction. `dsl_parser.nim`'s combined `of itVariant,
  ## itMultiVariant:` P2b decline arm is SPLIT: a LITERAL-discriminant
  ## `itVariant` constructor now builds a real `svVariant` (disc pinned to
  ## the literal tag, active arm's fields from the parsed exprs, every
  ## other arm allocated fresh-unconstrained); `itMultiVariant` keeps
  ## declining verbatim in its own retained arm. A symbolic discriminant
  ## and a ref-object-ALIASED variant constructor (ADR-0022 D#1 shape;
  ## ADR-0029 "deliberately not covered") both keep declining cleanly too.
  ## Verdict-changing for any SUT constructing a literal-discriminant
  ## value-object variant: previously-`sxUnknown` constructors now resolve
  ## to real `sxSat`/`sxUnsat`, so the cache key rotates (`Ver: SW`).
  ##
  ## "74" — Round-6 A0 — fold `low(T)`/`high(T)` int magics at parse time
  ## (`dsl_parser.nim`'s `nnkCall` arm, before `earlyClosureCallDetect` and
  ## the generic user-proc fall-through). Fixes the v69-round discovered
  ## fault: a `.magic`-pragma intrinsic like `low`/`high` has no body for
  ## `ensureProcRegistered`/`earlyClosureCallDetect`'s `getImpl` probing to
  ## fetch, so any prior parse of `low(int32)`/`high(int32)` inside a symex
  ## target produced a walker fault where the equivalent literal spelling
  ## proved clean. A concrete int-family type argument now folds to its
  ## literal `mkIntLit` bit pattern at parse time (same encoding every other
  ## int literal in this parser already uses); a non-int-family type/value
  ## argument declines cleanly instead. Verdict-changing for any SUT using
  ## the magic-call spelling: previously-faulting `low`/`high` calls now
  ## resolve to real verdicts, so the cache key rotates (`Ver: SW`).
  ##
  ## "73" — RFC-parser-normalization A2a — the `parseAtomicOperand` chokepoint
  ## (#146/#149, D2). Atomizes operands of the clean general infix family
  ## (comparisons, arithmetic, shl/shr, xor), the borrow/rune-compare/
  ## nil-compare/pred-succ/string-concat bypass sites, and the two
  ## `nnkPrefix` arms (`not`, unary minus) — never the boolean bAnd/bOr
  ## path (constraint 1; A2b's scope) and never inside a while-guard
  ## condition parse (constraint 4, `ctx.inGuardCond`). Bumps for CACHE-KEY
  ## reasons, not verdict reasons: `canonicalize.nim` renders locals as
  ## positional slots, so inserting a hoisted `isLet` renumbers every
  ## subsequent local — the cache key changes for every program with a
  ## compound operand of a non-short-circuit op anywhere, even where the
  ## verdict is unchanged (RFC §Cache-key honesty). Expect broad one-time
  ## witness-cache staleness on this bump.
  ## "73" — RFC-parser-normalization A2b (#146/#149, D2). Classify-first
  ## restructure of the bAnd/bOr block: the boolean-vs-bitwise decision now
  ## precedes both operand parses, so the BITWISE and/or family (no
  ## short-circuit semantics in Nim) atomizes its operands through the same
  ## `parseAtomicOperand` chokepoint A2a gave the general infix family. Same
  ## cache-key-only rationale as "72" — canonicalize's positional-slot
  ## rendering renumbers on any newly-hoisted `isLet`, so the key changes
  ## for every program with a compound bitwise and/or operand, even where
  ## the verdict is unchanged. The boolean short-circuit path (D1c) is
  ## untouched verbatim, so boolean-only programs' keys do not move.
  ##
  ## RFC-parser-normalization N0 — complete the #147 `nnkFuncDef` widening
  ## (three missed kind gates, `dsl_parser.nim`): `borrowInfoFor` (:855)
  ## gated on bare `impl.kind != nnkProcDef`, excluding a `func` `{.borrow.}`
  ## operator from the borrow path (verdict/witness-inert in isolation — see
  ## the site's own comment — so this widen alone would not have forced a
  ## bump); C3 proc-as-value (:1048/:1050) gated on `symKind(n) == nskProc`
  ## (`func` symbols are the distinct `nskFunc` kind), so a `func`-valued
  ## capture (`let g = someFunc`) fell to bare `mkVar`, producing an
  ## unbound-env `KeyError` at walk time classified `weInternalWalkerFault`
  ## -> `sxUnknown`; G8 string-op disambiguation (:2083) gated positively on
  ## `calleeSym.getImpl.kind == nnkProcDef`, so a user `func` with a
  ## string-typed first param fell through to the generic string-receiver
  ## path and registered a false `seUnsupportedStringOp` degrade -> also
  ## `sxUnknown`. All three widen to `{nnkProcDef, nnkFuncDef}` /
  ## `{nskProc, nskFunc}`. The C3 and G8 fixes turn a classified `sxUnknown`
  ## into a real verdict for previously-degraded `func` programs — a
  ## verdict-surface change, so the cache key rotates (`Ver: SW`).
  ##
  ## Round-6 B0 — scan-lift bound soundness (hotfix): the v60 Q1 lift
  ## accepted ANY int bound and rewrote to Z3 `str.find`, which returns -1
  ## for out-of-range starts instead of raising — a false `sxUnsat` under
  ## tIndexError for `bound > s.len` and negative-start shapes (LIVE since
  ## v60; found by the round-6 architect review). v70 accepts only a bound
  ## that is syntactically the scanned string's own `.len` (other bounds
  ## fall through to k-unroll's honest SND-4 forks) and prepends a guarded
  ## entry-read probe so a negative start deposits the real IndexDefect
  ## fork. Verdict-changing: previously-false sxUnsat becomes sxRaised.
  ##
  ## v69 — Round-5 sello fixes (three verdict-changing repairs):
  ## 1. Literal-width protos (sello #1): a bare `iekIntLit` at a binding,
  ##    assignment, or call-argument site is shaped at the DECLARED width
  ##    (isLet lty / assign target's current rep / formal's ty) instead of
  ##    the svBV64 default — ends the bv32/svBV64 confusion that crashed
  ##    overflowCond (FieldDefect) and binBV (width doAssert) on branch-
  ##    merged int32 locals and chained int32 callees. Genuine defects
  ##    previously masked by the crash now surface (e.g. int32 underflow).
  ## 2. bool→int conversion (sello #3): `int32(b)` A-normalises to a 1/0
  ##    if-statement at the conversion's width (was a pass-through leaving
  ##    svBool where negBV/lowerArith need an int kind — the ref10 mask
  ##    idiom `-int32(b)` now proves).
  ## 3. svTuple retBindEq (sello #2): tuple-returning callees bind
  ##    structurally per field (recursive, int-reconciled) — the v64
  ##    catalog-#6 `feUnsupportedOp` drain degrade is retired for tuples;
  ##    walks proceed past the bind to the real decidability boundary.
  ##
  ## v68 — Round-5 discard totality: `discard <expr>` is WALKED, not dropped —
  ## every discarded expression lowers to a synthetic sink `let`
  ## (`discardSink`), so its raise/defect forks are searched exactly as a
  ## bound use would be. Previously only an allowlisted handful (E8
  ## exception intrinsics, M2 parseInt/parseBiggestInt) lowered; everything
  ## else dropped to `mkBlock(@[])`, leaving `discard f(x)` verdicts
  ## vacuously narrow (the chapulin round-4 CRITICAL finding — the callee
  ## was never walked). Verdicts can change: previously-vacuous `sxUnsat`
  ## may honestly become `sxRaised`/`sxUnknown` where the discarded
  ## expression carries defect forks or unmodeled constructs.
  ##
  ## v67 — Round-4 dev item 1 (seq-slice VALUES): `data[a..b]` / `data[a ..< b]`
  ## as a VALUE — previously EITHER a macro-time compile abort
  ## (`getImpl`-inlining system's `[]` died on its `len` callee) in value
  ## position, OR silently DROPPED in `discard` position (the earlier
  ## "slices prove on HEAD" ledger note was THAT artifact — vacuously
  ## sxUnsat, retracted in the round-4 ledger). v67 models the slice as an
  ## ARRAY-LAMBDA VIEW (`iekSeqSlice`): `len = hi - lo + 1`, `data =
  ## (lambda (i) (select base (+ i lo)))` — element-sort-generic,
  ## quantifier-free, copy semantics free (the lambda closes over the
  ## base's array AST at slice time). OOB deposits a REAL IndexDefect fork
  ## via the SND-4 sink. Bounds follow ADR-0027 (svInt proto; BV bound
  ## declines classified). Also: `ensureProcRegistered`'s unresolvable-
  ## `getImpl` macro `error()` — the last §0 clause-(b) wall on this path —
  ## now degrades classified (`feUnsupportedOp` + a never-registered key →
  ## the missing-callee arm). Two further routing walls fixed en route:
  ## system's slice `[]` takes an OPENARRAY receiver (hidden-conversion
  ## unwrap, the v65 `contains` precedent) and `^k` does NOT pre-expand
  ## for seqs (stays `BackwardsIndex(k)`; rewritten to `len(base) - k`).
  ## OWNERSHIP LESSON (cost a debug cycle): under a refcounting Z3 context
  ## an rc-0 node returned by one API call may be freed by the NEXT call —
  ## the view's select node briefly lived raw across two calls, a
  ## use-after-free surfacing as a SIGSEGV in `Z3_dec_ref` at scope
  ## teardown (EATEN by the v64 solve fiber until reproduced with
  ## `-d:symexNoBigStack --stackTrace:on`). Every intermediate raw is now
  ## wrapped (inc_ref'd) immediately. Verdict-surface change: seq-slice
  ## value shapes move from compile-abort/vacuous-drop to real proofs with
  ## defect-fork honesty. `renderAsChoicesVersion` STAYS "7".
  ##
  ## ---- v66 note (kept for the version ledger) ----
  ## Round-4 Slice A (soundness): a let/var-BOUND string slice
  ## (`let t = s[0 ..< i]`) arrives at the string `[]`-call route as
  ## `nnkHiddenStdConv(HSlice…, infix)`; the former shape-only `nnkInfix`
  ## test fell through to the single-CHAR path, mis-lowering the binding as
  ## `s[dummy]` (svBV8). Every downstream string op then degraded
  ## (requireStr), and two such mis-lowered slices would compare as
  ## FIRST-CHAR equality — a wrong-verdict hazard. v66: unwrap hidden
  ## wrappers, then dispatch on the index's TYPE — int → char read;
  ## recognizable `..`/`..<` range → `iekStrSubstr`; anything else →
  ## CR-2a classified degrade (never a char mis-read). Verdict-surface
  ## change: bound string slices move from degrade/mis-lowering to REAL
  ## substring proofs.
  ## ADR-0027 (same landing): `iekStrSubstr` bounds must be Int-sorted —
  ## a BV-represented bound (free int param) would bv2int-bridge into
  ## Sequence theory, an empirical Z3 non-terminator on the UNSAT side
  ## (> 3 h, bisected); such bounds decline classified. Bounds from
  ## find/len/literals (the field-realistic class) prove.
  ## Round-4 Slice B (same landing, ADR-0026): `strutils.strip` with a
  ## literal flag/char-set spec is MODELED as quantifier-free decomposition
  ## constraints over per-occurrence fresh strings (`iekStrStrip`, the
  ## `stripDecompConds` global sink) — chain AND bound-across-statements
  ## shapes move from sxUnknown to real verdicts (the dominant chapulin #9
  ## instance). Non-literal specs degrade classified.
  ## `renderAsChoicesVersion` STAYS "7".
  ##
  ## ---- v65 note (kept for the version ledger) ----
  ## Chapulin round-4 backlog item 1 (the round-3 Defect net's first field
  ## catch): CHAR needles for the string-search family. `s.find(']')`,
  ## `s.rfind(':')`, `s.contains('x')`, `startsWith`/`endsWith` char
  ## overloads all lower the needle as svBV8 (S3's char repr) and crashed
  ## the former bare `doAssert sub.kind == svString` at the
  ## `runtime_strings.nim` needle sites (uncaught AssertionDefect —
  ## observed as `weInternalWalkerFault` on the real `parseTftpUri`).
  ## Fix: `needleAsStr` bridges a BV8 char to the 1-char string via
  ## `(str.from_code codepoint)` — exact under the ≤0xFF byte-faithful
  ## constraint (ADR-0006); any other needle kind raises the classified
  ## `SymexUnsupportedStringOpError` (file precedent) instead of asserting.
  ## Also in v65 (same landing):
  ##   * `s.contains('@')`-class calls resolve through Nim's
  ##     string→openArray[char] implicit conversion (there is no strutils
  ##     (string, char) `contains`) — the parser now unwraps the
  ##     `nnkHiddenStdConv` receiver so they route to `iekStrContains`
  ##     instead of aborting in generic-openArray inlining.
  ##   * HashSet witness consistency (round-3 ledger gap, root-caused): a
  ##     symbolically-keyed membership (`s.len in hs`) is satisfiable by a
  ##     CONST-TRUE (universal) model array — nothing to enumerate, so the
  ##     finite witness rendered `{}` inconsistently. The membership KEY
  ##     TERMS are now recorded per set (`setMembershipKeyTerms`) and their
  ##     model values included in extraction; a store-chain harvest
  ##     (`harvestSetStoreKeys`) additionally surfaces stored keys.
  ## Verdict-surface change: char-needle searches move from native crash to
  ## correctly modeled; witness surface: set witnesses gain
  ## symbolically-keyed members (previously silently missing).
  ## `renderAsChoicesVersion` STAYS "7" — no new witness shape.
  ##
  ## ---- v64 note (kept for the version ledger) ----
  ## Chapulin 0.1.0 re-test triage (catalog #3 residual, CRASH class): 63→64.
  ## Nim spells boolean AND bitwise `and`/`or` with the same identifiers, so
  ## the D1c short-circuit lift (dsl_parser.nim) also fired for an INT-typed
  ## infix — `(uint16(data[o]) shl 8) or uint16(data[o+1])` with a
  ## defect-forking RHS bound its BV16 LHS into a `tBool()` temp and emitted
  ## `uNot(temp)`, crashing at the walker's `doAssert inner.kind == svBool`
  ## (uncaught AssertionDefect — reported by chapulin as runtime.nim:3155).
  ## Fixes, parser side: the short-circuit machinery is now gated on the
  ## infix expression classifying `itBool`; a bitwise `and`/`or` lowers as a
  ## plain binop with its RHS preamble hoisted unconditionally (faithful —
  ## Nim bitwise ops have no short-circuit). Runtime side (sibling audit of
  ## the assert-kind crash class): the `uNot` arm now lowers a BV operand
  ## via `notBV` (Nim prefix `not` on an int IS the bitwise complement) and
  ## SND-3-degrades any other kind; `lowerBool`'s chokepoint doAssert and
  ## the HashSet-membership key doAssert (svInt keys from `.len`/`parseInt`
  ## now bridge via `svIntToBV`, CR-1a precedent) degrade in-band instead of
  ## native-crashing.
  ## Also folded into the same v64 landing (chapulin re-test round 3, see
  ## docs/RFC-chapulin-hardening.md §Round-3 ledger):
  ##   * catalog #11 — Windows stack overflow (silent exit-255 class): the
  ##     solve now runs on a 16 MB fiber stack (`runSymexWithBigStack`,
  ##     `-d:symexNoBigStack` opts out; frame-state saved/restored around
  ##     the switch — the abandoned trampoline frame would otherwise leave
  ##     `framePtr` dangling into the freed fiber stack).
  ##   * catalog #6 — composite-typed retSym through the isReturn
  ##     scalar-raise drain: in-band `feUnsupportedOp` degrade instead of
  ##     `retBindEq`'s ValueError raise (the b7258f7-class in-walk raise
  ##     chapulin saw as a nondeterministic native crash).
  ##   * catalog #5(b) / Invariant 7 — `maxLoopUnwind` exhaustion and
  ##     `maxFrontierSize` prunes classify as the new tail-appended
  ##     `beBudgetExhausted`; a verdict-time backstop stamps any
  ##     still-unclassified sxUnknown `weInternalWalkerFault`.
  ##   * catalog #pred — `pred(x[,k])`/`succ(x[,k])` arithmetic passthrough
  ##     in the parser (unblocks `..<`-derived bounds).
  ##   * §0 clause (b) — an UNMODELED infix operator in expression position
  ##     (e.g. `a .. b` building an HSlice value in a call argument, seen on
  ##     the real `parseTftpUri`) now degrades CR-2a-style (classified
  ##     `feUnsupportedOp` parse error + `mkUnsupported` taint + typed zero
  ##     dummy) instead of `binopForInfix`'s macro-time `error()` abort.
  ## Verdict-surface change: shapes that previously CRASHED now
  ## prove/degrade honestly; previously-EMPTY sxUnknown `errors` now carry
  ## a classified kind; no previously-sound verdict changes.
  ## `renderAsChoicesVersion` STAYS "7" — no new witness shape.
  ##
  ## ---- v63 note (R2/R6, kept for the version ledger) ----
  ## RFC-chapulin-hardening R2 (CRITICAL soundness fix) + R6 (MEDIUM
  ## hardening), Q1 scan-idiom recognizer review: 61→62.
  ## `tryRecognizeScanIdiom` (dsl_parser.nim) matches
  ##   while <i> < <bound> and <s>[<i>] != <lit>: inc <i>
  ## and rewrites it to a closed form that evaluates `<bound>` ONCE at loop
  ## entry — but the only check on `<bound>` was a TYPE check (`itInt`), never
  ## a LOOP-INVARIANCE check. `while i < (n - i) and s[i] != 'z': inc i` has a
  ## REAL guard of `2*i < n` (the bound tightens every iteration as `i`
  ## grows), but was mis-lifted against the FIXED `bound = n` `n - i` happens
  ## to equal at loop entry (`i == 0`) — a silent WRONG VERDICT/WITNESS: the
  ## closed form can report an `i` value the real loop can never reach.
  ## R2 fix: after extracting `iNode` (the loop counter) and `boundNode` (the
  ## `<` guard's RHS), the recognizer now REJECTS the match
  ## (`refersToSym(boundNode, iNode)`) if `boundNode` refers to `iNode` at
  ## all. The body shape is already constrained to `inc <i>` / `<i> = <i> +
  ## 1` (i.e. `i` is the loop's ONLY mutated variable), so non-reference to
  ## `i` is both necessary and sufficient for `boundNode` to be
  ## loop-invariant. On rejection the caller falls through to the ordinary
  ## `mkWhile`/`mkGuardedWhile` k-unroll path — sound, just less precise
  ## (`sxUnknown` for trip counts beyond `maxLoopUnwind`).
  ## R6 fix (hardening, bundled in the same review cycle): "same variable as
  ## `i`" was matched via `.strVal` (the printed name) at three sites — the
  ## guard's `s[i]` index, the body's incremented variable, and (new) R2's
  ## `boundNode` reference check — which could false-match two DIFFERENT
  ## symbols sharing a printed name (e.g. a gensym'd template-injected `i`
  ## shadowing an outer loop `i`). All three sites now route through
  ## `sameSym(a, b: NimNode): bool`, which compares TRUE SYMBOL IDENTITY via
  ## the stdlib `macros.==(NimNode, NimNode)` (magic `EqNimrodNode`) —
  ## empirically confirmed (this Nim version, 2.2.10) to compare `true` for
  ## two references to the same binding and `false` for two distinct
  ## same-named bindings in disjoint scopes.
  ## Verdict-surface change: R2 makes the recognizer REJECT a shape it
  ## PREVIOUSLY (incorrectly) ACCEPTED — any SUT matching the
  ## counter-dependent-bound near-miss moves from a fabricated closed-form
  ## verdict to the sound k-unroll degrade. `renderAsChoicesVersion` STAYS
  ## "7" — no new witness shape, only a false lift removed.
  ##
  ## RFC-chapulin-hardening R1B (short-circuit OOB-guard fix), folded into the
  ## same v61 landing as R1 below (no further bump): `s[i]` (`iekStrAt`) and
  ## `parseInt(s)` (`iekStrToInt`) each deposit an inline defect-fork
  ## predicate EVERY time they lower (`strIndexOobConds`/`parseIntRaiseConds`,
  ## `runtime_strings.nim`). When such a node sat on the RHS of a
  ## short-circuit `and`/`or` (e.g. `i < s.len and s[i] == 'x'`),
  ## `rhsHasInlineDefectFork` (`dsl_parser.nim`) failed to self-report them,
  ## so D1c's short-circuit machinery took the FAST flat-`mkBinop` path
  ## instead of the GUARDED path — the OOB/raise fork fired UNGUARDED even on
  ## paths where the LHS made the RHS unreachable in real Nim (a false
  ## `sxRaised`). Fix, two parts: (1) `iekStrAt`/`iekStrToInt` now
  ## self-report `true` in `rhsHasInlineDefectFork`, forcing D1c's guarded
  ## path for once-evaluated arms (if/let/assign/return) — the fork now only
  ## fires under the LHS guard. (2) The guarded path emits a hoisted
  ## preamble that recomputes the guard; for a `while` guard this preamble
  ## was hoisted ONCE before the loop (stale after the first iteration), so
  ## the `nnkWhileStmt` arms (`dsl_parser.nim`) now restructure to `while
  ## true: <guard preamble>; if not cond: break; <body>` whenever the guard
  ## produced a hoisted preamble — re-running the guard (and its defect
  ## fork) every iteration, exactly as real Nim does. The fast path (no
  ## hoisted preamble) is untouched. Verdict-surface change: some previously
  ## false `sxRaised(IndexDefect)`/`sxRaised(ValueError)` verdicts now
  ## correctly resolve `sxUnsat`/`sxUnknown`/`sxSat`; genuinely unguarded OOB
  ## reads (no bounding `and`/`or`, e.g. an unbounded `while s[i] == ' '`)
  ## are UNCHANGED (still `sxRaised`, per R1 below). `renderAsChoicesVersion`
  ## STAYS "7" — no new witness shape, only false raises removed.
  ##
  ## RFC-chapulin-hardening R1 (CRITICAL soundness fix): 60→61.
  ## `lowerInExpr`/`lowerBoolInExpr` RESET the scalar-raise-fork sinks
  ## (`strIndexOobConds`/`parseIntRaiseConds`/`divByZeroConds`/
  ## `overflowConds`) at their own entry. FIVE statement arms lowered an
  ## expression through one of those procs but never called
  ## `drainScalarRaiseForks` afterward: `isWhile` (the loop guard),
  ## `isIndex` (both the dynamic `seq[T]` index expr and the static array
  ## index expr), `isVariantReassignSymbolic` (the symbolic-RHS disc expr),
  ## and `isReturn` (the return-value expr). Undrained, any raise predicate
  ## deposited by such an expression (`s[i]` OOB, `x div 0`, etc.) was
  ## silently DISCARDED — no raise fork opened, no bounds narrowing applied
  ## to the survivor — so a target reachable only PAST a real
  ## `IndexDefect`/`DivByZeroDefect`/`OverflowDefect`/`ValueError` was
  ## falsely reported `sxSat` with an impossible-in-real-Nim witness (an
  ## Invariant-3 soundness violation), and the raise itself was falsely
  ## `sxUnsat`/`sxUnknown` rather than `sxRaised`. Fix: each of the five
  ## sites now calls `drainScalarRaiseForks` immediately after its
  ## `lowerInExpr`/`lowerBoolInExpr` call and threads the returned
  ## survivor(s) forward — mirroring the already-correct `isLet`/`isAssign`/
  ## `isIf` arms exactly. Verdict-surface change: previously-dropped raises
  ## at these five sites now fork correctly, and their survivor
  ## continuations gain the implicit bounds/non-zero/non-overflow facts a
  ## sound model requires — a real soundness correction, not a new witness
  ## shape. `renderAsChoicesVersion` STAYS "7" — the fix removes false
  ## witnesses; it does not introduce a new rendered witness shape.
  ##
  ## RFC-chapulin-hardening Q1 (ADR-0025): 59→60. Verdict-surface change: the
  ## canonical bounded forward scan-to-literal-delimiter idiom
  ## (`while i < bound and s[i] != lit: inc i`) is now RECOGNIZED at parse
  ## time (`tryRecognizeScanIdiom`, dsl_parser.nim) and lifted to a
  ## closed-form `indexOf(s, lit, i)` — a program whose scan-loop-gated
  ## target previously degraded to `sxUnknown` (finite k-unrolling cannot
  ## decide a SYMBOLIC trip count) now resolves a REAL `sxSat`/`sxUnsat`/
  ## `sxRaised`. Dependent/chained scans (a later scan's start derived from
  ## an earlier scan's result) compose for free under the same rewrite.
  ## Bundled in the same slice: `iekStrFind` gained an optional 3rd `start`
  ## operand (`s.find(sub, start)` → Z3 `indexOf(s, sub, start)`, the closed
  ## form's foundation) — this ALSO fixes a latent unsoundness where a
  ## caller-written 3-arg `find` already parsed but silently DROPPED `start`
  ## at lowering (wrong verdict, not even a clean degrade). Anything off the
  ## exact recognized shape (`==`-guards, char-class/predicate scans,
  ## backward scans, non-`inc` bodies, non-char delimiters) is deliberately
  ## left UNRECOGNIZED and still degrades to `sxUnknown` exactly as before.
  ## `renderAsChoicesVersion` STAYS unchanged — no new witness shape
  ## (witnesses are strings/ints already rendered).
  ##
  ## RFC-chapulin-hardening SND-4 (ADR-0024): 58→59. Fixes a soundness
  ## UNDER-approximation (false "no defect"): string character index reads
  ## (`s[i]`, IR kind `iekStrAt`) had ZERO `IndexError`/`IndexDefect` modeling,
  ## unlike seq/array/Table indexing (which already fork a defect via the
  ## unconditional `forkDefect` in the `isIndex` walk arm, Phase 16 D1a). An
  ## out-of-range `i` silently degraded to a fabricated byte value (Z3's
  ## `at`/`toCode` spec: OOB → empty string / -1 → BV8 0xFF) instead of
  ## raising, so a `tIndexError()` search over `s[i]` returned `sxUnsat`
  ## ("no OOB reachable") EVEN WHEN AN OOB WAS REACHABLE. Fix: mirrors the
  ## `parseIntRaiseConds`/`divByZeroConds`/`overflowConds` lowering-sink →
  ## drain-fork pattern exactly (never fork inline from `lower()` — SND-3's
  ## anti-pattern). `iekStrAt` deposits `oob = idx<0 or idx>=len(s)` into a new
  ## `strIndexOobConds` sink; `drainStrIndexRaises`, folded into
  ## `drainScalarRaiseForks` as a 4th stage, forks the OOB sub-path as a
  ## routed `IndexDefect` and asserts the negation onto the survivor's
  ## `defectSurvivorPc` (ADR-0012). Verdict-surface change: every `s[i]` read
  ## now (a) makes `tIndexError()` reachable where it previously was not, and
  ## (b) implicitly narrows its continuation to `len(s) > i` — a genuine
  ## bounds correction (a prior `sxSat`/`sxUnsat` witness that silently relied
  ## on an OOB `s[i]` producing 0xFF was unsound; real Nim would have raised
  ## before that value was ever observed). `renderAsChoicesVersion` STAYS "7"
  ## — IndexError surfaces via `raisedWitness` (a raise), not a new rendered
  ## `witness` shape. See ADR-0024 (`SYMEX_PLAN.md`) for the full write-up.
  ##
  ## RFC-chapulin-hardening SND-3 (ADR-0023): 57→58. Fixes a HIGH-severity
  ## C-backend-divergent false `sxUnsat`: a relational char/string-ordering
  ## comparison (or non-int64 `HashSet`/`set` membership test) inside a LOOP
  ## GUARD previously `raise`d a classified `Symex*Error` from deep inside
  ## expression lowering. Outside a loop that raise propagated cleanly to the
  ## `runSymex` boundary (sound `sxUnknown`); INSIDE a loop guard, the raise
  ## unwound through the walk's live `seq[Path]` and was SILENTLY LOST on the
  ## C backend's goto-exception model (the b7258f7/CR-1c divergence class) —
  ## the walk continued with a mis-lowered guard, producing a false `sxUnsat`
  ## (c) vs. the honest `sxUnknown` (cpp, whose native exceptions propagate).
  ## Fix: the three lowering-time raise sites reachable during a loop-guard
  ## walk (CR-17(a) char-ordering, `cmpString` string-ordering, `iekContains`
  ## non-int64-set membership) now degrade IN-BAND — a fresh unconstrained
  ## bool, threadvar-classified, and folded into SND-1's per-path `uncertain`
  ## taint at `drainPendingLowerEffects` — instead of raising, so both
  ## backends agree (`sxUnknown`). Verdict-surface change: c-backend loop
  ## guards over an unmodeled char/string-ordering or set-membership compare
  ## move from a false `sxUnsat` to the sound `sxUnknown` both backends
  ## already gave outside a loop. `renderAsChoicesVersion` STAYS "7" — no new
  ## witness shape (the fresh symbol is never solved-for/rendered; the
  ## degrade always demotes to `sxUnknown`). See ADR-0023 (`SYMEX_PLAN.md`)
  ## for the full write-up and the systemic raise-site audit.
  ##
  ## Cluster H H_containers (ADR-0022): 56→57. Containers OF a named
  ## ref-object now construct/index to REAL verdicts instead of raising a
  ## native exception (classified `weInternalWalkerFault` -> `sxUnknown`):
  ##   * `storeSeqElem` (runtime.nim) gains an `itRef`/`itPtr` arm — the
  ##     erased seq-data-array STORE side for a `seq[Node]` LITERAL
  ##     (`@[a, b]`) previously had no case (it raised `ValueError:
  ##     storeSeqElem: unsupported elem kind itRef`) even though the
  ##     ALLOCATION side (`allocateSeqDataRaw`) already supported itRef/itPtr
  ##     (built for Phase 15 R3's `seq[ref T]` inline-ref support). The store
  ##     is a plain raw `Z3_mk_store` of the element's `Ref_T` address —
  ##     mirrors the `isIndex/seq` read-path's raw `Z3_mk_select`.
  ##   * `iteSV` gains an `svRef`/`svPtr` arm — `array[N, Node]` INDEXING
  ##     (`arr[i]`) always routes through `isIndex`'s static-array ite-merge
  ##     chain (even for a compile-time-literal index; a static array has no
  ##     Z3Array-backed fast path like `seq` does), and any array with >1
  ##     element previously raised `ValueError: iteSV: svRef/svPtr merge
  ##     lands with Cluster R R5/R7`. The merge is a plain per-position
  ##     `Z3_mk_ite` over the two `Ref_T` addresses — sound since a
  ##     homogeneous `array[N, T]`'s elements share one `Ref_T` sort; this is
  ##     a distinct axis from R5's nil-fork / R7's alias-equality machinery
  ##     (which reason about whether two refs denote the SAME address, not
  ##     which of two already-built addresses a branch picks).
  ##   * `tuple[a: Node]` construction/field-access needed NO code change —
  ##     `svTuple.fields`/`lowerTupleLit` are kind-agnostic (`seq[SymVal]`),
  ##     and straight-line field access never touches `iteSV`.
  ##   * `Table[K, Node]` / `HashSet[Node]` STAY degraded (`sxUnknown`) —
  ##     confirmed out of scope (`allocateSym` hard-restricts table
  ##     keys/values and set elements independently of Node's ref-ness);
  ##     guard-test regressions lock this in.
  ## Per-element `seq[Node]` witness fidelity remains LENGTH-ONLY — the
  ## `extractSeqElements` itRef/itPtr arm is the PRE-EXISTING R3 stub
  ## (unchanged this slice); a full recursive per-element witness is a later
  ## H_witness slice. `renderAsChoicesVersion` does NOT bump: no new
  ## rendered WITNESS SHAPE lands here, only newly-REACHABLE verdicts for
  ## shapes (`itSeq`/`itArray`/`itTuple`) whose witness-rendering machinery
  ## already existed structurally.
  ##
  ## Cluster H Step C (ADR-0022, the atomic H1): 55→56. `classifyType`
  ## (`dsl_typebridge.nim`) FLIPS a bare named `ref object`/`ptr object`
  ## alias — BOTH the direct `type Node = ref object` form and the
  ## sym-indirected `type NodeRef = ref Obj` form — from value-modelling
  ## (`itTuple`, Phase 16 D1a) to TRUE HEAP IDENTITY (`itRef`/`itPtr(full
  ## pointee)`). This is a broad VERDICT-SURFACE change: aliasing (`q = p;
  ## q.val = 99; assert p.val == 99`) and reference identity (`p == q`,
  ## `p == nil`) on a bare named-ref symbol now yield REAL Z3 verdicts where
  ## they previously degraded to `sxUnknown`. Folds in what would have been a
  ## separate H4 slice: `ref object` construction (the P2b `nnkObjConstr` arm)
  ## now emits REAL `mkNewT` + per-present-field `mkFieldDerefWrite` heap
  ## construction (superseding P2b/ADR-0021's value-tuple arm for the ref
  ## case; a plain non-ref object constructor is unchanged); the `isNew`
  ## walker arm (`runtime_heap.nim`) universally zero-writes EVERY field of a
  ## freshly allocated object (not just the fields a constructor happened to
  ## set), closing a false-SAT hole a fresh field-split heap array would
  ## otherwise leave (an unwritten field select is UNCONSTRAINED). A variant
  ## (`case`-having) ref-object stays EXCLUDED from this flip — it still
  ## value-models via `itVariant`/`itMultiVariant`, ADR-0022 sub-decision #1
  ## (the field-split heap declines variant reads). A witness-rendering
  ## provenance flag (`IRType.isPlaceholder`) replaces an ambiguous
  ## `fields.len == 0` heuristic that mis-rendered a genuinely zero-field named
  ## ref type (`type Token = ref object`) as `nil`. Also closes a latent
  ## `emitIRType` gap this slice's own first cross-shape use exposed: the
  ## `itTuple` runtime-reconstruction call never serialised `nominalId`, so
  ## Cluster H Step A/B's nominal sort-naming silently fell back to the
  ## STRUCTURAL `$pointeeTy` rendering at WALK time for every `itTuple` — fixed
  ## by threading `nominalId` through `emitIRType`'s `itTuple` arm.
  ##
  ## Cluster H Step B (ADR-0022): 54→55. `refPointeeTypeId` (`runtime_heap.nim`)
  ## now PREFERS the pointee's `nominalId` (Cluster H Step A) over the
  ## structural `$pointeeTy` rendering when the pointee is a named object
  ## (`itTuple` with a non-empty `nominalId`) — this changes the `Ref_<...>`
  ## Z3 sort NAMES minted for inline (`ref`/`ptr`) heap pointees. Sort names
  ## are internal (never surfaced in a witness/verdict), but they flow into
  ## the symex CACHE KEY, so this is a pure cache-key rotation: verdicts and
  ## witnesses for every existing SUT are BYTE-IDENTICAL, only the DB slot
  ## they're stored under changes. `renderAsChoicesVersion` does NOT bump —
  ## no witness-shape change. This slice proves the nominal-keying mechanism
  ## on inline refs (bare `ref T`/`ptr T` params and object fields); it also
  ## unifies a bare named-ref's full-field pointee with a recursive field's
  ## empty-fielded placeholder pointee (`namedRefPlaceholder`) onto the SAME
  ## sort when they share a `nominalId` — though today a bare named-ref-alias
  ## PARAM is still VALUE-modelled (Phase 16 D1a / P2b, not `itRef`), so that
  ## particular unification becomes live only once Step C routes named refs
  ## through `itRef`.
  ##
  ## P2b (RFC-chapulin-hardening, Cluster 4 — Parser expression coverage,
  ## ADR-0021): 53→54. `ref object` construction as an EXPRESSION (`let p =
  ## Node(val: x, next: nil)`, `Node = ref object`). `classifyType` UNWRAPS a
  ## NAMED `ref object` alias to the SAME `itTuple` shape a plain value object
  ## produces (`dsl_typebridge.nim`'s "#136: unwrap ref T / ptr T"), so P2a's
  ## `nnkObjConstr` arm ALREADY, silently, took this path for ref-object
  ## constructors too — with every ref/ptr-typed field degrading to
  ## `sxUnknown` (a bare `nnkNilLit` field value has no general `parseExpr`
  ## arm; an omitted ref-typed field has no `zeroValueForType` encoding).
  ## P2b's investigation (2026-07-22) EMPIRICALLY REJECTED the RFC's original
  ## sketch (synthesise an `isNew` allocation + `mkFieldDerefWrite` preamble,
  ## mirroring the heap/logical-ref model): `let p = new(Node)` for a NAMED
  ## ref-object alias CRASHES today at walk time (`field 'refPointeeTy' is
  ## not accessible for type 'IRType' using 'kind = itTuple'`) because Phase
  ## 16 D1a deliberately VALUE-MODELS every BARE symbol of a named
  ## ref-object-alias type, REGARDLESS of how it was bound (a `let`-bound
  ## local classifies identically to a formal param) — any `svRef` a
  ## heap-based construction minted would be invisible to every later BARE
  ## `p.field` read elsewhere in the SUT (each independently re-derives `p`'s
  ## type from the AST). See ADR-0021 for the full writeup.
  ##
  ## So P2b instead HARDENS the existing value-tuple construction arm to
  ## handle ref/ptr-typed FIELDS soundly (no ref-vs-value branch: a plain
  ## `object` can equally declare a `next: Node` field):
  ##   * `next: nil` → `mkNil(fieldTy)` directly (bare `nnkNilLit` has no
  ##     general `parseExpr` arm outside the `==`/`!=` comparison special
  ##     case).
  ##   * An OMITTED ref-typed field → `mkNil(fieldTy)` (Nim's REAL zero for a
  ##     ref/ptr is `nil` — sound, not a degrade — `zeroValueForType`'s
  ##     `else: nil` catch-all doesn't cover itRef/itPtr, so this is
  ##     special-cased ahead of it).
  ##   * A PRESENT ref-typed field whose value does NOT resolve to a genuine
  ##     ref/ptr address (the common case: `next: otherNode`, recursive
  ##     construction from an existing BARE-symbol node, D1a value-modelled
  ##     as `itTuple` — no address to store) degrades THAT FIELD ONLY
  ##     (`feUnsupportedExprKind` + `mkUnsupported`, SND-1 taints the whole
  ##     run to `sxUnknown`) and fills with a type-COMPATIBLE `mkNil` — never
  ##     a shape-mismatched value that could crash a downstream accessor.
  ##   * A VARIANT object constructor (`itVariant`/`itMultiVariant`) reaching
  ##     this arm is GUARDED and degraded (register the classified error,
  ##     return a reference to a FRESH, deliberately UNBOUND synthetic var —
  ##     any consumer's `env[name]` lookup raises `KeyError`, a
  ##     `CatchableError` caught by the CR-1c safety net — never `mkIntLit(0)`
  ##     under a mismatched declared type, which would risk `isVariantField`'s
  ##     `doAssert false`, an uncatchable `Defect`/crash). Variant objects are
  ##     EXCLUDED from construction (round-2 decision — the field-split heap
  ##     already declines variant READS, `heRefVariantUnsupported`; this
  ##     retroactively hardens a P2a gap that otherwise hard-crashed macro
  ##     expansion on ANY variant-object constructor, ref or value). Negative
  ##     DoD test pins this stays `sxUnknown`, never a crash.
  ## Pure VERDICT change (`sxUnknown` → real `sxSat`/`sxUnsat`) for SUTs
  ## constructing a ref object as an expression — hence the walker bump.
  ## `renderAsChoicesVersion` does NOT bump, for the SAME reason P1/P2a
  ## didn't: the witness surface is built only from top-level SUT PARAMETERS,
  ## and a constructed ref object is an internal `let`/return value that
  ## never reaches `renderAsChoices` in a new shape.
  ##
  ## P2a (RFC-chapulin-hardening, Cluster 4 — Parser expression coverage):
  ## 52→53. `parseExpr` (`dsl_parser.nim`) gains an `nnkObjConstr` arm: a
  ## value-object (non-ref) constructor `Point(x: a, y: b)` used as an
  ## EXPRESSION (e.g. `let p = Point(x: a, y: b)`, an object `return`) was
  ## previously recognised ONLY inside `nnkRaiseStmt`'s `newException(T,
  ## msg)` shape; any OTHER value-object construction fell through to
  ## CR-2a's catch-all, tainting the whole run to `sxUnknown` (SND-1). A
  ## value object's `IRType` is `itTuple`-shaped (`classifyType`'s nominal-
  ## object plain-record path — ALREADY exercised today by object-typed SUT
  ## parameters, e.g. the P1-precedent `Point` case in
  ## `tsymex_phase4_tuple.nim` — yields `tTuple(fields, fieldNames,
  ## objectName = "Point")`), so P2a REUSES P1's `iekTupleLit`/
  ## `mkTupleLit`/`lowerTupleLit` wholesale rather than minting a new IR
  ## kind: every existing `iekTupleLit` dispatch site (emitExpr,
  ## abstraction.nim, probeProto, canonicalize, …) transfers for free.
  ## Unlike a tuple, object-constructor fields may be reordered or omitted;
  ## the new arm walks the TYPE's declared field order and, for an omitted
  ## field, synthesises Nim's genuine zero-init value via CR-2a's
  ## `zeroValueForType` (sound — not a degrade) or, for a field type with no
  ## clean zero-value encoding, degrades that one field via the same
  ## `feUnsupportedExprKind`/`mkUnsupported`/SND-1 taint idiom the CR-2a
  ## catch-all uses — never a false `sxSat`. A present field parses via the
  ## ORDINARY `parseExpr` recursion, so an individually-unsupported field
  ## (e.g. `cast[int32](x)`) independently taints via SND-1, same as P1.
  ## Pure VERDICT change (`sxUnknown` → real `sxSat`/`sxUnsat`) for SUTs
  ## constructing a value object as an expression — hence the walker bump.
  ## `renderAsChoicesVersion` does NOT bump, for the SAME reason P1 didn't:
  ## the witness surface is built only from top-level SUT PARAMETERS (whose
  ## object/tuple reflection branch already existed), and a constructed
  ## value object is an internal `let`/return value that never reaches
  ## `renderAsChoices` in a new shape.
  ##
  ## P1 (RFC-chapulin-hardening, Cluster 4 — Parser expression coverage):
  ## 51→52. `parseExpr` (`dsl_parser.nim`) gains a general N-ary
  ## `nnkTupleConstr` arm: a tuple constructor `(a, b, c)` / named `(x: a, y:
  ## b)` used as an EXPRESSION (e.g. `let t = (a, b)`, a tuple `return`) was
  ## previously handled ONLY by the narrow `yield (e1,e2)` A3-S2a special-case
  ## (`parseIterBodyStmt`); any other occurrence fell through to CR-2a's
  ## catch-all, which taints the whole run to `sxUnknown` (SND-1). The new
  ## arm builds a fresh `iekTupleLit` IR node → `svTuple` at runtime, reusing
  ## the ALREADY-EXISTING itTuple/svTuple witness/runtime machinery built for
  ## variant/object values — this slice is purely the construction path. A
  ## tuple containing one still-unsupported field (e.g. `cast[int32](x)`)
  ## independently hits the CR-2a catch-all for that field, which taints via
  ## SND-1 same as before — never a false `sxSat`. Pure VERDICT change
  ## (`sxUnknown` → real `sxSat`/`sxUnsat`) for SUTs constructing a tuple as
  ## an expression — hence the walker bump. `renderAsChoicesVersion` does
  ## NOT bump: the witness surface (`renderAsChoices*[T]`, `symex.nim`) is
  ## built ONLY from the SUT's top-level PARAMETER list via
  ## `emitTyAndReader`/`witnessTup` — never from an internal `let`-bound or
  ## returned value — and its `elif T is tuple:` branch (generic reflection
  ## over `fields(w)`) already existed untouched before this slice (tuple-
  ## typed SUT PARAMETERS already rendered correctly, per the M1 precedent
  ## for nested `tuple[seq[byte]]`). P1 introduces no new value ever reaches
  ## `renderAsChoices` in a new shape, so no cache-format rotation is needed
  ## for RC.
  ##
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
  ##
  ## RFC-chapulin-hardening R14 (CRITICAL soundness fix): 62→63. The
  ## `mkGuardedWhile` do-while rotation (landed as part of R1B, 61) re-ran a
  ## short-circuit while-guard's hoisted preamble as a TRAILING statement in
  ## the loop body (`<body>; <guardPre>`). `walkBlock` (runtime.nim) stops
  ## processing a block's remaining statements once a statement returns zero
  ## paths — exactly what `continue` does (siphons the path into
  ## `continuePaths`, returns `@[]`) — so a `continue` silently skipped the
  ## guard-refresh, the guard temp `sc` went stale, and the NEXT guard check
  ## ran against OLD loop-variable state: a false verdict (confirmed repro: a
  ## `continue` inside `while i < s.len and s[i] != 'z': inc i; continue`).
  ## `mkGuardedWhile` is DELETED and replaced by `mkShortCircuitWhile`
  ## (`dsl_parser.nim`), which PREFERS desugaring the short-circuit `and` at
  ## the LOOP level instead of hoisting a guard temp: `while (A and B): body`
  ## (B carrying the inline defect fork, e.g. `s[i]`) becomes `while A: <B's
  ## preamble>; if not B: break; body`. B is lowered INSIDE the body, entered
  ## only when guard A holds, so B's inline fault forks with A already in the
  ## path condition — sound "for free" by loop semantics, and continue-safe
  ## by construction (`continue` jumps to the top of `while A`, re-evaluating
  ## A and re-running B's preamble exactly like Nim does).
  ##
  ## A guard that is not a clean `and`-split (a plain guard whose parse
  ## hoists a preamble for ANY reason — not necessarily a short-circuit
  ## fault; e.g. `(a div b) > i` semchecks to a trivial `nnkStmtListExpr`
  ## wrapper that alone hoists a no-op preamble statement — an `or`-guard
  ## with a fault, or a fault nested inside the `and`'s own LHS) falls back
  ## to the pre-R14 do-while rotation (`mkRotatedGuardWhile`, the former
  ## `mkGuardedWhile` guarded path, kept as a controlled fallback) whenever
  ## the loop body PROVABLY contains no `continue` (`hasContinueShallow`) —
  ## the rotation is only unsound when a `continue` can skip its trailing
  ## refresh, so once that is ruled out structurally it is safe. Only when
  ## the body DOES contain a `continue` AND no clean and-split is available
  ## does this emit a classified `feUnsupportedOp` sound-degrade (`sxUnknown`)
  ## instead of ever risking a stale-guard false verdict. (An earlier
  ## iteration of this fix degraded ANY guard needing D1c-style hoisting,
  ## regardless of `continue`-safety — caught by `tsymex_r1_draingap.nim`'s
  ## `whileDivZero` regressing from `sxRaised` to a false `sxUnknown`; fixed
  ## before landing by adding the `hasContinueShallow` gate.)
  ## Verdict-surface change: any SUT whose `while`-guard's short-circuit RHS
  ## carries an inline defect fork AND whose body contains a `continue` moves
  ## from a possible false `sxUnknown`/false verdict to the correct one; the
  ## rare or-with-fault / nested-fault guard shapes WITH a `continue` in the
  ## body move from the old (silently wrong in that case) guarded rotation to
  ## an honest `sxUnknown` degrade — the same shapes WITHOUT a `continue`
  ## keep computing the correct real verdict via the rotation fallback, byte-
  ## identical to pre-R14 behaviour. `renderAsChoicesVersion` STAYS "7" — no new
  ## witness shape, only a verdict-correctness fix.
  ##
  ## Round-6 B7-rider (2026-08-16/17, ADR-0028 Leg 1 + Leg 2 — closes the B7
  ## exit-gate BLOCKER A): 86→87. LEG 1: `tryRecognizeScanIdiom`(Q1/B0)/
  ## `tryRecognizeScanPairIdiom`(B3)/`tryRecognizeAccumulatingScan`(B4)/
  ## `tryRecognizePairLoopIdiom`(B6) — `dsl_parser.nim` — WIDENED their
  ## receiver gate from itString-only to also accept a string-backed
  ## `seq[byte]` receiver (`ctx.stringBackedParams`, B1's shared classifier,
  ## consulted via the new shared `scanReceiverOk`/`scanDelimiterChar`); the
  ## delimiter gate widened in lockstep to accept a byte-range literal
  ## (`0'u8`/`byte(0)`/`0x00`, mapped to its char value) alongside the
  ## original char literal. `collectStringBackedByteSeqParams`'s own
  ## candidate walk — previously Q1-shape-only — now tries all four shape
  ## predicates per loop, closing a real gap: chapulin's actual
  ## `readCString`/`readOptions` shapes are B4/B6-shaped, never Q1-shaped, so
  ## their `seq[byte]` params were never classified string-backed at all
  ## regardless of how the four recognizers' own gates were widened. A NEW
  ## one-level call trace (mirroring `collectIntOffsetParamsImpl`'s own
  ## "wrapper" promotion) closes a companion composability gap: `runtime.nim`'s
  ## `isCall` arm binds a caller's lowered argument value directly into the
  ## callee's env with no representation bridge (`calleeEnv[formal.name] =
  ## argVals[i]`) — unlike `IRParam.isIntOffset` (int/BV are fungible via a
  ## proto), itString and itSeq are different Z3 sorts with no lossless
  ## reinterpretation, so a caller whose own top-level `seq[byte]` param has
  ## no qualifying loop of its own (the scan lives entirely inside a callee
  ## it invokes) now ALSO gets classified string-backed in its own scope, so
  ## its argument lowers as `svString` from entry, matching what the callee's
  ## inlined body expects. Verdict-surface change: a `seq[byte]` receiver
  ## through any of the four recognizer shapes moves from an unrecognized
  ## k-unroll (`sxUnknown` once the trip count exceeds budget) to the SAME
  ## real closed-form verdict an equivalent `string` receiver already gets.
  ##
  ## LEG 2 (companion char-widening witness-corruption bug, root-caused
  ## while landing this rider): the chapulin handoff's own hypothesis
  ## ("witness EXTRACTION corrupts") was investigated and found INCORRECT —
  ## `evalStrBytes`/`getStringContents` (the B4-rider extraction chokepoint)
  ## faithfully report whatever Z3's model actually contains; the real
  ## defect is a PARSE-TIME MODELING GAP, one call-site removed from
  ## extraction entirely. `char` is not a member of `intTyNames` and was
  ## never mapped by `normalizeIntTyName` the way `byte` is — so
  ## `isIntFamilyName("char")` was FALSE, and a widening conversion off a
  ## char (`uint16(s[i])`, the TFTP opcode-dispatch header-read shape)
  ## fell through `dsl_parser.nim`'s `nnkConv` arm to its bare
  ## `parseExpr(operand, ...)` pass-through — SILENTLY DROPPING the
  ## conversion, exactly the class of bug B2 itself fixed for narrowing/
  ## reinterpret conversions, just for a source type B2 never covered.
  ## Isolated repro (`let hi = uint16(s[0]); let lo = uint16(s[1]); let
  ## combined = (hi shl 8) or lo; combined == 0x4142'u16`): with the
  ## conversion dropped, `hi`/`lo`/`combined` all stayed 8-bit (`svBV8`) —
  ## Nim's own DECLARED 16-bit type on the `let` bindings notwithstanding
  ## (`isLet`'s walker arm binds whatever `lower()` returns for the RHS,
  ## with NO width coercion for a non-literal expression). Comparing an
  ## 8-bit `combined` to the 16-bit literal `0x4142'u16` truncated the
  ## literal to its low byte (`0x42`) at the literal-shaping step
  ## (`coerceIntLit`), so the CHECKED property silently degenerated to `lo
  ## == 0x42` with `hi` COMPLETELY UNCONSTRAINED. `sxSat` was technically
  ## correct (`'A','B'` genuinely satisfies the real, intended property),
  ## but the reported witness reflected Z3's free (don't-care) choice for
  ## `hi`'s underlying byte — confirmed empirically: the reported witness
  ## (`s[0] == 189` in one observed run) does NOT reproduce `combined ==
  ## 0x4142` when replayed through the real widen+shl+or expression, while
  ## a genuine solution (`s == "AB"`) does. Fix (`dsl_parser.nim`,
  ## `normalizeIntTyName`): `char` now normalizes to `"uint8"`, the SAME
  ## treatment `byte` already gets — `char` is ordinally an 8-bit UNSIGNED
  ## value (never sign-extends) under a distinct (non-alias) type name, so
  ## this is semantically exact, not an approximation. Every existing
  ## `isIntFamilyName`/`intTyWidth`/`intTySigned` call site now handles
  ## `char` for free: `uint16(<char>)` WIDENS (zero-extends) through B2's
  ## existing `iekConvIntWidth`; `char(<byte>)`/`char(<uint8>)` normalize
  ## to the same width+signedness on both sides and fall to the existing
  ## harmless identity pass-through (a `byte`↔`char` reinterpretation is
  ## bit-identical); `char(<a wider int>)` NARROWS and correctly
  ## classified-declines, mirroring `byte`'s own narrowing decline.
  ## Verdict-surface change (genuine, not merely cosmetic — this is why
  ## LEG 2 shares LEG 1's walker bump rather than only bumping
  ## `renderAsChoicesVersion`): a property whose truth genuinely depends on
  ## a char-widened value's FULL width — reachable and unreachable cases
  ## alike — was being checked at a silently truncated 8-bit width; both a
  ## false-negative (a real property, provable only through information
  ## the truncation discarded, wrongly declining) and the false-witness
  ## symptom this repro pins are instances of the same underlying gap.
  ## `renderAsChoicesVersion` bumps in lockstep, 10→11 (see above) — content
  ## for every affected already-`sxSat` witness changes from Z3's
  ## previously-free don't-care byte to the value the (now-sound) proof
  ## actually depends on.

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
  of iekConvIntWidth:
    # Round-6 B2. Every field that changes the encoding (source/target width
    # AND signedness — signedness picks zero- vs sign-extend, and steers the
    # result's own `signed` flag) is part of the key so two conversions that
    # differ only in signedness never collide.
    "Ex<CIW:" & $e.ciwSrcWidth & ":" & $e.ciwSrcSigned & ":" &
      $e.ciwTgtWidth & ":" & $e.ciwTgtSigned & ":" &
      canonicalize(e.ciwOperand, env) & ">"
  of iekConvIntReinterpret:
    # A1 adjudication: width + target signedness are both part of the key
    # (mirrors iekConvIntWidth) so a signed vs. unsigned reinterpret of the
    # same operand never collides.
    "Ex<CIR:" & $e.cirWidth & ":" & $e.cirTgtSigned & ":" &
      canonicalize(e.cirOperand, env) & ">"
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
  of iekTupleLit:
    # RFC-chapulin-hardening P1. Distinct `TL:` prefix so a tuple literal
    # never cache-collides with `AL:` (array) or `SeqLit:` (seq) content-
    # addressing, even if the argument lists happened to canonicalize
    # identically otherwise.
    var parts: seq[string]
    for x in e.telems: parts.add canonicalize(x, env)
    "Ex<TL:" & canonicalize(e.ttupleTy) & ";[" & parts.join(",") & "]>"
  of iekVariantLit:
    # Round-6 A1. Distinct `VL:` prefix (never collides with `TL:`/`AL:`);
    # the tag ordinal is part of the key so two constructions of the same
    # variant type at different literal tags never cache-collide.
    var armParts: seq[string]
    for x in e.vlArmFields: armParts.add canonicalize(x, env)
    var plainParts: seq[string]
    for x in e.vlPlainFields: plainParts.add canonicalize(x, env)
    "Ex<VL:" & canonicalize(e.vlVariantTy) & ";" & $e.vlTagOrd & ";[" &
      armParts.join(",") & "];[" & plainParts.join(",") & "]>"
  of iekSeqLen:    "Ex<SL:" & canonicalize(e.lenObj, env) & ">"
  of iekSeqSlice:  "Ex<SSL:" & canonicalize(e.ssBase, env) & ":" &
                   canonicalize(e.ssLo, env) & ":" &
                   canonicalize(e.ssHi, env) & ">"   ## v67: seq-slice view
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
  of isVariantConstructSym:
    # Round-6 A3 (ADR-0029). Distinct `VCS:` prefix (never collides with
    # `VRS:`/`VL:`). `vcsLoc` is DELIBERATELY excluded — it is pure
    # diagnostic metadata (a source location string for a walk-time decline
    # message), and the cache key is defined to be "stable across builds
    # (no source locations, ...)"; two logically-identical constructs at
    # different call sites already differ via `vcsResultVar`'s bound slot
    # and every operand below, so omitting `vcsLoc` costs no precision.
    let slot = bindLocal(env, s.vcsResultVar)
    var tagParts: seq[string]
    for t in s.vcsTagSet: tagParts.add $t
    var plainParts: seq[string]
    for x in s.vcsPlainFields: plainParts.add canonicalize(x, env)
    "St<VCS:$" & $slot & "=" & canonicalize(s.vcsVariantTy) & ";disc=" &
      canonicalize(s.vcsDiscExpr, env) & ";tags=[" & tagParts.join(",") &
      "];plain=[" & plainParts.join(",") & "]>"
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
  ##   maxVariantConstructorForks — Round-6 A3 (ADR-0029): gates whether a
  ##                        symbolic-discriminant variant CONSTRUCTION forks
  ##                        per-tag (real sxSat/sxUnsat) or classifies a
  ##                        `beBudgetExhausted` decline (sxUnknown) — WIRED
  ##                        from the same commit that introduces the field
  ##                        (never had an "unwired" period to exclude it for).
  ##   maxVariantConstructorFieldAllocs — N9 (round-6 review remediation):
  ##                        gates whether `isVariantConstructSym`'s per-fork
  ##                        ALL-ARMS field allocation proceeds (real
  ##                        sxSat/sxUnsat) or classifies a `beBudgetExhausted`
  ##                        decline (sxUnknown) — same wiring precedent as
  ##                        `maxVariantConstructorForks` above, WIRED from the
  ##                        commit that introduces the field.
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
    ";mvcf=" & $s.budget.maxVariantConstructorForks &  ## Round-6 A3
    ";mvfa=" & $s.budget.maxVariantConstructorFieldAllocs &  ## N9
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
