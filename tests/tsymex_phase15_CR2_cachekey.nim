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
import proptest/smt/canonicalize
import proptest/smt/types

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

  test "CR-2 sub-test 5: symexWalkerVersion is now 48":
    ## M2 (RFC-chapulin-hardening Cluster 3 — Model/stdlib gaps) bumped the
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
    check symexWalkerVersion == "48"

  test "CR-2 sub-test 6: renderAsChoicesVersion is now 5":
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
    check renderAsChoicesVersion == "5"
