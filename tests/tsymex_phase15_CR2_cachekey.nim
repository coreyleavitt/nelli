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

  test "CR-2 sub-test 5: symexWalkerVersion is now 44":
    ## CR-2a (RFC-chapulin-hardening Cluster 2 — Crash-totality) bumped the
    ## walker version 43→44: `parseExpr`'s expression-position catch-all no
    ## longer `error()`s at macro-expansion on an unsupported NimNode `kind`
    ## (which aborted compilation outright — strictly worse than `sxUnknown`,
    ## the SUT couldn't be analysed at all). It now registers a classified
    ## `sevError` (`feUnsupportedExprKind`), emits `mkUnsupported` into the
    ## preamble, and returns a type-correct dummy (`classifyType(n).ty`),
    ## reusing the A7-S3 `runeLen(symbolic)` degrade idiom. SUTs that
    ## previously failed to COMPILE now compile and resolve to a classified
    ## `sxUnknown`, so the cache key must rotate.
    ## (Prior: CR-1c 42→43: a final `except CatchableError` catch-all on the
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
    check symexWalkerVersion == "44"

  test "CR-2 sub-test 6: renderAsChoicesVersion is now 4":
    ## CR-4 changes how int32(f) materialises as svBV32 internally; however,
    ## renderAsChoices operates on the extracted Nim witness value (int32 →
    ## SomeSignedInt → integerChoice path), which is identical before and after.
    ## The renderAsChoices FORMAT is genuinely unaffected by CR-4.
    ## However, the consolidated version bump document (Part 2 of CR-2 task)
    ## instructs a bump to "4" as part of the CR-1/CR-3/CR-4/CR-5/CR-6
    ## consolidated model-change cache rotation.
    check renderAsChoicesVersion == "4"
