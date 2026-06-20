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
    s1.maxClosureInlineCount = s0.maxClosureInlineCount + 1
    check canonicalize(s0) != canonicalize(s1)

  test "CR-2 sub-test 3: maxBytesEncodingLen changes canonical form":
    ## Changing maxBytesEncodingLen changes whether a bytes(s) materialisation
    ## triggers seBytesLengthTooLarge → sxUnknown vs expands (sxSat).
    ## Two settings differing ONLY in maxBytesEncodingLen must hash differently.
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.maxBytesEncodingLen = s0.maxBytesEncodingLen + 1
    check canonicalize(s0) != canonicalize(s1)

  test "CR-2 sub-test 4: maxFreshnessAssertions changes canonical form":
    ## Changing maxFreshnessAssertions changes how many `newRef != prior`
    ## distinctness constraints are emitted. When the cap is hit, dropped
    ## inequalities allow Z3 to alias refs it otherwise could not → false-SAT
    ## direction. Two settings differing ONLY in maxFreshnessAssertions must hash
    ## differently.
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.maxFreshnessAssertions = s0.maxFreshnessAssertions + 1
    check canonicalize(s0) != canonicalize(s1)

  test "CR-2 guard: maxSplitParts still OMITTED from canonical form (unwired)":
    ## maxSplitParts is deliberately excluded: no reachable code reads it today
    ## (symbolic split takes sxUnknown first). When wired (CR-18), it must be
    ## added then; until then, the key must NOT change when only maxSplitParts
    ## differs (avoiding false cache-miss overhead for an unwired setting).
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.maxSplitParts = s0.maxSplitParts + 1
    check canonicalize(s0) == canonicalize(s1)

suite "Phase 15 CR-2 — version bumps":

  test "CR-2 sub-test 5: symexWalkerVersion is now 14":
    ## Phase 15 F5-probeproto fix bumped the walker version 13→14.
    ## `probeProto`'s `iekConvFloatToInt` arm now returns the correct BV
    ## sentinel (svBV32 for int32(f), svBV64 for int(f)), matching what
    ## `lower()` produces. Before the fix, the stale svInt sentinel caused
    ## literal operands in `int(f)>5` or `int(f)+5==k` to be lowered as svInt
    ## while the conversion result was svBV64 — reopening the F5 bv2int hang
    ## for ordering goals and crashing binBV for arithmetic goals.
    check symexWalkerVersion == "14"

  test "CR-2 sub-test 6: renderAsChoicesVersion is now 4":
    ## CR-4 changes how int32(f) materialises as svBV32 internally; however,
    ## renderAsChoices operates on the extracted Nim witness value (int32 →
    ## SomeSignedInt → integerChoice path), which is identical before and after.
    ## The renderAsChoices FORMAT is genuinely unaffected by CR-4.
    ## However, the consolidated version bump document (Part 2 of CR-2 task)
    ## instructs a bump to "4" as part of the CR-1/CR-3/CR-4/CR-5/CR-6
    ## consolidated model-change cache rotation.
    check renderAsChoicesVersion == "4"
