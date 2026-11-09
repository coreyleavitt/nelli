## Phase 16 R16-1 — ArithCheck policy foundation.
##
## DoD (ADR-0011 R16-1 row):
##   * `DefectKind` has `dkOverflowDefect` and `dkDivByZeroDefect` appended at
##     the END (CR-16 ordinal-stability).
##   * `typeIdToDefectKind` maps "OverflowDefect" and "DivByZeroDefect" to the
##     new kinds.
##   * `ArithCheck` enum `{acOverflow, acDivByZero, acRange}` is new.
##   * (RFC-0016 K10d: the `SymexSettings.arithChecks` setting, its cache-key
##     key, its default and its `validateSymexSettings` warnings were part of
##     this slice and are removed; the build decides. See
##     `tsymex_0016_k10d_removals`.)
##   * `symexWalkerVersion` is bumped to "21".
##   * NO new defect forks — no behavior change; existing suite stays green.
##
## This test file is the RED→GREEN harness for R16-1.

import std/[unittest, strutils, sequtils]
import nelli/smt/canonicalize
import nelli/smt/types

# ---- Part 1: DefectKind enum additions (F3, CR-16) --------------------------

suite "R16-1 — DefectKind enum additions (F3, CR-16 ordinal stability)":

  test "dkOverflowDefect is declared and distinct from all prior kinds":
    ## R16-1 appended dkOverflowDefect at the END of DefectKind. Verify it
    ## compiles and has a higher ordinal than dkOther (the previous last member).
    check dkOverflowDefect.ord > dkOther.ord

  test "dkDivByZeroDefect is declared and distinct from all prior kinds":
    ## R16-1 appended dkDivByZeroDefect after dkOverflowDefect.
    check dkDivByZeroDefect.ord > dkOverflowDefect.ord

  test "prior DefectKind ordinals are UNCHANGED (CR-16 stability)":
    ## Inserting at the END must not shift existing ordinals. Verify that the
    ## well-known members still occupy their original positions.
    check dkAssertionDefect.ord    == 0
    check dkIndexDefect.ord        == 1
    check dkFieldDefect.ord        == 2
    check dkRangeDefect.ord        == 3
    check dkOutOfMemoryDefect.ord  == 4
    check dkStackOverflowDefect.ord == 5
    check dkOther.ord              == 6
    ## New R16-1 members follow at 7 and 8.
    check dkOverflowDefect.ord     == 7
    check dkDivByZeroDefect.ord    == 8

# ---- Part 2: typeIdToDefectKind mapping (runtime.nim internal — test via
#              defectExclusions membership, the only public surface) -----------

## `typeIdToDefectKind` is an internal `runtime.nim` proc; we cannot call it
## directly in a unit test.  Instead we verify that the new DefectKind values
## can be placed in `defectExclusions` (the only public consumer) and that the
## resulting settings canonical forms differ as expected.

suite "R16-1 — new DefectKind values usable in defectExclusions":

  test "dkOverflowDefect can be added to defectExclusions":
    var s = defaultSymexSettings()
    s.defectExclusions.incl dkOverflowDefect
    check dkOverflowDefect in s.defectExclusions

  test "dkDivByZeroDefect can be added to defectExclusions":
    var s = defaultSymexSettings()
    s.defectExclusions.incl dkDivByZeroDefect
    check dkDivByZeroDefect in s.defectExclusions

  test "defectExclusions with new kinds produces a DIFFERENT canonical form":
    ## Confirm ordinal-stable rendering: adding dkOverflowDefect to the exclusion
    ## set changes the cache key (the `;de=` field changes).
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.defectExclusions.incl dkOverflowDefect
    check canonicalize(s0) != canonicalize(s1)

# ---- Part 3: ArithCheck enum -------------------------------------------------

suite "R16-1 — ArithCheck enum":

  test "ArithCheck members have expected ordinals (CR-16 stability base)":
    ## Lock ordinals now so future appends don't accidentally shift them.
    check acOverflow.ord  == 0
    check acDivByZero.ord == 1
    check acRange.ord     == 2

# ---- Part 8: walker version --------------------------------------------------

suite "R16-1 — walker version bump to 21 (now superseded by R16-2b bump to 23)":

  test "symexWalkerVersion floor >= 21 (R16-1 arithcheck foundation introduced at 21)":
    ## R16-1 "21" → … → A2 Slice 1 "27" → A2 Slice 2 "28" → A2 Slice 3 "29"
    ## → A3 Slice 1 "30" → A3 Slice 2 "31" → A3-S2a tuple-yield "32"
    ## → A8 radix formatting "33" → A9 ASCII case-fold "34"
    ## → A7-S1 Rune codepoint model "35" → A7-S2 $r UTF-8 encoding "36"
    ## → A7-S3 concrete runes/runeLen + symbolic degrade "37"
    ## → SND-1 isUnsupported taints Path.uncertain "38"
    ## → SND-1b closure ground-axiom uncertain-drop "39".
    ## SW pin idiom (RFC §Version-pin discipline,
    ## Corey-decided synthesis 2026-07-12): this incidental feature-test pin
    ## migrates to a tolerant `>=` floor (only the canonical
    ## tsymex_phase15_CR2_cachekey.nim keeps brittle `==`).
    check parseInt(symexWalkerVersion) >= 21
