## Phase 16 R16-1 — ArithCheck policy foundation.
##
## DoD (ADR-0011 R16-1 row):
##   * `DefectKind` has `dkOverflowDefect` and `dkDivByZeroDefect` appended at
##     the END (CR-16 ordinal-stability).
##   * `typeIdToDefectKind` maps "OverflowDefect" and "DivByZeroDefect" to the
##     new kinds.
##   * `ArithCheck` enum `{acOverflow, acDivByZero, acRange}` is new.
##   * `SymexSettings.arithChecks` defaults to ALL-ON `{acOverflow, acDivByZero,
##     acRange}`.
##   * Two `SymexSettings` differing ONLY in `arithChecks` produce DIFFERENT
##     cache keys.
##   * `validateSymexSettings` emits a warning when `arithChecks` is empty
##     ("no arithmetic checks visible").
##   * `validateSymexSettings` emits a warning when a check is enabled in
##     `arithChecks` but its corresponding `DefectKind` is in `defectExclusions`
##     ("fork cost paid, finding suppressed").
##   * `symexWalkerVersion` is bumped to "21".
##   * NO new defect forks — no behavior change; existing suite stays green.
##
## This test file is the RED→GREEN harness for R16-1.

import std/[unittest, strutils, sequtils]
import proptest/smt/canonicalize
import proptest/smt/types

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

# ---- Part 4: SymexSettings.arithChecks default --------------------------------

suite "R16-1 — SymexSettings.arithChecks default":

  test "defaultSymexSettings has arithChecks == {acOverflow, acDivByZero, acRange}":
    ## ADR-0011 F2 decision: default is ALL-ON (debug-like). Empty set is the
    ## release-like opt-out — not the default.
    let s = defaultSymexSettings()
    check s.arithChecks == {acOverflow, acDivByZero, acRange}

  test "arithChecks field is present and assignable":
    var s = defaultSymexSettings()
    s.arithChecks = {acDivByZero}
    check s.arithChecks == {acDivByZero}
    s.arithChecks = {}
    check s.arithChecks == {}

# ---- Part 5: arithChecks in cache key ----------------------------------------

suite "R16-1 — arithChecks participates in cache key":

  test "two settings differing ONLY in arithChecks produce DIFFERENT canonical forms":
    ## The main R16-1 cache-key DoD: arithChecks gates fork emission and thus
    ## changes verdicts. Two settings that differ only in arithChecks must not
    ## hash to the same key.
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.arithChecks = {}    ## all checks off — different from default (all-on)
    check canonicalize(s0) != canonicalize(s1)

  test "arithChecks == {acOverflow} vs {acDivByZero} produces DIFFERENT canonical forms":
    var s0 = defaultSymexSettings()
    var s1 = s0
    s0.arithChecks = {acOverflow}
    s1.arithChecks = {acDivByZero}
    check canonicalize(s0) != canonicalize(s1)

  test "canonical form contains the ;ac= field":
    let s = defaultSymexSettings()
    check ";ac=" in canonicalize(s)

# ---- Part 6: SymexSettings + merge threads arithChecks ----------------------

suite "R16-1 — SymexSettings + merge threads arithChecks":

  test "merging a non-default arithChecks overrides the base":
    let base = defaultSymexSettings()
    var override = defaultSymexSettings()
    override.arithChecks = {acOverflow}
    let merged = base + override
    check merged.arithChecks == {acOverflow}

  test "merging a default arithChecks keeps the base value":
    var base = defaultSymexSettings()
    base.arithChecks = {acDivByZero}
    let override = defaultSymexSettings()  ## arithChecks == default (all-on)
    let merged = base + override
    ## override's arithChecks equals the default, so base's value is kept
    check merged.arithChecks == {acDivByZero}

# ---- Part 7: validateSymexSettings warnings ----------------------------------

suite "R16-1 — validateSymexSettings arithChecks warnings":

  test "(b) empty arithChecks emits 'no arithmetic checks' warning":
    ## ADR-0011 R16-1: when arithChecks is empty, no arithmetic defect forks
    ## are ever emitted. Warn the user — this is almost certainly a mistake.
    var s = defaultSymexSettings()
    s.arithChecks = {}
    let warns = validateSymexSettings(s)
    check warns.len >= 1
    check warns.anyIt("arithChecks" in it and "empty" in it)

  test "(b) all-on arithChecks emits NO 'empty' warning":
    let s = defaultSymexSettings()
    let warns = validateSymexSettings(s)
    check warns.allIt("arithChecks" notin it or "empty" notin it)

  test "(c) acOverflow on but dkOverflowDefect excluded → 'waste' warning":
    ## Fork is emitted (paying path cost) but finding is always suppressed.
    var s = defaultSymexSettings()
    s.arithChecks = {acOverflow}
    s.defectExclusions.incl dkOverflowDefect
    let warns = validateSymexSettings(s)
    check warns.len >= 1
    check warns.anyIt("acOverflow" in it and "dkOverflowDefect" in it)

  test "(c) acDivByZero on but dkDivByZeroDefect excluded → 'waste' warning":
    var s = defaultSymexSettings()
    s.arithChecks = {acDivByZero}
    s.defectExclusions.incl dkDivByZeroDefect
    let warns = validateSymexSettings(s)
    check warns.len >= 1
    check warns.anyIt("acDivByZero" in it and "dkDivByZeroDefect" in it)

  test "(c) acRange on but dkRangeDefect excluded → 'waste' warning":
    var s = defaultSymexSettings()
    s.arithChecks = {acRange}
    s.defectExclusions.incl dkRangeDefect
    let warns = validateSymexSettings(s)
    check warns.len >= 1
    check warns.anyIt("acRange" in it and "dkRangeDefect" in it)

  test "(c) acOverflow OFF — no waste warning even if dkOverflowDefect excluded":
    ## When the check is disabled (not in arithChecks), there is no fork cost to
    ## waste; the excluded kind is redundant but not wasteful. No warning.
    var s = defaultSymexSettings()
    s.arithChecks = {acDivByZero, acRange}   ## acOverflow is OFF
    s.defectExclusions.incl dkOverflowDefect
    let warns = validateSymexSettings(s)
    check warns.allIt("acOverflow" notin it)

  test "pre-existing seqInlineThreshold warning still fires alongside R16-1 warnings":
    ## Regression: the new warnings must coexist with the pre-existing
    ## seqInlineThreshold warning from Phase 15 C4.
    var s = defaultSymexSettings()
    s.budget.seqInlineThreshold = 42
    s.inlinePolicy = ipAlwaysInline   ## seqInlineThreshold warning trigger
    s.arithChecks = {}                ## R16-1 empty warning trigger
    let warns = validateSymexSettings(s)
    check warns.len >= 2
    check warns.anyIt("seqInlineThreshold" in it)
    check warns.anyIt("arithChecks" in it and "empty" in it)

# ---- Part 8: walker version --------------------------------------------------

suite "R16-1 — walker version bump to 21 (now superseded by R16-2b bump to 23)":

  test "symexWalkerVersion is now 34 (A9 ASCII case-fold, 33→34)":
    ## R16-1 "21" → … → A2 Slice 1 "27" → A2 Slice 2 "28" → A2 Slice 3 "29"
    ## → A3 Slice 1 "30" → A3 Slice 2 "31" → A3-S2a tuple-yield "32"
    ## → A8 radix formatting "33" → A9 ASCII case-fold "34".
    ## The arithChecks cache-key invariant from R16-1 is preserved — the
    ## version just moved forward.
    check symexWalkerVersion == "34"
