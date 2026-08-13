## Phase 15 code-review CR-11 + CR-18: maxSplitParts cap wired into concrete-inline split.
##
## CR-11: the concrete-inline split paths (empty-sep byte-iteration and both-literal)
##        had no cap on parts.len — a huge literal like "x".repeat(10_000).split("")
##        would emit 10_000+ Z3 store calls before anything stopped it (compile-time DoS).
##
## CR-18: the `maxSplitParts` setting (budget.maxSplitParts, default 8) was DEFINED
##        but UNWIRED — no reachable code read it (the symbolic split took sxUnknown
##        first). Now wired into the concrete-inline paths.
##
## FIX (CR-11 + CR-18 together):
##   * If parts.len > maxSplitParts (and cap > 0), classify sxUnknown
##     (seZ3StringIncomplete) BEFORE emitting Z3 stores. Applies to BOTH:
##       (a) empty-sep: literal.split("") → byte array
##       (b) concrete-inline: literal.split(literal-sep)
##   * maxSplitParts added to the canonicalize(SymexSettings) cache key
##     (was excluded while unwired per CR-2 audit; now included).
##
## DoD:
##   1. A concrete split producing > maxSplitParts parts (cap=3, 4-part literal)
##      → sxUnknown + seZ3StringIncomplete.
##   2. A small concrete split (parts.len <= cap) → sxSat as usual.
##   3. Empty-sep split that would exceed the cap → sxUnknown.
##   4. maxSplitParts now produces DISTINCT canonical forms (cache-key participation).
##
## Verdict change: large-literal split: silent-huge-Z3-build → sxUnknown.
## The default cap (8) already existed; this wire means programs where split
## parts > 8 now classify sxUnknown instead of building huge Z3 terms.
## Version bump decision: the behaviour change (huge split now sxUnknown) is real
## and stale cache entries built before this wiring would be wrong (they might have
## completed successfully with a smaller literal or a different cap). HOWEVER, the
## default cap (8) means any pre-existing splits ≤ 8 parts are UNCHANGED (the cap
## applies only to > cap). Since no pre-existing test had a split > 8 parts, and
## the cache key now includes maxSplitParts (so settings changes rotate the cache
## correctly), we do NOT bump symexWalkerVersion: the structural change (cache-key
## addition) is sufficient to isolate new vs old results for large-literal cases.
## Programs with ≤ default-cap parts are verdict-identical.

import std/unittest
import std/strutils
import nelli/symex
import nelli/smt/canonicalize
import nelli/smt/types

# --- SUT: concrete both-literal split with 4 parts (cap=3 → sxUnknown) ---
proc splitFourParts(s: string) =
  if s == "x":
    let parts = "a,b,c,d".split(",")   # 4 parts
    if parts.len == 4:
      symexTarget("hit")

# --- SUT: concrete both-literal split with 2 parts (cap=3 → sxSat) ---
proc splitTwoParts(s: string) =
  if s == "x":
    let parts = "a,b".split(",")   # 2 parts
    if parts.len == 2:
      symexTarget("hit")

# --- SUT: empty-sep split producing 5 parts (cap=3 → sxUnknown) ---
proc splitEmptySepFiveParts(s: string) =
  if s == "x":
    let parts = "abcde".split("")   # 5 parts ("a","b","c","d","e")
    if parts.len == 5:
      symexTarget("hit")

# --- Settings: cap=3 (tighter than default 8 for the test) ---
const cap3 = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxSplitParts = 3

suite "Phase 15 CR-11 + CR-18 — maxSplitParts cap wired into concrete-inline split":

  test "CR-11: concrete split >cap parts → sxUnknown + seZ3StringIncomplete (DoS guard)":
    ## 4-part split with cap=3: must classify sxUnknown, NOT build a huge Z3 term.
    ## RED before fix: this test passed without the cap (the split returned sxSat
    ## by emitting 4 Z3 store calls — not a huge DoS here, but proves the cap fires).
    let r = symexFind(splitFourParts, tLabel("hit"), cap3)
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seZ3StringIncomplete

  test "CR-18: small split (<=cap parts) still yields sxSat (cap does not over-classify)":
    ## 2-part split with cap=3: must still succeed. The cap only fires when exceeded.
    let r = symexFind(splitTwoParts, tLabel("hit"), cap3)
    check r.status == sxSat
    check r.witness[0] == "x"

  test "CR-11: empty-sep split >cap parts → sxUnknown (same guard on path (a))":
    ## 5-byte literal split with cap=3: path (a) (empty-sep) must also cap.
    let r = symexFind(splitEmptySepFiveParts, tLabel("hit"), cap3)
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seZ3StringIncomplete

  test "CR-18: maxSplitParts NOW changes canonical form (wired into cache key)":
    ## Two settings differing only in maxSplitParts must produce distinct keys.
    ## (Previously == per CR-2 audit; now != because the cap is wired.)
    var s0 = defaultSymexSettings()
    var s1 = s0
    s1.budget.maxSplitParts = s0.budget.maxSplitParts + 1
    check canonicalize(s0) != canonicalize(s1)
