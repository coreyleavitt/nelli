## Phase 16 A7-S3 — concrete `runes` / `runeLen` + symbolic DEGRADE (ADR-0017).
##
## A7-S3 is the final slice of Cluster A7 and the last slice of Phase 16.
## It adds:
##   * `runeLen(lit)` / `lit.runeLen` over a STRING LITERAL → concrete rune count
##     as a numeral (decoded in Nim at parse time via unicode.runeLen).
##   * `for r in lit.runes:` over a LITERAL string → static concrete unroll:
##     bind the loop variable `r: Rune` (= svInt) to each decoded codepoint and
##     run the for-body once per rune. Callee-origin guard: only std/unicode.runes
##     is intercepted (a user-defined `runes` iterator is passed to A3 or degrades).
##   * DEGRADE (MANDATORY): `runeLen(s)` / `for r in s.runes:` over a SYMBOLIC
##     string → classified `seZ3StringIncomplete` (sxUnknown, Invariant 3 — never
##     a crash or hang). Symbolic UTF-8 decode = variable-length grouping over an
##     unknown byte stream; no quantifier-free Z3 encoding exists.
##   * REGRESSION: a user-defined proc named `runeLen` whose owner is NOT
##     `std/unicode` is NOT hijacked by the A7-S3 intercept.
##
## Walker version: v36 → v37 (new concrete-decode + symbolic-degrade behaviour).

import std/[unittest, unicode, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs
# ---------------------------------------------------------------------------

# SUT 1: runeLen("A€") == 2 — concrete decode to numeral at parse time.
# "A" is 1 byte (U+0041), "€" is 3 bytes (U+20AC) → 2 runes.
# Condition is concrete-true → target always reached → sxSat.
proc sutRuneLenLiteral(r: Rune) =
  if runeLen("A€") == 2:
    symexTarget("runelen2")

# SUT 2: for r in literal.runes — concrete unroll.
# "A€" has runes [0x41, 0x20AC]. The second rune has ord 0x20AC (€).
# Gates on the € codepoint → sxSat with witness to that iteration.
proc sutRunesIterLiteral(x: int) =
  for r in "A€".runes:
    if r.ord == 0x20AC:
      symexTarget("euro_iter")

# SUT 3: DEGRADE — for r in symbolic_s.runes → seZ3StringIncomplete, sxUnknown.
# UTF-8 grouping over an unknown byte stream has no quantifier-free Z3 encoding.
# The engine must NOT hang (gate: rc=0, bounded by dt-bounded.sh 200s timeout).
proc sutRunesIterSymbolic(s: string) =
  for r in s.runes:
    if r.ord == 0x41:
      symexTarget("runes_sym")

# SUT 4: DEGRADE — runeLen(symbolic_s) → seZ3StringIncomplete, sxUnknown.
proc sutRuneLenSymbolic(s: string) =
  if runeLen(s) == 2:
    symexTarget("runelen_sym")

# SUT 5 REGRESSION: user-defined `runeLen` with a non-unicode origin (int→int).
# Our origin guard (owner.strVal == "unicode") must NOT grab this proc.
# Falls through to normal user-proc walk: runeLen(n) = n * 2;
# if n * 2 == 6 → n == 3 → sxSat, witness == 3.
proc runeLen(x: int): int = x * 2

proc sutUserRuneLen(n: int) =
  if runeLen(n) == 6:
    symexTarget("userRuneLen")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex Phase 16 A7-S3 — concrete runes / runeLen (Part A)":

  test "A7-S3-1: runeLen(literal) decoded to concrete numeral → sxSat (condition always true)":
    ## runeLen("A€") is decoded at parse time → int literal 2.
    ## Condition `2 == 2` is concrete-true; any valid Rune witness satisfies it.
    let r = symexFind(sutRuneLenLiteral, tLabel("runelen2"))
    check r.status == sxSat

  test "A7-S3-2: for r in literal.runes unrolls → sxSat on specific codepoint gate":
    ## "A€" has 2 runes: 0x41 ('A'), 0x20AC ('€').
    ## Second iteration: r.ord == 0x20AC → true → target reached → sxSat.
    let r = symexFind(sutRunesIterLiteral, tLabel("euro_iter"))
    check r.status == sxSat

suite "symex Phase 16 A7-S3 — symbolic DEGRADE (Part B, MANDATORY)":

  test "A7-S3-3: for r in s.runes (symbolic s) → sxUnknown + seZ3StringIncomplete (no hang)":
    ## Symbolic UTF-8 decode → variable-length grouping with no QF Z3 encoding.
    ## Must classify seZ3StringIncomplete, never crash or hang (Invariant 3).
    let r = symexFind(sutRunesIterSymbolic, tLabel("runes_sym"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seZ3StringIncomplete and e.severity == sevError:
        sawKind = true
    check sawKind

  test "A7-S3-4: runeLen(symbolic s) → sxUnknown + seZ3StringIncomplete (no hang)":
    ## runeLen over a symbolic string: same reason — symbolic UTF-8 grouping.
    ## Must classify seZ3StringIncomplete, never crash or hang (Invariant 3).
    let r = symexFind(sutRuneLenSymbolic, tLabel("runelen_sym"))
    check r.status == sxUnknown
    var sawKind = false
    for e in r.errors:
      if e.kind == seZ3StringIncomplete and e.severity == sevError:
        sawKind = true
    check sawKind

suite "symex Phase 16 A7-S3 — regression guard":

  test "A7-S3-5: user-defined runeLen (int→int, non-unicode origin) NOT hijacked":
    ## The origin guard (owner.strVal == \"unicode\") must prevent intercepting
    ## a same-named user proc. The user proc runeLen(n) = n*2 is walked normally:
    ## n*2 == 6 → n == 3 → sxSat, witness == 3.
    ## If the guard is wrong, this would degrade to seZ3StringIncomplete (regression).
    let r = symexFind(sutUserRuneLen, tLabel("userRuneLen"))
    check r.status == sxSat
    check r.witness[0] == 3
    for e in r.errors:
      check e.kind != seZ3StringIncomplete

suite "symex Phase 16 A7-S3 — walker version pin":

  test "walker version floor >= 37 (A7-S3 introduced at 37)":
    ## A7-S3 adds parse-time literal decode + seZ3StringIncomplete classify
    ## for symbolic runes/runeLen; bump 36→37 rotates any stale entries.
    ## (Prior: A7-S2 35→36; A7-S1 34→35; A9 33→34; A8 32→33; A3-S2a 31→32.)
    ## SW pin idiom (RFC §Version-pin discipline, Corey-decided synthesis
    ## 2026-07-12): this incidental feature-test pin migrates to a tolerant
    ## `>=` floor (only the canonical tsymex_phase15_CR2_cachekey.nim keeps
    ## brittle `==`).
    check parseInt(symexWalkerVersion) >= 37
