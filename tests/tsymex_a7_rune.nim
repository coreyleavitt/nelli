## Phase 16 A7-S1 — Unicode Rune codepoint model foundation (ADR-0017, Path B).
##
## `Rune = distinct int32` from std/unicode is modelled as `svInt` (Z3Int) pinned
## [0, 0x10FFFF].  Path B is ADDITIVE — the byte-faithful string model (ADR-0006,
## ≤0xFF char range) is UNTOUCHED.  Zero S-cluster edits.
##
## S1 scope (this file):
##   * free Rune param → `svInt` pinned [0, 0x10FFFF]
##   * `ord(r)` / `int(r)` → identity on the svInt term
##   * `Rune(intExpr)` → coerce int to svInt (no new constraint beyond the param pin)
##   * comparisons / equality → Z3Int (in)equality
##   * soundness/UNSAT direction: `r.ord > 0x10FFFF` must be sxUnsat
##
## S2 (`$r` UTF-8 encoding) and S3 (concrete `runes()` / `runeLen()`) are separate
## slices with their own version bumps.
##
## Walker version: v34 → v35 (first verdict flip: Rune SUT now sxSat/sxUnsat
## instead of sxUnknown).

import std/[unittest, unicode]
import proptest/symex
import proptest/smt/canonicalize

# ---------------------------------------------------------------------------
# SUTs — must be at module scope so getImpl resolves them at macro time.
# ---------------------------------------------------------------------------

# SUT 1: free Rune param, equality with a Rune literal.
proc runeEq(r: Rune) =
  if r == Rune(0x41): symexTarget("hit")

# SUT 2: Rune comparison via ord (strictly greater).
# std/unicode in Nim 2.2.10 exports `==` and `<%`/`<=%` but NOT bare `<`/`>`.
# `r.ord` lowers to `ord(r)` → int; int `>` int is always available.
proc runeCmp(r: Rune) =
  if r.ord > 0x1000: symexTarget("big")

# SUT 3: ord arithmetic on two Rune params + inequality.
# `r1.ord` lowers to `ord(r1)` in the typed AST — intercepted as identity.
proc runeOrdArith(r1: Rune, r2: Rune) =
  if r1.ord + r2.ord == 0x82 and r1 != r2: symexTarget("sum")

# SUT 4: Rune constructed from a symbolic int param.
proc runeFromInt(n: int) =
  let r = Rune(n)
  if r == Rune(0x41): symexTarget("fromInt")

# SUT 5: soundness — r.ord > 0x10FFFF must be UNSAT (the [0,0x10FFFF] pin holds).
proc runeOob(r: Rune) =
  if r.ord > 0x10FFFF: symexTarget("oob")

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

suite "symex Phase 16 A7-S1 — Rune codepoint model (Path B)":

  test "free Rune param: r == Rune(0x41) → sxSat, witness 0x41":
    ## Rune is now classified as tInt(64,signed) pinned [0,0x10FFFF].
    ## Z3 finds r == 65 (U+0041 'A') uniquely.
    ## witness[0] has type int (Rune→tInt witness reads as int).
    let r = symexFind(runeEq, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] == 0x41

  test "Rune comparison via ord: r.ord > 0x1000 → sxSat, witness > 0x1000":
    ## ord(r) lowers to identity on svInt; Z3 picks any codepoint in (0x1000, 0x10FFFF].
    ## (std/unicode Nim 2.2.10 exports `==` but not bare `<`/`>` for Rune.)
    let r = symexFind(runeCmp, tLabel("big"))
    check r.status == sxSat
    check r.witness[0] > 0x1000

  test "ord arithmetic: r1.ord + r2.ord == 0x82 and r1 != r2 → sxSat, distinct":
    ## ord(r) is intercepted as identity; + is Z3Int addition; != is Z3Int neq.
    ## Many solutions: e.g. r1=1, r2=129 or r1=64, r2=66.
    let r = symexFind(runeOrdArith, tLabel("sum"))
    check r.status == sxSat
    check r.witness[0] + r.witness[1] == 0x82
    check r.witness[0] != r.witness[1]

  test "Rune(intExpr) from symbolic int → sxSat, witness 0x41":
    ## Rune(n) is a nnkConv that falls through to parseExpr(n) (identity).
    ## Z3 solves n == 0x41 directly.
    let r = symexFind(runeFromInt, tLabel("fromInt"))
    check r.status == sxSat
    check r.witness[0] == 0x41

  test "soundness: r.ord > 0x10FFFF → sxUnsat (Invariant 3 range pin holds)":
    ## The [0, 0x10FFFF] pin is the soundness anchor (ADR-0017 §SOUNDNESS).
    ## A Rune value outside that range would be a false model — must be UNSAT.
    let r = symexFind(runeOob, tLabel("oob"))
    check r.status == sxUnsat

# ---------------------------------------------------------------------------
# A7-S2 SUTs — $r (Rune → UTF-8 string)
# Must be at module scope.
# ---------------------------------------------------------------------------

# SUT 6: free Rune param, 1-byte ASCII — $r == "A" → sxSat, witness 0x41.
proc runeToStrAscii(r: Rune) =
  if $r == "A": symexTarget("ascii")

# SUT 7: free Rune param, 2-byte é — $r == "\xC3\xA9" → sxSat, witness 0xE9.
proc runeToStr2Byte(r: Rune) =
  if $r == "\xC3\xA9": symexTarget("eacute")

# SUT 8: free Rune param, 3-byte € — $r == "\xE2\x82\xAC" → sxSat, witness 0x20AC.
proc runeToStr3Byte(r: Rune) =
  if $r == "\xE2\x82\xAC": symexTarget("euro")

# SUT 9: free Rune param, 4-byte emoji — $r == "\xF0\x9F\x98\x80" → sxSat, witness 0x1F600.
# High-plane (> 0x3FFFF): proves byte-level encoding beats BV18 char limit.
proc runeToStr4Byte(r: Rune) =
  if $r == "\xF0\x9F\x98\x80": symexTarget("emoji")

# SUT 10: soundness UNSAT — $r == "A" and r.ord > 0x42 is impossible
# (only r == 0x41 gives 1-byte "A", but 0x41 is not > 0x42).
proc runeToStrUnsat(r: Rune) =
  if $r == "A" and r.ord > 0x42: symexTarget("impossible")

# SUT 11: REGRESSION guard — plain int $n must still route to DECIMAL string.
proc intToStrRegression(n: int) =
  if $n == "42": symexTarget("forty_two")

suite "symex Phase 16 A7-S2 — $r UTF-8 encoding":

  test "$Rune: r → 1-byte ASCII 'A' → sxSat, witness 0x41":
    ## After S2: $r uses runeToUtf8Sym (4-branch ITE). 1-byte branch: r < 0x80
    ## → fromCode(r). Z3 finds r == 65 (== 0x41 == 'A').
    let r = symexFind(runeToStrAscii, tLabel("ascii"))
    check r.status == sxSat
    check r.witness[0] == 0x41

  test "$Rune: r → 2-byte UTF-8 for é (U+00E9) → sxSat, witness 0xE9":
    ## lead = 0xC0 + 0xE9/64 = 0xC3; cont = 0x80 + 0xE9 mod 64 = 0xA9 → "\xC3\xA9".
    let r = symexFind(runeToStr2Byte, tLabel("eacute"))
    check r.status == sxSat
    check r.witness[0] == 0xE9

  test "$Rune: r → 3-byte UTF-8 for € (U+20AC) → sxSat, witness 0x20AC":
    ## lead=0xE2, cont1=0x82, cont2=0xAC → "\xE2\x82\xAC".
    let r = symexFind(runeToStr3Byte, tLabel("euro"))
    check r.status == sxSat
    check r.witness[0] == 0x20AC

  test "$Rune: r → 4-byte UTF-8 for 😀 (U+1F600) → sxSat, witness 0x1F600":
    ## High-plane codepoint (> 0x3FFFF = BV18 max): byte-level encoding is sound
    ## (probe P7c). lead=0xF0, cont1=0x9F, cont2=0x98, cont3=0x80 → "\xF0\x9F\x98\x80".
    let r = symexFind(runeToStr4Byte, tLabel("emoji"))
    check r.status == sxSat
    check r.witness[0] == 0x1F600

  test "soundness UNSAT: $r == 'A' and r.ord > 0x42 → sxUnsat (injective encoding)":
    ## Only r == 0x41 maps to the 1-byte string "A"; r > 0x42 is incompatible.
    let r = symexFind(runeToStrUnsat, tLabel("impossible"))
    check r.status == sxUnsat

  test "REGRESSION: $plainInt still routes to decimal (iekIntToStr unbroken)":
    ## A7-S2 must NOT reroute plain int $n to the Rune encoder.
    ## $42 == "42" must remain sxSat via iekIntToStr → toStr (Z3 int.to.str).
    let r = symexFind(intToStrRegression, tLabel("forty_two"))
    check r.status == sxSat
    check r.witness[0] == 42

suite "symex Phase 16 A7-S1+S2 — walker version pin":

  test "walker version is now 37 (A7-S3 concrete runes/runeLen + degrade, 36→37)":
    ## A7-S3 adds parse-time literal decode + seZ3StringIncomplete classify;
    ## bump 36→37 rotates any stale cache entries.
    ## (Prior: A7-S2 35→36; A7-S1 34→35; A9 33→34; A8 32→33; A3-S2a 31→32.)
    check symexWalkerVersion == "37"
