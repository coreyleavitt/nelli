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

suite "symex Phase 16 A7-S1 — walker version pin":

  test "walker version is now 35 (A7-S1 Rune foundation, 34→35)":
    ## A7-S1 is the first verdict-changing Rune slice: previously sxUnknown
    ## (Rune landed as itDistinct / uninterp sort), now sxSat/sxUnsat.
    ## The cache key must rotate so stale sxUnknown results are invalidated.
    ## (Prior: A9 33→34; A8 32→33; A3-S2a 31→32; A3-S1 29→30.)
    check symexWalkerVersion == "35"
