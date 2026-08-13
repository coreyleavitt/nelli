## Phase 15 — Cluster S, cycle S6b: regex walker integration.
##
## Wires the standalone S6a parser (`parseNimRegexToZ3Regex`) into the walker.
## Intercepts Nim `std/re` calls whose pattern argument is a compile-time
## `re"..."` literal:
##   * `s.match(re"pat")`    → Z3 `(seq.in.re s r)`  via `matches(sv, re)` → svBool
##   * `s.contains(re"pat")` → same membership predicate                  → svBool
##   * `s.find(re"pat")`     → DEFERRED: nim-z3 has no `indexOf`-on-regex
##                             API (only substring `indexOf`), so a regex
##                             `find` classifies `seUnsupportedRegex` (sxUnknown).
##   * `s.replace(re"pat",x)`→ regex global replace, VERSION-GATED behind
##                             `-d:z3WithSeqReplaceRe` (absent on this Z3 4.15.0
##                             build) → sxUnknown + seZ3VersionMissing.
##
## On a parser `isErr` (backreference / lookahead / named group — the S6a
## rejected families), the walker emits `seUnsupportedRegex` (sxUnknown), never
## a silent UNSAT (ADR-0006, Invariant 3).
##
## Byte-faithful (ADR-0006): the ≤0xFF char-range constraint on every free
## string keeps regex membership in the same byte alphabet as the parser's
## byte-faithful classes, so witnesses round-trip to Nim bytes. This is the
## cluster's highest hang-risk code (Z3 string-solver + regex on a free string);
## the test asserts it terminates with concrete verdicts.
import std/unittest
import std/re        ## match/find/contains/replace with compiled Regex
import nelli/symex

# --- match: [a-z]+ → SAT, all-lowercase witness ---
proc matchLower(s: string) =
  if s.len == 3 and s.match(re"[a-z]+"):
    symexTarget("hit")

# --- match: \d+ → SAT, numeric witness ---
proc matchDigits(s: string) =
  if s.len == 2 and s.match(re"\d+"):
    symexTarget("hit")

# --- match contradiction: non-empty s can't match the empty-string regex ---
# `re""` matches only "", so a length-1 constraint makes membership UNSAT.
proc matchEmptyContradiction(s: string) =
  if s.len >= 1 and s.match(re""):
    symexTarget("hit")

# --- backreference → seUnsupportedRegex (S6a parser rejects it) ---
proc matchBackref(s: string) =
  if s.match(re"(.)\1"):
    symexTarget("hit")

# --- regex replace → version-gated (this build lacks the gate) ---
proc replaceRe(s: string) =
  if s == "foofoo" and s.replace(re"f+", "x") == "xoxo":
    symexTarget("hit")

suite "symex Phase 15 S6b — regex match walker integration":
  test "match [a-z]+: SAT with an all-lowercase witness":
    let r = symexFind(matchLower, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 3
    for c in r.witness[0]:
      check c in {'a'..'z'}

  test "match \\d+: SAT with a numeric witness":
    let r = symexFind(matchDigits, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 2
    for c in r.witness[0]:
      check c in {'0'..'9'}

  test "match contradiction: non-empty s vs re\"\" (empty) is UNSAT":
    let r = symexFind(matchEmptyContradiction, tLabel("hit"))
    check r.status == sxUnsat

  test "backreference re\"(.)\\1\": sxUnknown + seUnsupportedRegex":
    let r = symexFind(matchBackref, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seUnsupportedRegex

  test "regex replace on 4.15.0: sxUnknown + seZ3VersionMissing":
    let r = symexFind(replaceRe, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.len >= 1
    check r.errors[0].kind == seZ3VersionMissing
