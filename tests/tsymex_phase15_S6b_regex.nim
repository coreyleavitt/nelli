## Phase 15 — Cluster S, cycle S6b: regex walker integration.
##
## Wires the standalone S6a parser (`parseNimRegexToZ3Regex`) into the walker.
## Intercepts Nim `std/re` calls whose pattern argument is a compile-time
## `re"..."` literal:
##   * `s.match(re"pat")`    → a PREFIX of `s[start..]` in the language
##   * `s.contains(re"pat")` → an occurrence in `s[start..]`
##                             (RFC-0005 S8ay: both were full-string
##                             membership with `start` dropped, so the
##                             "match contradiction" pin below was a false
##                             sxUnsat: every string matches `re""`.)
##   * `s.find(re"pat")`     → the leftmost occurrence (RFC-0005 S8ay; was
##                             a `seUnsupportedRegex` deferral).
##   * `s.replace(re"pat",x)`→ regex global replace. Was VERSION-GATED behind
##                             `-d:z3WithSeqReplaceRe` (sxUnknown +
##                             seZ3VersionMissing on every build); RFC-0005
##                             S8aw lowers it in the walker (a literal, a
##                             one-byte class, a class under `+`), so the
##                             wrong claim below is now sxUnsat.
##
## On a pattern whose validity is undecided (a named group, an unread
## escape), the walker emits `seUnsupportedRegex` (sxUnknown); a VALID
## pattern with an unmodelled construct (a backreference, a lookahead) is a
## fresh value, `seZ3StringIncomplete` (RFC-0005 S8ay), never a silent UNSAT
## (ADR-0006, Invariant 3).
##
## Byte-faithful (ADR-0006): the ≤0xFF char-range constraint on every free
## string keeps regex membership in the same byte alphabet as the parser's
## byte-faithful classes, so witnesses round-trip to Nim bytes. This is the
## cluster's highest hang-risk code (Z3 string-solver + regex on a free string);
## the test asserts it terminates with concrete verdicts.
import std/[unittest, strutils]
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

# --- `re""` matches a prefix of every string ---
# RFC-0005 S8ay: this was pinned sxUnsat ("`re""` matches only """), but
# Nim's `match` is a prefix match: `"x".match(re"")` is true.
proc matchEmptyContradiction(s: string) =
  if s.len >= 1 and s.match(re""):
    symexTarget("hit")

# --- backreference: valid, not modelled → a fresh value (RFC-0005 S8ay) ---
proc matchBackref(s: string) =
  if s.match(re"(.)\1"):
    symexTarget("hit")

# --- regex replace → version-gated (this build lacks the gate) ---
proc replaceRe(s: string) =
  if s == "foofoo" and s.replace(re"f+", "x") == "xoxo":
    symexTarget("hit")

suite "symex Phase 15 S6b — regex match walker integration":
  test "match [a-z]+: SAT with a lowercase-led witness":
    # RFC-0005 S8ay: `match` is a prefix match, so only the first byte must
    # be lowercase (this pinned all three).
    let r = symexFind(matchLower, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 3
    check r.witness[0][0] in {'a'..'z'}
    check r.witness[0].match(re"[a-z]+")

  test "match \\d+: SAT with a digit-led witness":
    let r = symexFind(matchDigits, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0].len == 2
    check r.witness[0][0] in {'0'..'9'}
    check r.witness[0].match(re"\d+")

  test "re\"\" matches a prefix of a non-empty string: SAT":
    # RFC-0005 S8ay: was pinned sxUnsat -- a false verdict.
    let r = symexFind(matchEmptyContradiction, tLabel("hit"))
    check r.status == sxSat

  test "backreference re\"(.)\\1\": a fresh value, never a claim":
    # RFC-0005 S8ay: a valid pattern (PCRE accepts it) whose language the
    # walker does not model: `seZ3StringIncomplete` (a fresh bool, a SAT is
    # replay-gated), no longer `seUnsupportedRegex`.
    let r = symexFind(matchBackref, tLabel("hit"))
    check r.status in {sxSat, sxUnknown}
    var named = false
    for e in r.errors:
      if e.kind == seZ3StringIncomplete and "backreference" in e.msg:
        named = true
    check named or r.status == sxSat
    if r.status == sxSat: check r.witness[0].match(re"(.)\1")

  test "regex replace: \"foofoo\".replace(re\"f+\", \"x\") is \"xoox\", so \"xoxo\" is sxUnsat":
    # RFC-0005 S8aw (was sxUnknown + seZ3VersionMissing: the gated
    # `str.replace_re` was never built in).
    let r = symexFind(replaceRe, tLabel("hit"))
    check r.status == sxUnsat
    for e in r.errors: check e.kind != seZ3VersionMissing
