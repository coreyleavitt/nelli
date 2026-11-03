## RFC-0005 (soundness channels) slice S8ay -- S8aw's remainder.
##
## Nim's `std/re` entry points each ask PCRE a different question, and the
## walker answered all of them with one: full-string membership of the
## S6a reading of the pattern (`matches(s, R)`), with the `start` argument
## dropped. Wrong verdicts at 04e3a97 (each pinned below, RED first):
##   * `contains(s, R)` is "R occurs somewhere": `"abc".contains(re"b")`
##     was false to the walker -- a false sxSat for `not contains`;
##   * `match(s, R, start)` is "R matches a PREFIX of `s[start..]`" (PCRE's
##     ANCHORED), and true for an out-of-range `start` (`matchLen` returns
##     PCRE_ERROR_BADOFFSET, which is not -1): `"abc".match(re"")` and
##     `"abc".match(re"b", 1)` were false to the walker (false sxSat), and
##     S6b's "match contradiction" pin (`s.len >= 1 and s.match(re"")` is
##     sxUnsat) was itself a false sxUnsat;
##   * `contains(s, R, start)` dropped `start` (a false sxUnsat);
##   * the S6a reading was not PCRE's: `.` matched `\n`, `\D \W \S \n \t`
##     were literal letters, `^ $` literal bytes;
##   * `rex"..."` (extended: whitespace and `#` comments ignored) was read
##     as `re"..."`;
##   * a pattern PCRE rejects (`re"a**"`) never raised the `RegexError` Nim
##     raises at run time -- a handler target was a false sxUnsat;
##   * `matchLen`, `findBounds`, `findAll`, `replacef` and `=~` crashed the
##     compile ("node has no type"); the captures overloads
##     (`match(s, R, matches)`) dropped the `matches` write -- a false
##     sxUnsat for any claim on a capture.
## Item 5: `replace(s, re, by)` over a receiver of unknown length is exact
## past S8aw's 16-byte unroll.
## Item 6: a query only step 1c refutes no longer pays step 1's
## full-theory search first (S8aw's join walk: 10,000,930 units at
## 8b2508f, about 20 s on Z3 5.1; pinned by units, this file's .nim.cfg).
##
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8ay_remainder_b`, `tsymex_rfc0005_s8ay_remainder_c`,
## `tsymex_rfc0005_s8ay_remainder_d`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 94 s).

import std/[unittest, strutils, re]
import z3
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/regex_parser
import nelli/smt/runtime

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8ay_remainder needs -d:symexQueryStats (its .nim.cfg)".}

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors)
  r

# ---- item 1: each entry point asks its own question --------------------------

proc containsMid(s: string) =
  if s == "abc" and not s.contains(re"b"):
    symexTarget("ay_contains_mid")

proc containsSym(s: string) =
  # Reachable: any string with a digit after its first byte.
  if s.len == 3 and s[0] == 'x' and s.contains(re"[0-9]"):
    symexTarget("ay_contains_sym")

proc matchEmpty(s: string) =
  if s == "abc" and not s.match(re""):
    symexTarget("ay_match_empty")

proc matchContradiction(s: string) =
  # S6b pinned this sxUnsat ("a non-empty string cannot match the empty
  # pattern"); `match` is a prefix match, so every string matches re"".
  if s.len >= 1 and s.match(re""):
    symexTarget("ay_match_contradiction")

proc matchPrefix(s: string) =
  if s.len == 2 and s.match(re"a") and s[1] == 'z':
    symexTarget("ay_match_prefix")

proc matchStart(s: string) =
  if s == "abc" and not s.match(re"b", 1):
    symexTarget("ay_match_start")

proc matchBadStart(s: string) =
  # `matchLen` returns PCRE_ERROR_BADOFFSET (-24) past the end: not -1.
  if s == "ab" and s.match(re"z", 5):
    symexTarget("ay_match_bad_start")

proc containsStart(s: string) =
  if s == "ab" and s.contains(re"b", 1):
    symexTarget("ay_contains_start")

proc containsBadStart(s: string) =
  if s == "ab" and s.contains(re"", 3):
    symexTarget("ay_contains_bad_start")

proc startsWithMid(s: string) =
  if s == "abc" and s.startsWith(re"b"):
    symexTarget("ay_starts_mid")

proc startsWithHit(s: string) =
  if s == "abc" and s.startsWith(re"a."):
    symexTarget("ay_starts_hit")

proc endsWithHit(s: string) =
  if s == "abc" and s.endsWith(re"b."):
    symexTarget("ay_ends_hit")

proc endsWithRun(s: string) =
  # A greedy run at the end: PCRE's match is the longest, so `endsWith` is
  # "some non-empty suffix is in the language". Unbounded again (RFC-0005
  # S8bp, `mergeMemberships`): S8ay bounded it at `s.len <= 8`, Z3 4.13.4
  # leaving it undecided past maxSeqLen (`beSolverUndef`).
  if s.endsWith(re"b+") and not s.contains(re"b"):
    symexTarget("ay_ends_run")

proc endsWithAltOrder(s: string) =
  # "ab".endsWith(re"a|ab") is false (PCRE takes `a` at 0); the language
  # reading says true. S8ay declined it; RFC-0005 S8bb models PCRE's
  # choice, so it is unreachable.
  if s == "ab" and s.endsWith(re"a|ab"):
    symexTarget("ay_ends_alt")

suite "S8ay (1): contains / match / startsWith / endsWith / find":

  test "contains is an occurrence anywhere: a false sxSat at 04e3a97":
    check verdict(containsMid, "ay_contains_mid").status == sxUnsat

  test "contains over a symbolic receiver is solved":
    let r = verdict(containsSym, "ay_contains_sym")
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0].contains(re"[0-9]")

  test "match is a prefix match: re\"\" matches every string":
    check verdict(matchEmpty, "ay_match_empty").status == sxUnsat

  test "S6b's 'match contradiction' is reachable (its sxUnsat was false)":
    check verdict(matchContradiction, "ay_match_contradiction").status == sxSat

  test "a prefix match leaves the rest free":
    let r = verdict(matchPrefix, "ay_match_prefix")
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0] == "az"

  test "match honours start":
    check verdict(matchStart, "ay_match_start").status == sxUnsat

  test "match past the end is true (PCRE_ERROR_BADOFFSET is not -1)":
    check verdict(matchBadStart, "ay_match_bad_start").status == sxSat

  test "contains honours start":
    check verdict(containsStart, "ay_contains_start").status == sxSat

  test "contains past the end is false":
    check verdict(containsBadStart, "ay_contains_bad_start").status == sxUnsat

  test "startsWith is anchored at 0":
    check verdict(startsWithMid, "ay_starts_mid").status == sxUnsat
    check verdict(startsWithHit, "ay_starts_hit").status == sxSat

  test "endsWith on a fixed-length pattern":
    check verdict(endsWithHit, "ay_ends_hit").status == sxSat

  test "endsWith on a greedy run at the end":
    check verdict(endsWithRun, "ay_ends_run").status == sxUnsat

  test "endsWith whose answer is PCRE's match order (RFC-0005 S8bb)":
    check verdict(endsWithAltOrder, "ay_ends_alt").status == sxUnsat
