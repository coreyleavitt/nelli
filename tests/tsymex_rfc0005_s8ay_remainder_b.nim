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
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_s8ay_remainder`, `tsymex_rfc0005_s8ay_remainder_c`,
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

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors)
  r

proc findLeftmost(s: string) =
  if s == "xaba" and s.find(re"a") != 1:
    symexTarget("ay_find_leftmost")

proc findSym(s: string) =
  # The leftmost digit is at 2: neither earlier byte is a digit.
  if s.len == 3 and s.find(re"[0-9]") == 2 and s[1] == '7':
    symexTarget("ay_find_sym")

proc findSymHit(s: string) =
  if s.len == 4 and s.find(re"ab") == 2:
    symexTarget("ay_find_sym_hit")

proc findBadStart(s: string) =
  if s == "ab" and s.find(re"a", 3) == -24:
    symexTarget("ay_find_bad_start")

proc matchLenHit(s: string) =
  if s == "abc" and s.matchLen(re"ab") == 2:
    symexTarget("ay_matchlen_hit")

proc matchLenGreedy(s: string) =
  if s == "aaab" and s.matchLen(re"a+") != 3:
    symexTarget("ay_matchlen_greedy")

proc findBoundsHit(s: string) =
  if s == "xab":
    let (first, last) = s.findBounds(re"ab")
    if first == 1 and last == 2:
      symexTarget("ay_findbounds_hit")

proc findBoundsMiss(s: string) =
  if s == "xab":
    let (first, last) = s.findBounds(re"ab")
    if first != 1 or last != 2:
      symexTarget("ay_findbounds_miss")

proc findAllDecline(s: string) =
  if s == "aa" and s.findAll(re"a").len == 5:
    symexTarget("ay_findall")

proc splitDecline(s: string) =
  if s == "a,b" and s.split(re",").len == 5:
    symexTarget("ay_split")

proc replacefDecline(s: string) =
  if s == "ab" and s.replacef(re"(a)", "$1$1") == "zz":
    symexTarget("ay_replacef")

proc capturesMatch(s: string) =
  var m: array[1, string]
  if s == "ab" and s.match(re"(a)b", m) and m[0] == "a":
    symexTarget("ay_captures")

proc tildeCaptures(s: string) =
  if s == "ab" and s =~ re"(a)b":
    if matches[0] == "a":
      symexTarget("ay_tilde")

suite "S8ay (1): contains / match / startsWith / endsWith / find":
  test "find is the leftmost match":
    check verdict(findLeftmost, "ay_find_leftmost").status == sxUnsat
    check verdict(findSym, "ay_find_sym").status == sxUnsat
    let h = verdict(findSymHit, "ay_find_sym_hit")
    check h.status == sxSat
    if h.status == sxSat: check h.witness[0].find(re"ab") == 2

  test "find past the end is PCRE_ERROR_BADOFFSET":
    check verdict(findBadStart, "ay_find_bad_start").status == sxSat

  test "matchLen (a compile crash at 04e3a97)":
    check verdict(matchLenHit, "ay_matchlen_hit").status == sxSat
    check verdict(matchLenGreedy, "ay_matchlen_greedy").status == sxUnsat

  test "findBounds (a compile crash at 04e3a97)":
    check verdict(findBoundsHit, "ay_findbounds_hit").status == sxSat
    check verdict(findBoundsMiss, "ay_findbounds_miss").status == sxUnsat

  test "findAll / split / replacef decline, never claim":
    for r in [verdict(findAllDecline, "ay_findall"),
              verdict(splitDecline, "ay_split"),
              verdict(replacefDecline, "ay_replacef")]:
      check r.status == sxUnknown
      check hasKind(r.errors, seZ3StringIncomplete)

  test "the captures overloads: the `matches` write is not dropped":
    # RFC-0005 S8bb re-pin: the write is modelled (std/re's rule, see
    # `regex_parser.lowerCapture`), so both reach their target (was the
    # sxUnknown decline).
    check verdict(capturesMatch, "ay_captures").status == sxSat
    check verdict(tildeCaptures, "ay_tilde").status == sxSat
