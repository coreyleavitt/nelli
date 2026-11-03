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
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_s8ay_remainder`, `tsymex_rfc0005_s8ay_remainder_b`,
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

# ---- item 2: PCRE's reading of the pattern ------------------------------------

proc dotNewline(s: string) =
  if s == "\n" and s.match(re"."):
    symexTarget("ay_dot_newline")

proc notDigit(s: string) =
  if s == "a" and not s.match(re"\D"):
    symexTarget("ay_not_digit")

proc newlineEscape(s: string) =
  if s == "\n" and not s.match(re"\n"):
    symexTarget("ay_newline_escape")

proc vtSpace(s: string) =
  if s == "\v" and not s.match(re"\s"):
    symexTarget("ay_vt_space")

proc caretAnchor(s: string) =
  if s == "b" and not s.match(re"^b"):
    symexTarget("ay_caret")

proc caretMid(s: string) =
  if s == "ab" and s.contains(re"^b"):
    symexTarget("ay_caret_mid")

proc dollarNewline(s: string) =
  # `$` matches before a final `\n`.
  if s == "a\n" and not s.match(re"a$"):
    symexTarget("ay_dollar")

proc dollarMid(s: string) =
  if s == "a\nb" and s.contains(re"a$"):
    symexTarget("ay_dollar_mid")

suite "S8ay (2): the pattern is read as PCRE reads it":

  test "'.' excludes \\n":
    check verdict(dotNewline, "ay_dot_newline").status == sxUnsat

  test "\\D is a complement, \\n a newline, \\s holds VT":
    check verdict(notDigit, "ay_not_digit").status == sxUnsat
    check verdict(newlineEscape, "ay_newline_escape").status == sxUnsat
    check verdict(vtSpace, "ay_vt_space").status == sxUnsat

  test "^ anchors at the subject start":
    check verdict(caretAnchor, "ay_caret").status == sxUnsat
    check verdict(caretMid, "ay_caret_mid").status == sxUnsat

  test "$ matches at the end or before a final \\n":
    check verdict(dollarNewline, "ay_dollar").status == sxUnsat
    check verdict(dollarMid, "ay_dollar_mid").status == sxUnsat

# ---- item 3: re vs rex --------------------------------------------------------

proc rexSpace(s: string) =
  if s == "ab" and not s.match(rex"a b"):
    symexTarget("ay_rex_space")

proc reSpace(s: string) =
  if s == "ab" and s.match(re"a b"):
    symexTarget("ay_re_space")

suite "S8ay (3): re and rex are distinct":

  test "rex ignores whitespace":
    check verdict(rexSpace, "ay_rex_space").status == sxUnsat

  test "re keeps it":
    check verdict(reSpace, "ay_re_space").status == sxUnsat

# ---- item 4: a pattern PCRE rejects raises RegexError -------------------------

proc rejectedCaught(s: string) =
  try:
    if s.match(re"a**"):
      discard
  except RegexError:
    symexTarget("ay_rejected_caught")

proc rejectedAsValueError(s: string) =
  try:
    if s.contains(re"[z-a]"):
      discard
  except ValueError:
    symexTarget("ay_rejected_value_error")

proc rejectedMsg(s: string) =
  try:
    discard s.find(re"(ab")
  except RegexError:
    if getCurrentExceptionMsg() == s:
      symexTarget("ay_rejected_msg")

proc rejectedNotReached(s: string) =
  try:
    if s.match(re"a**"):
      symexTarget("ay_rejected_after")
  except RegexError:
    discard

proc rejectedRaises(s: string): bool =
  s.match(re"x{3,2}")

suite "S8ay (4): a rejected pattern is a RegexError raise":

  test "the handler is reached":
    check verdict(rejectedCaught, "ay_rejected_caught").status == sxSat

  test "RegexError is a ValueError":
    check verdict(rejectedAsValueError, "ay_rejected_value_error").status == sxSat

  test "the message is Nim's, caret at PCRE's offset":
    let r = verdict(rejectedMsg, "ay_rejected_msg")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == "missing )\n(ab\n   ^\n"

  test "nothing after the raise is reached":
    check verdict(rejectedNotReached, "ay_rejected_after").status == sxUnsat

  test "the raise is the routine's exit":
    let r = symexFind(rejectedRaises, tRaisedExn("RegexError"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised
