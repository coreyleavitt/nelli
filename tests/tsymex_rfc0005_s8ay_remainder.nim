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
import std/[unittest, strutils, re]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

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
  # "some non-empty suffix is in the language".
  if s.endsWith(re"b+") and not s.contains(re"b"):
    symexTarget("ay_ends_run")

proc endsWithAltOrder(s: string) =
  # "ab".endsWith(re"a|ab") is false (PCRE takes `a` at 0); the language
  # reading says true. Not claimed.
  if s == "ab" and s.endsWith(re"a|ab"):
    symexTarget("ay_ends_alt")

proc findLeftmost(s: string) =
  if s == "xaba" and s.find(re"a") != 1:
    symexTarget("ay_find_leftmost")

proc findSym(s: string) =
  # The leftmost digit is at 2: neither earlier byte is a digit.
  if s.find(re"[0-9]") == 2 and s[0] in {'0'..'9'}:
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
  if s == "xab" and s.findBounds(re"ab") == (1, 2):
    symexTarget("ay_findbounds_hit")

proc findBoundsMiss(s: string) =
  if s == "xab" and s.findBounds(re"ab") != (1, 2):
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

  test "endsWith whose answer is PCRE's match order: never claimed":
    let r = verdict(endsWithAltOrder, "ay_ends_alt")
    check r.status == sxUnknown
    check hasKind(r.errors, seZ3StringIncomplete)

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
    check verdict(capturesMatch, "ay_captures").status == sxUnknown
    check verdict(tildeCaptures, "ay_tilde").status == sxUnknown

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

# ---- item 5: exact regex replace past 16 bytes --------------------------------

proc pastUnroll(s: string) =
  if s.len > 40 and s.replace(re"a", "") == "b":
    symexTarget("ay_past_unroll")

proc pastUnrollPair(s: string) =
  if s.len > 20 and s.replace(re"aa", "x") == "xa":
    symexTarget("ay_past_unroll_pair")

proc pastUnrollRun(s: string) =
  if s.len > 20 and s.replace(re"f+", "x") == "xoxo":
    symexTarget("ay_past_unroll_run")

suite "S8ay (5): regex replace is exact past 16 bytes":

  test "a deletion over a 41+ byte receiver: sxSat, untainted":
    let r = verdict(pastUnroll, "ay_past_unroll")
    check r.status == sxSat
    check not hasKind(r.errors, seZ3StringIncomplete)
    if r.status == sxSat:
      check r.witness[0].len > 40
      check r.witness[0].replace(re"a", "") == "b"

  test "a two-byte literal: an impossible result is sxUnsat":
    check verdict(pastUnrollPair, "ay_past_unroll_pair").status == sxUnsat

  test "a greedy run over a 21+ byte receiver: sxSat":
    let r = verdict(pastUnrollRun, "ay_past_unroll_run")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].replace(re"f+", "x") == "xoxo"

suite "S8ay: walker version floor":
  test "symexWalkerVersion >= 198":
    check parseInt(symexWalkerVersion) >= 198
