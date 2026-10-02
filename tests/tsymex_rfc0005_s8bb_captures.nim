## RFC-0005 (soundness channels) slice S8bb, item 5 -- the constructs S8ay
## left undecided (named groups, inline options, `\p{..}`, the `(*...)`
## verbs) and the captures overloads.
##
## At ae08bfd every one of these calls declined (sxUnknown): the pattern
## reader stopped at the construct, and a call with a `matches` array was
## not lowered at all (the write into the array was not modelled). Each pin
## below is a verdict `std/re` decides concretely (the expected values were
## probed against Nim 2.2.10's `std/re`, PCRE 8.45).
import std/[unittest, strutils, re]
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors) & " witness=" &
             (if r.status in {sxSat, sxRaised}: $r.witness else: "-")
  r

# ---- the constructs the reader now reads ---------------------------------------

proc namedGroup(s: string) =
  if s == "ab" and not s.match(re"(?<n>a)b"):
    symexTarget("bb_named")

proc namedGroupSym(s: string) =
  if s.match(re"(?P<word>[a-c]+)$") and s.len == 2 and s[1] == 'c':
    symexTarget("bb_named_sym")

proc caseless(s: string) =
  if s == "AB" and not s.match(re"(?i)ab"):
    symexTarget("bb_caseless")

proc caselessScoped(s: string) =
  # `(?i)` inside a group ends with the group.
  if s == "AB" and s.match(re"(?:(?i)a)b"):
    symexTarget("bb_caseless_scoped")

proc property(s: string) =
  if s == "\xC9" and not s.match(re"\p{Lu}"):
    symexTarget("bb_property")

proc propertyNeg(s: string) =
  if s == "a" and s.match(re"\P{L}"):
    symexTarget("bb_property_neg")

proc ucpWord(s: string) =
  if s == "\xE9" and not s.match(re"(*UCP)\w"):
    symexTarget("bb_ucp_word")

proc failVerb(s: string) =
  if s.match(re"a(*F)|b") and s[0] == 'a':
    symexTarget("bb_fail_verb")

proc markVerb(s: string) =
  if s == "a" and not s.match(re"(*MARK:m)a"):
    symexTarget("bb_mark_verb")

proc crDollar(s: string) =
  # `(*CR)`: `$` holds before a final CR, not before a final LF.
  if s == "a\r" and not s.match(re"(*CR)a$"):
    symexTarget("bb_cr_dollar")

proc crDollarLf(s: string) =
  if s == "a\n" and s.match(re"(*CR)a$"):
    symexTarget("bb_cr_dollar_lf")

proc crlfDot(s: string) =
  # `(*CRLF)`: `.` fails at a CR only when an LF follows it.
  if s == "\r\r\n" and (s.matchLen(re"(*CRLF).") != 1 or
                          s.match(re"(*CRLF)..")):
    symexTarget("bb_crlf_dot")

proc crlfSkip(s: string) =
  # The bumpalong skips the LF of a CRLF pair after a failed attempt at the
  # CR (no explicit CR or LF in the pattern) -- unless PCRE's start-of-match
  # optimisation passed over the CR. A match can start at an LF here, so
  # the occurrence is the optimiser's call: undecided (std/re finds -1).
  if s == "\r\n" and s.find(re"(*CRLF).") != -1:
    symexTarget("bb_crlf_skip")

proc anycrlfFind(s: string) =
  # No match can start at an LF (`.` excludes CR and LF): the skip changes
  # nothing, and the search is decided.
  if s == "\r\na" and s.find(re"(*ANYCRLF).") != 2:
    symexTarget("bb_anycrlf_find")

proc crlfNoSkip(s: string) =
  # An explicit `\n` in the pattern turns the skip off.
  if s == "\r\n" and s.find(re"(*CRLF)(?:\n\x00)?.") != 1:
    symexTarget("bb_crlf_noskip")

proc anycrlfDollar(s: string) =
  # `(*ANYCRLF)`: `$` before a final CRLF and before its final LF.
  if s == "a\r\n" and (s.matchLen(re"(*ANYCRLF)a\r?$") != 2 or
                        not s.match(re"(*ANYCRLF)a$")):
    symexTarget("bb_anycrlf_dollar")

proc anyNewline(s: string) =
  # `(*ANY)`: FF and NEL are newlines (`.` excludes them, `$` precedes them).
  if s.len == 2 and s[0] == 'a' and s.match(re"(*ANY)a$") and
     s[1] != '\n' and s[1] != '\v' and s[1] != '\f' and s[1] != '\r' and
     s[1] != '\x85':
    symexTarget("bb_any_newline")

proc acceptVerb(s: string) =
  # `(*ACCEPT)` ends the match at once, closing the groups it is in.
  var m = ["x", "y"]
  if s == "ab" and (s.matchLen(re"a(*ACCEPT)b") != 1 or
                    not s.match(re"(a(*ACCEPT)b)|(c)", m) or m[0] != "a" or
                    m[1] != "y"):
    symexTarget("bb_accept")

proc acceptPrio(s: string) =
  # The first alternative to reach `(*ACCEPT)` wins.
  if s.len == 2 and s.matchLen(re"a(?:(*ACCEPT)|b)") == 2:
    symexTarget("bb_accept_prio")

suite "S8bb (5): the constructs S8ay left undecided":

  test "a named group is a capturing group":
    check verdict(namedGroup, "bb_named").status == sxUnsat
    let r = verdict(namedGroupSym, "bb_named_sym")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].match(re"(?P<word>[a-c]+)$")

  test "(?i) folds ASCII letters, for the rest of its group":
    check verdict(caseless, "bb_caseless").status == sxUnsat
    check verdict(caselessScoped, "bb_caseless_scoped").status == sxUnsat

  test "\\p{..} is a byte set (a byte is the code point of its value)":
    check verdict(property, "bb_property").status == sxUnsat
    check verdict(propertyNeg, "bb_property_neg").status == sxUnsat

  test "(*UCP) widens \\w":
    check verdict(ucpWord, "bb_ucp_word").status == sxUnsat

  test "(*F) never matches; (*MARK:x) matches the empty string":
    check verdict(failVerb, "bb_fail_verb").status == sxUnsat
    check verdict(markVerb, "bb_mark_verb").status == sxUnsat

  test "the newline conventions (*CR) (*CRLF) (*ANYCRLF) (*ANY)":
    check verdict(crDollar, "bb_cr_dollar").status == sxUnsat
    check verdict(crDollarLf, "bb_cr_dollar_lf").status == sxUnsat
    check verdict(crlfDot, "bb_crlf_dot").status == sxUnsat
    check verdict(crlfSkip, "bb_crlf_skip").status == sxUnknown
    check verdict(anycrlfFind, "bb_anycrlf_find").status == sxUnsat
    check verdict(crlfNoSkip, "bb_crlf_noskip").status == sxUnsat
    check verdict(anycrlfDollar, "bb_anycrlf_dollar").status == sxUnsat
    check verdict(anyNewline, "bb_any_newline").status == sxUnsat

  test "(*ACCEPT) ends the match where it is reached":
    check verdict(acceptVerb, "bb_accept").status == sxUnsat
    check verdict(acceptPrio, "bb_accept_prio").status == sxUnsat

# ---- the captures overloads ----------------------------------------------------

proc capMatch(s: string) =
  var m: array[1, string]
  if s == "ab" and s.match(re"(a)b", m) and m[0] == "a":
    symexTarget("bb_cap_match")

proc capMatchWrong(s: string) =
  var m: array[1, string]
  if s == "ab" and s.match(re"(a)b", m) and m[0] != "a":
    symexTarget("bb_cap_match_wrong")

proc capTilde(s: string) =
  if s == "ab" and s =~ re"(a)b":
    if matches[0] == "a":
      symexTarget("bb_cap_tilde")

proc capTildeWrong(s: string) =
  if s == "ab" and s =~ re"(a)b":
    if matches[0] != "a" or matches[1] != "":
      symexTarget("bb_cap_tilde_wrong")

proc capUnset(s: string) =
  # An unset group below the highest set one is written ""; one above it is
  # not written at all.
  var m = ["x", "y", "z"]
  if s == "b" and s.match(re"(a)|(b)", m):
    if m[0] != "" or m[1] != "b" or m[2] != "z":
      symexTarget("bb_cap_unset")

proc capTooSmall(s: string) =
  # A set group past the array: PCRE reports the ovector too small (0), and
  # nothing is written -- the call still matches.
  var m = ["x"]
  if s == "ab" and s.match(re"(a)(b)", m) and m[0] != "x":
    symexTarget("bb_cap_too_small")

proc capTooSmallUnset(s: string) =
  # The group past the array is unset here: the write happens.
  var m = ["x"]
  if s == "a" and s.match(re"(a)|(b)", m) and m[0] != "a":
    symexTarget("bb_cap_fits")

proc capMiss(s: string) =
  var m = ["x"]
  if s == "c" and not s.match(re"(a)", m) and m[0] != "x":
    symexTarget("bb_cap_miss")

proc capBadStart(s: string) =
  # A bad offset: `match` is true (-24 != -1), nothing is written.
  var m = ["x"]
  if s == "ab" and s.match(re"(a)", m, 5) and m[0] != "x":
    symexTarget("bb_cap_bad_start")

proc capLastIteration(s: string) =
  var m = ["x", "y"]
  if s == "abab" and s.match(re"((a)|b)+", m):
    if m[0] != "b" or m[1] != "a":
      symexTarget("bb_cap_last_iter")

proc capEmptyIteration(s: string) =
  var m = ["x"]
  if s == "aaa" and s.match(re"(a*)+", m) and m[0] != "":
    symexTarget("bb_cap_empty_iter")

proc capPriority(s: string) =
  var m = ["x", "y"]
  if s == "ab" and s.match(re"(a|ab)(c|bcd|)", m):
    if m[0] != "a" or m[1] != "":
      symexTarget("bb_cap_priority")

proc capSym(s: string) =
  var m: array[2, string]
  if s.match(re"([0-9]+)-([a-z]*)", m) and m[1] == "q" and m[0].len == 2:
    symexTarget("bb_cap_sym")

proc capFind(s: string) =
  var m = ["p", "q"]
  if s == "xab" and s.find(re"(a)(b)", m) == 1:
    if m[0] != "a" or m[1] != "b":
      symexTarget("bb_cap_find")

proc capContains(s: string) =
  var m = ["p", "q"]
  if s == "xxab" and s.contains(re"(a)(b)", m):
    if m[0] != "a" or m[1] != "b":
      symexTarget("bb_cap_contains")

proc capFindBounds(s: string) =
  var m = ["p", "q"]
  let (first, last) = s.findBounds(re"(a)(b)", m)
  if s == "xab" and (first != 1 or last != 2 or m[0] != "a" or m[1] != "b"):
    symexTarget("bb_cap_find_bounds")

proc capFindBoundsMiss(s: string) =
  var m = ["p", "q"]
  let (first, last) = s.findBounds(re"(a)(b)", m)
  if s == "xyz" and (first != -1 or last != 0 or m[0] != "p"):
    symexTarget("bb_cap_find_bounds_miss")

proc capMatchLen(s: string) =
  var m = ["p"]
  if s == "aab" and s.matchLen(re"(a+)b", m) == 3 and m[0] != "aa":
    symexTarget("bb_cap_match_len")

proc capSeq(s: string) =
  # (`newSeq[string](2)` aborts the compile in `symexFind`: a different
  # mechanism, reported under RFC-0005 S8bb's "As landed".)
  var m = @["p", "q"]
  if s == "ab" and s.match(re"(a)(b)", m):
    if m[0] != "a" or m[1] != "b":
      symexTarget("bb_cap_seq")

proc capSeqShort(s: string; drop: bool) =
  # The seq's length depends on `drop`: the write needs every set group to
  # fit, so a one-element `matches` is left alone.
  var m = @["p", "q"]
  if drop: discard m.pop()
  if s == "ab" and s.match(re"(a)(b)", m):
    if m[0] != (if drop: "p" else: "a"):
      symexTarget("bb_cap_seq_short")

type Holder = object
  ms: array[2, string]

proc capField(s: string) =
  var h = Holder(ms: ["p", "q"])
  if s == "ab" and s.match(re"(a)(b)", h.ms):
    if h.ms[0] != "a" or h.ms[1] != "b":
      symexTarget("bb_cap_field")

proc capStartOffset(s: string) =
  var m = ["p"]
  if s == "zab" and s.match(re"a(b)", m, 1) and m[0] != "b":
    symexTarget("bb_cap_start")

proc capCaretFind(s: string) =
  # `^` holds only at subject position 0, also for the captures.
  var m = ["p"]
  if s == "ab" and s.find(re"(^b|b)", m) == 1 and m[0] != "b":
    symexTarget("bb_cap_caret")

proc capBounds(s: string) =
  # `findBounds`' bounds overload: each group's (first, last) in the
  # subject, (-1, 0) for an unset one.
  var m: array[2, tuple[first, last: int]]
  let (f, l) = s.findBounds(re"(a)|(b)", m)
  if s == "xb":
    if f != 1 or l != 1 or m[0].first != -1 or m[0].last != 0 or
       m[1].first != 1 or m[1].last != 1:
      symexTarget("bb_cap_bounds")

proc capBoundsBadStart(s: string) =
  # With captures, a bad offset is (-1, 0) (the plain overload: (-24, 0)).
  var m = ["p"]
  let (f, l) = s.findBounds(re"(a)", m, 5)
  if s == "a" and (f != -1 or l != 0 or m[0] != "p"):
    symexTarget("bb_cap_bounds_bad")

suite "S8bb (5): the captures overloads write `matches` as std/re does":

  test "match / =~ write the groups":
    check verdict(capMatch, "bb_cap_match").status == sxSat
    check verdict(capMatchWrong, "bb_cap_match_wrong").status == sxUnsat
    check verdict(capTilde, "bb_cap_tilde").status == sxSat
    check verdict(capTildeWrong, "bb_cap_tilde_wrong").status == sxUnsat

  test "unset groups, a too-small array, a miss, a bad offset":
    check verdict(capUnset, "bb_cap_unset").status == sxUnsat
    check verdict(capTooSmall, "bb_cap_too_small").status == sxUnsat
    check verdict(capTooSmallUnset, "bb_cap_fits").status == sxUnsat
    check verdict(capMiss, "bb_cap_miss").status == sxUnsat
    check verdict(capBadStart, "bb_cap_bad_start").status == sxUnsat

  test "PCRE's chosen match: last iteration, empty iteration, priority":
    check verdict(capLastIteration, "bb_cap_last_iter").status == sxUnsat
    check verdict(capEmptyIteration, "bb_cap_empty_iter").status == sxUnsat
    check verdict(capPriority, "bb_cap_priority").status == sxUnsat

  test "a symbolic subject's captures are solved":
    let r = verdict(capSym, "bb_cap_sym")
    check r.status == sxSat
    if r.status == sxSat:
      var m: array[2, string]
      check r.witness[0].match(re"([0-9]+)-([a-z]*)", m)
      check m[1] == "q" and m[0].len == 2

  test "find / contains / findBounds / matchLen write the leftmost match's":
    check verdict(capFind, "bb_cap_find").status == sxUnsat
    check verdict(capContains, "bb_cap_contains").status == sxUnsat
    check verdict(capFindBounds, "bb_cap_find_bounds").status == sxUnsat
    check verdict(capFindBoundsMiss, "bb_cap_find_bounds_miss").status == sxUnsat
    check verdict(capMatchLen, "bb_cap_match_len").status == sxUnsat
    check verdict(capStartOffset, "bb_cap_start").status == sxUnsat
    check verdict(capCaretFind, "bb_cap_caret").status == sxUnsat
    check verdict(capBounds, "bb_cap_bounds").status == sxUnsat
    check verdict(capBoundsBadStart, "bb_cap_bounds_bad").status == sxUnsat

  test "a seq or a field as the matches array":
    check verdict(capSeq, "bb_cap_seq").status == sxUnsat
    check verdict(capSeqShort, "bb_cap_seq_short").status == sxUnsat
    check verdict(capField, "bb_cap_field").status == sxUnsat
