## RFC-0005 (soundness channels) slice S8bb, item 5 -- the constructs S8ay
## left undecided (named groups, inline options, `\p{..}`, the `(*...)`
## verbs) and the captures overloads.
##
## At ae08bfd every one of these calls declined (sxUnknown): the pattern
## reader stopped at the construct, and a call with a `matches` array was
## not lowered at all (the write into the array was not modelled). Each pin
## below is a verdict `std/re` decides concretely (the expected values were
## probed against Nim 2.2.10's `std/re`, PCRE 8.45).
##
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8bb_captures_b`, `tsymex_rfc0005_s8bb_captures_c`,
## `tsymex_rfc0005_s8bb_captures_d`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 92 s).

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
  # RFC-0005 S8bj: the interpreter's scan and skip are modelled (sxUnsat);
  # RFC-0005 S8bt: and so are 8.37's JIT's.
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
    check verdict(crlfSkip, "bb_crlf_skip").status == sxUnsat
    check verdict(anycrlfFind, "bb_anycrlf_find").status == sxUnsat
    check verdict(crlfNoSkip, "bb_crlf_noskip").status == sxUnsat
    check verdict(anycrlfDollar, "bb_anycrlf_dollar").status == sxUnsat
    check verdict(anyNewline, "bb_any_newline").status == sxUnsat
