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
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_s8bb_captures`, `tsymex_rfc0005_s8bb_captures_c`,
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
