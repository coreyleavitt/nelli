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
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_s8bb_captures`, `tsymex_rfc0005_s8bb_captures_b`,
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
