## RFC-0005 S8cf (items 8, 9, 10) -- a call whose Z3 encoding is heavy or past
## its size cap is read at the points the search proposes, with the automaton
## the encoding is verified against (`regex_parser.concreteEntry`): a literal
## subject at walk time, a symbolic one by point lemmas. Native std/re states
## each outcome first.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/runtime

proc units(): int =
  for st in symexQueryStats: result += st.rlimitDelta

const
  # S8bt's measured family: k = 4 is 269k regex nodes, past the 40k cap.
  k4 = "(*UTF)(?:a|b)*a(?:a|b){4}c"
  w4 = "caaaaac"

proc stepHit(s: string) =
  if s.len <= 4 and s.replace(re"(*UTF8)a", "x") == "x-":
    symexTarget("cf_step_hit")

proc stepM(s: string) =
  if s.len <= 4 and s.replace(re"(?m)^a", "x") == "x-":
    symexTarget("cf_step_m")

proc capFind(s: string) =
  if s.find(re"(*UTF)(?:a|b)*a(?:a|b){4}c") == 1:
    symexTarget("cf_cap_find")

proc capFindPinned(s: string) =
  if s == w4 and s.find(re"(*UTF)(?:a|b)*a(?:a|b){4}c") == 1:
    symexTarget("cf_cap_pinned")

proc capRefuted(s: string) =
  if s == w4 and s.find(re"(*UTF)(?:a|b)*a(?:a|b){4}c") == 3:
    symexTarget("cf_cap_refuted")

proc lastLiteral() =
  let s = "abcde"
  if s.findBounds(re"(*UTF)(*ANY).+").last == 4:
    symexTarget("cf_last_literal")

proc lastLiteralRefuted() =
  let s = "abcde"
  if s.findBounds(re"(*UTF)(*ANY).+").last == 3:
    symexTarget("cf_last_literal_no")

proc lastPinned(s: string) =
  if s == "abcde" and s.findBounds(re"(*UTF)(*ANY).+").last == 4:
    symexTarget("cf_last_pinned")

proc lastPinnedRefuted(s: string) =
  if s == "abcde" and s.findBounds(re"(*UTF)(*ANY).+").last != 4:
    symexTarget("cf_last_pinned_no")

proc matchLenLiteral() =
  let s = "\xc3\xa9b"
  if s.matchLen(re"(*UCP)(*UTF)\w+") == 3:
    symexTarget("cf_len_literal")

proc endsPinned(s: string) =
  if s == "\xc3\xa9b" and s.endsWith(re"(*UCP)(*UTF)\w"):
    symexTarget("cf_ends_pinned")

template measured(f: untyped; l: string): untyped =
  symexQueryStats = @[]
  let res = symexFind(f, tLabel(l))
  echo "  ", l, ": ", res.status, " ", units(), " units"
  check units() < 3_000_000
  res.status

suite "S8cf: the point route":
  test "native":
    check "a-".replace(re"(*UTF8)a", "x") == "x-"
    check "a-".replace(re"(?m)^a", "x") == "x-"
    check w4.find(re(k4)) == 1
    check "abcde".findBounds(re"(*UTF)(*ANY).+").last == 4
    check "\xc3\xa9b".matchLen(re"(*UCP)(*UTF)\w+") == 3
    check "\xc3\xa9b".endsWith(re"(*UCP)(*UTF)\w")

  test "item 8: a symbolic receiver through the step table":
    check measured(stepHit, "cf_step_hit") == sxSat
    check measured(stepM, "cf_step_m") == sxSat

  test "item 9: a pattern past the regex cap":
    check measured(capFindPinned, "cf_cap_pinned") == sxSat
    check measured(capRefuted, "cf_cap_refuted") == sxUnsat
    check measured(capFind, "cf_cap_find") == sxSat

  test "item 10: the priority route on a concrete subject":
    check measured(lastLiteral, "cf_last_literal") == sxSat
    check measured(lastLiteralRefuted, "cf_last_literal_no") == sxUnsat
    check measured(lastPinned, "cf_last_pinned") == sxSat
    check measured(lastPinnedRefuted, "cf_last_pinned_no") == sxUnsat
    check measured(matchLenLiteral, "cf_len_literal") == sxSat
    check measured(endsPinned, "cf_ends_pinned") == sxSat
