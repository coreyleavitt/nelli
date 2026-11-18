## RFC-0016 S8co (PRC-33 item 9) -- `strutils.count` of a `set[char]` and
## the overlapping `count(s, sub, true)`. Each lowers to a recursive
## definition over the receiver with the facts Z3's unfolding does not reach
## (`runtime_strings`' `iekStrCount`). The reference loops below are
## strutils' own bodies, checked against `strutils.count` on every short word,
## and every pinned value is checked against `strutils.count` natively. A
## pinned receiver must decide its value exactly; against the symbolic
## reference loops the walker must find no receiver where the values differ
## (soundness only: Z3 need not exhaust the search).
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex

const alpha = ["a", "b", "\xe9", "c"]

proc words(k: int): seq[string] =
  result = @[""]
  var fr = @[""]
  for _ in 1 .. k:
    var nx: seq[string]
    for w in fr:
      for c in alpha: nx.add w & c
    result.add nx
    fr = nx

proc refSet(s: string): int =
  ## `count(s, {'a', '\xe9'})`.
  for i in 0 ..< s.len:
    if s[i] == 'a' or s[i] == '\xe9': inc result

proc refOver(s: string): int =
  ## `count(s, "aba", overlapping = true)`.
  var i = 0
  while i + 3 <= s.len:
    if s[i] == 'a' and s[i + 1] == 'b' and s[i + 2] == 'a': inc result
    inc i

proc setAgrees(s: string) =
  if s.len <= 3 and s.count({'a', '\xe9'}) != refSet(s):
    symexTarget("co_cnt_set_ref")

proc setPinned(s: string) =
  if s == "a\xe9bca" and s.count({'a', '\xe9'}) != 3:
    symexTarget("co_cnt_set_pin")

proc setPinnedSat(s: string) =
  if s == "a\xe9bca" and s.count({'a', '\xe9'}) == 3:
    symexTarget("co_cnt_set_pin_sat")

proc setSat(s: string) =
  if s.len <= 6 and s.count({'a' .. 'c'}) == 3 and s.count('a') == 0:
    symexTarget("co_cnt_set_sat")

proc setBound(s: string) =
  if s.count({'a' .. 'c', '\xe9'}) > s.len:
    symexTarget("co_cnt_set_bound")

proc setNone(s: string) =
  if s.count({'x', 'y'}) >= 1 and not s.contains('x') and not s.contains('y'):
    symexTarget("co_cnt_set_none")

proc overAgrees(s: string) =
  if s.len <= 3 and s.count("aba", overlapping = true) != refOver(s):
    symexTarget("co_cnt_over_ref")

proc overPinned(s: string) =
  if s == "aaaa" and (s.count("aa", overlapping = true) != 3 or
                      s.count("aa") != 2):
    symexTarget("co_cnt_over_pin")

proc overPinnedSat(s: string) =
  if s == "aaaa" and s.count("aa", overlapping = true) == 3 and
     s.count("aa") == 2:
    symexTarget("co_cnt_over_pin_sat")

proc overPinnedAba(s: string) =
  if s == "ababa" and (s.count("aba", overlapping = true) != 2 or
                       s.count("aba") != 1 or
                       s.count("a", overlapping = true) != 3):
    symexTarget("co_cnt_over_pin_aba")

proc overSat(s: string) =
  if s.len <= 5 and s.count("aa", overlapping = true) == 4:
    symexTarget("co_cnt_over_sat")

proc overVsNon(s: string) =
  if s.len <= 3 and s.count("aa", overlapping = true) < s.count("aa"):
    symexTarget("co_cnt_over_non")

proc overNone(s: string) =
  if s.count("ab", true) >= 1 and not s.contains("ab"):
    symexTarget("co_cnt_over_none")

suite "S8co item 9: count of a set[char], overlapping count":
  test "the reference loops and pinned values are strutils.count":
    var runs = 0
    for w in words(5):
      inc runs
      check w.count({'a', '\xe9'}) == refSet(w)
      check w.count("aba", overlapping = true) == refOver(w)
    check "a\xe9bca".count({'a', '\xe9'}) == 3
    check "aaaa".count("aa", overlapping = true) == 3
    check "aaaa".count("aa") == 2
    check "ababa".count("aba", overlapping = true) == 2
    check "ababa".count("aba") == 1
    check "ababa".count("a", overlapping = true) == 3
    check "aaaaa".count("aa", overlapping = true) == 4
    check "".count({'a'}) == 0
    check runs > 1000

  test "a set[char] count":
    check parseInt(symexWalkerVersion) >= 387
    check symexFind(setPinned, tLabel("co_cnt_set_pin")).status == sxUnsat
    check symexFind(setPinnedSat, tLabel("co_cnt_set_pin_sat")).status == sxSat
    check symexFind(setAgrees, tLabel("co_cnt_set_ref")).status != sxSat
    check symexFind(setSat, tLabel("co_cnt_set_sat")).status == sxSat
    check symexFind(setBound, tLabel("co_cnt_set_bound")).status == sxUnsat
    check symexFind(setNone, tLabel("co_cnt_set_none")).status == sxUnsat

  test "an overlapping count":
    check symexFind(overPinned, tLabel("co_cnt_over_pin")).status == sxUnsat
    check symexFind(overPinnedSat, tLabel("co_cnt_over_pin_sat")).status == sxSat
    check symexFind(overPinnedAba, tLabel("co_cnt_over_pin_aba")).status == sxUnsat
    check symexFind(overAgrees, tLabel("co_cnt_over_ref")).status != sxSat
    check symexFind(overSat, tLabel("co_cnt_over_sat")).status == sxSat
    check symexFind(overVsNon, tLabel("co_cnt_over_non")).status != sxSat
    check symexFind(overNone, tLabel("co_cnt_over_none")).status == sxUnsat
