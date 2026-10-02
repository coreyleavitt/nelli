## RFC-0005 (soundness channels) slice S8bb -- S8ay's remainder.
##
## Item 1: an expression's raise sites drain in evaluation order. At
## ae08bfd `drainScalarRaiseForks` drained its sinks in a fixed order (the
## closure raises, the float -> int domain, parseInt, div/mod by zero,
## overflow, the arithmetic traps, string index, seq del, range, and the
## regex raise LAST), whatever order the expression evaluated them in. So
## a raise written AFTER another in the same expression was forked without
## the earlier one's survivor fact: in `int(s.match(re"a**")) +
## parseInt(t)` Nim always raises `RegexError` and never runs `parseInt`,
## but the walker forked a `ValueError` for an unparsable `t`; in
## `10 div b + parseInt(t)` with `b == 0` Nim raises `DivByZeroDefect`,
## but the walker's `ValueError` fork did not exclude `b == 0`. And an `if`
## guard whose every continuation raised (a rejected pattern, S8ay's
## no-survivor drain) was walked on anyway, on its placeholder value: `int(b)`
## of a bool hoists exactly such a guard.
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
  checkpoint $r.status & " " & show(r.errors) & " witness=" &
             (if r.status in {sxSat, sxRaised}: $r.witness else: "-")
  r

# ---- item 1: drain in evaluation order ----------------------------------------

proc regexThenParse(s, t: string) =
  try:
    discard int(s.match(re"a**")) + parseInt(t)
  except RegexError:
    discard
  except ValueError:
    symexTarget("bb_regex_then_parse")

proc negatedRejected(s: string) =
  # The raise is in an `if` guard: its placeholder value (false) used to be
  # walked on, as the guard's continuation, when the drain left none.
  try:
    if not s.match(re"a**"):
      symexTarget("bb_negated_rejected")
  except RegexError:
    discard

proc shortCircuitRejected(s: string) =
  # `and` never evaluates its right operand when the left is false, so the
  # rejected pattern raises only on a receiver longer than 3.
  try:
    if s.len > 3 and s.match(re"a**"):
      discard
  except RegexError:
    if s.len <= 3:
      symexTarget("bb_short_circuit_rejected")

proc shortCircuitRejectedOr(s: string) =
  try:
    if s.len > 3 or s.contains(re"(ab"):
      discard
  except RegexError:
    if s.len > 3:
      symexTarget("bb_short_circuit_rejected_or")

proc findThenParse(s, t: string) =
  try:
    if s.find(re"(ab") == parseInt(t): discard
  except RegexError:
    discard
  except ValueError:
    symexTarget("bb_find_then_parse")

proc parseThenRegex(s, t: string) =
  # The other order: `parseInt` runs first, so its ValueError is real.
  try:
    discard parseInt(t) + int(s.match(re"a**"))
  except RegexError:
    discard
  except ValueError:
    if t == "x":
      symexTarget("bb_parse_then_regex")

proc divThenParse(t: string; b: int) =
  try:
    if 10 div b == parseInt(t): discard
  except ValueError:
    if b == 0:
      symexTarget("bb_div_then_parse")
  except DivByZeroDefect:
    discard

proc parseThenDiv(t: string; b: int) =
  try:
    if parseInt(t) == 10 div b: discard
  except DivByZeroDefect:
    if t == "x":
      symexTarget("bb_parse_then_div")
  except ValueError:
    discard

proc indexThenParse(s, t: string; i: int) =
  try:
    if s[i] == 'q' and parseInt(t) == 3: discard
  except ValueError:
    if i >= s.len:
      symexTarget("bb_index_then_parse")
  except IndexDefect:
    discard

proc indexPlusParse(s, t: string; i: int) =
  try:
    if ord(s[i]) == parseInt(t): discard
  except ValueError:
    if i >= s.len:
      symexTarget("bb_index_plus_parse")
  except IndexDefect:
    discard

# A `while` guard is not A-normalised (`ParseCtx.inGuardCond`), so its
# whole condition is ONE drain: here the fixed sink order showed. Each of
# these was a wrong `sxSat` at ae08bfd (no replay refutes a clean path).

proc guardRegexThenParse(s, t: string) =
  try:
    while s.find(re"(ab") + parseInt(t) > 0:
      break
  except RegexError: discard
  except ValueError: symexTarget("bb_guard_regex_then_parse")

proc guardIndexThenParse(s, t: string; i: int) =
  try:
    while ord(s[i]) + 10 div parseInt(t) > 0:
      break
  except ValueError:
    if i >= s.len: symexTarget("bb_guard_index_then_parse")
  except IndexDefect: discard
  except DivByZeroDefect: discard
  except OverflowDefect: discard

proc guardIndexThenDiv(s: string; i, b: int) =
  try:
    while ord(s[i]) + 10 div b > 0:
      break
  except DivByZeroDefect:
    if i >= s.len: symexTarget("bb_guard_index_then_div")
  except IndexDefect: discard
  except OverflowDefect: discard

proc indexThenRegex(s: string; i: int) =
  try:
    discard int(s[i]) + int(s.contains(re"(ab"))
  except IndexDefect:
    symexTarget("bb_index_then_regex")
  except RegexError:
    discard

suite "S8bb: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 201

suite "S8bb (1): an expression's raises drain in evaluation order":

  test "a raise after a rejected pattern never runs":
    check verdict(regexThenParse, "bb_regex_then_parse").status == sxUnsat

  test "a guard whose pattern is rejected has no continuation":
    check verdict(negatedRejected, "bb_negated_rejected").status == sxUnsat

  test "a rejected pattern behind a short circuit raises only when reached":
    check verdict(shortCircuitRejected, "bb_short_circuit_rejected").status == sxUnsat
    check verdict(shortCircuitRejectedOr, "bb_short_circuit_rejected_or").status == sxUnsat

  test "a raise after a rejected pattern in a comparison never runs":
    check verdict(findThenParse, "bb_find_then_parse").status == sxUnsat

  test "a raise before a rejected pattern still runs":
    check verdict(parseThenRegex, "bb_parse_then_regex").status == sxSat

  test "a ValueError after a division excludes the division's raise":
    check verdict(divThenParse, "bb_div_then_parse").status == sxUnsat

  test "the other order: a division after a parseInt":
    check verdict(parseThenDiv, "bb_parse_then_div").status == sxUnsat

  test "a ValueError after a string index excludes the index's raise":
    check verdict(indexThenParse, "bb_index_then_parse").status == sxUnsat
    check verdict(indexPlusParse, "bb_index_plus_parse").status == sxUnsat

  test "a while guard drains in evaluation order":
    check verdict(guardRegexThenParse, "bb_guard_regex_then_parse").status == sxUnsat
    check verdict(guardIndexThenParse, "bb_guard_index_then_parse").status == sxUnsat
    check verdict(guardIndexThenDiv, "bb_guard_index_then_div").status == sxUnsat

  test "an index raise before a rejected pattern is reachable":
    check verdict(indexThenRegex, "bb_index_then_regex").status == sxSat

# ---- item 4: findBounds over a compound receiver or start ---------------------
#
# Each half of `findBounds` lowers the receiver and `start`, so S8ay declined
# a compound one (a fresh value, `seZ3StringIncomplete`) rather than lower it
# -- and deposit its raises -- twice. S8bb binds it to a temporary.

proc fbRecvHit(s: string) =
  let b = (s & "ab").findBounds(re"ab")
  if s.len == 1 and b.first == 1 and b.last == 2:
    symexTarget("bb_fb_recv_hit")

proc fbRecvMiss(s: string) =
  let b = (s & "ab").findBounds(re"ab")
  if s.len == 1 and b.first == 0:
    symexTarget("bb_fb_recv_miss")

proc fbStartHit(s: string; k: int) =
  if k >= 0 and k < 4:
    let b = s.findBounds(re"a", k + 1)
    if s == "aa" and k == 0 and b.first == 1 and b.last == 1:
      symexTarget("bb_fb_start_hit")

proc fbStartMiss(s: string; k: int) =
  if k >= 0 and k < 4:
    let b = s.findBounds(re"a", k + 1)
    if s == "aa" and k == 0 and b.first == 0:
      symexTarget("bb_fb_start_miss")

proc fbRecvRaisesOnce(s: string) =
  # The receiver's IndexDefect is forked once, before the call.
  try:
    let b = s[1 .. 2].findBounds(re"b")
    if b.first == 1 and s.len == 3:
      symexTarget("bb_fb_slice_hit")
  except IndexDefect:
    if s.len == 2:
      symexTarget("bb_fb_slice_raise")

proc fbGuard(s: string): int =
  var i = 0
  while i < 3 and (s & "a").findBounds(re"a", i).first == i:
    inc i
  i

proc fbGuardTarget(s: string) =
  let i = fbGuard(s)
  if s.len == 0 and i == 1:
    symexTarget("bb_fb_guard_one")

proc fbGuardTargetMiss(s: string) =
  let i = fbGuard(s)
  if s.len == 0 and i == 3:
    symexTarget("bb_fb_guard_three")

suite "S8bb (4): findBounds binds a compound operand once":

  test "a compound receiver":
    check verdict(fbRecvHit, "bb_fb_recv_hit").status == sxSat
    check verdict(fbRecvMiss, "bb_fb_recv_miss").status == sxUnsat

  test "a compound start":
    check verdict(fbStartHit, "bb_fb_start_hit").status == sxSat
    check verdict(fbStartMiss, "bb_fb_start_miss").status == sxUnsat

  test "a raising receiver forks its raise once":
    check verdict(fbRecvRaisesOnce, "bb_fb_slice_hit").status == sxSat
    check verdict(fbRecvRaisesOnce, "bb_fb_slice_raise").status == sxSat

  test "in a while guard":
    check verdict(fbGuardTarget, "bb_fb_guard_one").status == sxSat
    check verdict(fbGuardTargetMiss, "bb_fb_guard_three").status == sxUnsat

# ---- item 3: PCRE's leftmost-first priority -----------------------------------
#
# `matchLen`, `endsWith` and `findBounds`'s `last` depend on WHICH match
# PCRE returns. S8ay modelled them only where PCRE's choice is the longest
# match and declined the rest (`a|ab`, `a*b`, `(ab)+`: a fresh value,
# `seZ3StringIncomplete`); S8bb runs PCRE's priority order
# (`pcre_select.nim`).

proc mlAltGround(s: string) =
  # PCRE takes `a`, the first alternative, not the longer `ab`.
  if s == "ab" and s.matchLen(re"a|ab") == 2:
    symexTarget("bb_ml_alt_ground")

proc mlAltSym(s: string) =
  if s.len == 2 and s.matchLen(re"a|ab") == 2:
    symexTarget("bb_ml_alt_sym")

proc mlAltSecond(s: string) =
  if s.len == 3 and s.matchLen(re"b|ab") == 2:
    symexTarget("bb_ml_alt_second")

proc mlStarBack(s: string) =
  if s == "aab" and s.matchLen(re"a*b") == 3:
    symexTarget("bb_ml_star_back")

proc mlGroupPlus(s: string) =
  if s.matchLen(re"(ab)+") == 3:
    symexTarget("bb_ml_group_plus")

proc mlNullableLoop(s: string) =
  if s == "aab" and s.matchLen(re"(a|)*b") != 3:
    symexTarget("bb_ml_nullable")

proc mlAnchorMid(s: string) =
  # `a(^|b)`: `^` after a byte never holds, so only `ab` matches.
  if s == "ab" and s.matchLen(re"a(^|b)") != 2:
    symexTarget("bb_ml_anchor_mid")

proc ewAltGround(s: string) =
  if s == "ab" and s.endsWith(re"a|ab"):
    symexTarget("bb_ew_alt_ground")

proc ewAltSym(s: string) =
  if s.len == 2 and s[0] == 'a' and s.endsWith(re"a|ab"):
    symexTarget("bb_ew_alt_sym")

proc fbAltLast(s: string) =
  if s == "xab":
    let (first, last) = s.findBounds(re"a|ab")
    if first == 1 and last == 2:
      symexTarget("bb_fb_alt_last")

proc fbAltHit(s: string) =
  if s == "xab":
    let (first, last) = s.findBounds(re"a|ab")
    if first == 1 and last == 1:
      symexTarget("bb_fb_alt_hit")

suite "S8bb (3): PCRE's match choice, not the longest match":

  test "matchLen takes the first alternative that matches":
    check verdict(mlAltGround, "bb_ml_alt_ground").status == sxUnsat
    check verdict(mlAltSym, "bb_ml_alt_sym").status == sxUnsat
    let r = verdict(mlAltSecond, "bb_ml_alt_second")
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0].matchLen(re"b|ab") == 2

  test "matchLen backtracks a greedy run":
    check verdict(mlStarBack, "bb_ml_star_back").status == sxSat
    check verdict(mlGroupPlus, "bb_ml_group_plus").status == sxUnsat

  test "an empty loop iteration and an anchor away from the edges":
    check verdict(mlNullableLoop, "bb_ml_nullable").status == sxUnsat
    check verdict(mlAnchorMid, "bb_ml_anchor_mid").status == sxUnsat

  test "endsWith reads the match PCRE picks at each position":
    check verdict(ewAltGround, "bb_ew_alt_ground").status == sxUnsat
    let r = verdict(ewAltSym, "bb_ew_alt_sym")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == "aa"

  test "findBounds' last is the chosen match's":
    check verdict(fbAltLast, "bb_fb_alt_last").status == sxUnsat
    check verdict(fbAltHit, "bb_fb_alt_hit").status == sxSat

proc containsAnchorMid(s: string) =
  # `a(^|b)` in "ba": `a` at 1, then `^` fails and there is no `b`.
  if s == "ba" and s.contains(re"a(^|b)"):
    symexTarget("bb_contains_anchor_mid")

proc findAnchorMid(s: string) =
  if s == "xaab" and s.find(re"a(^|b)") != 2:
    symexTarget("bb_find_anchor_mid")

proc findBoundsAnchorMid(s: string) =
  if s.len == 3 and s[0] == 'a':
    let (first, last) = s.findBounds(re"a(^|b)")
    if first == 0 and last == 1:
      symexTarget("bb_fb_anchor_mid")

suite "S8bb (3): an occurrence search with an anchor away from the edges":

  test "contains / find / findBounds follow the search automaton":
    check verdict(containsAnchorMid, "bb_contains_anchor_mid").status == sxUnsat
    check verdict(findAnchorMid, "bb_find_anchor_mid").status == sxUnsat
    let r = verdict(findBoundsAnchorMid, "bb_fb_anchor_mid")
    check r.status == sxSat
    if r.status == sxSat: check r.witness[0][0 .. 1] == "ab"
