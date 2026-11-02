## RFC-0005 S8cf (item 11) -- `replace`'s lemma residuals: two-byte containment,
## sure bytes for UTF, verbs and LIMIT, `count` over a replace value. Each fact
## is compared with std/re on every short subject, and each verdict is std/re's
## on every receiver.
import std/[unittest, re, strutils, unicode]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine

const
  factPats = ["a+b", "ab", "a{2}b", "a+?b", "[ab]c", "(?:ab|cd)+", "a+b|c",
    "a(*SKIP)", "b|a(*COMMIT)", "(*PRUNE)a", "a(*THEN)|b", "(*LIMIT_MATCH=9)a",
    "(*LIMIT_RECURSION=9)a", "(*LIMIT_MATCH=9)a+b", "(*UTF)a", "(*UTF)[ab]",
    "(*UTF)a+b", "(*UTF).", "(*UTF)\\x{e9}", "a(*COMMIT)b", "a(*SKIP)b",
    "(*LIMIT_MATCH=2)(?:a|b)*c", "(*CRLF)a", "(*CRLF)a+b"]
  alpha = ["a", "b", "c", "\n", "\r", "\xc3\xa9", "\xc3"]

proc words(k: int): seq[string] =
  result = @[""]
  var fr = @[""]
  for _ in 1 .. k:
    var nx: seq[string]
    for w in fr:
      for c in alpha: nx.add w & c
    result.add nx
    fr = nx

proc twoBounded(s: string) =
  if s.len <= 16 and s.replace(re"a+b", "-").contains("ab"):
    symexTarget("cf_rp_two")

proc twoStays(s: string) =
  if s.len <= 16 and s.replace(re"ab+", "-").contains("ba"):
    symexTarget("cf_rp_two_sat")

proc utfValid(s: string) =
  # A find that does not fail: `s` is valid.
  if s.len <= 8 and s.find(re"(*UTF)") == 0 and
     s.replace(re"(*UTF)a", "-").contains("a"):
    symexTarget("cf_rp_utf")

proc utfInvalid(s: string) =
  if s == "a\xff" and s.replace(re"(*UTF)a", "-").contains("a"):
    symexTarget("cf_rp_utf_inv")

proc skipSure(s: string) =
  if s.len <= 16 and s.replace(re"a(*SKIP)", "-").contains("a"):
    symexTarget("cf_rp_skip")

proc commitSure(s: string) =
  if s.len <= 16 and s.replace(re"b|a(*COMMIT)", "-").contains("a"):
    symexTarget("cf_rp_commit")

proc commitStays(s: string) =
  if s.len <= 16 and s.replace(re"a(*COMMIT)b", "-").contains("a"):
    symexTarget("cf_rp_commit_sat")

proc pruneSure(s: string) =
  if s.len <= 16 and s.replace(re"(*PRUNE)a", "-").contains("a"):
    symexTarget("cf_rp_prune")

proc limitSure(s: string) =
  if s.replace(re"(*LIMIT_MATCH=9)a", "-").contains("a"):
    symexTarget("cf_rp_limit")

proc countNo(s: string) =
  if s.len <= 16 and s.replace(re"a", "-").count('a') > 0:
    symexTarget("cf_rp_count")

proc countBy(s: string) =
  if s.len <= 16 and s.replace(re"a", "-").count('-') == 2:
    symexTarget("cf_rp_count_sat")

suite "S8cf: replace's lemma residuals":
  test "the facts against std/re":
    var calls, surePats, pairPats = 0
    var bad: seq[string]
    let ws = words(3)
    for p in factPats:
      let pr = parsePcre(p)
      check pr.status == psOk
      let n = buildNfa(pr, pcreSearchEngine(), limitRoom = 0)
      check n.ok
      let f = replaceFacts(n, pr.root)
      if f.sure.card > 0: inc surePats
      if f.pairs.len > 0: inc pairPats
      echo "  ", p, ": sure ", f.sure.card, " pairs ", f.pairs.len
      let rx = re(p)
      for s in ws:
        if f.utf and unicode.validateUtf8(s) >= 0: continue
        let r = s.replace(rx, "-")
        inc calls
        for b in f.sure:
          if b != '-' and b in r: bad.add p & " sure " & escape($b) & " in " & escape(r) & " of " & escape(s)
        for (x, y) in f.pairs:
          if ($x & $y) in r: bad.add p & " pair " & escape($x & $y) & " of " & escape(s)
        if bad.len > 30: break
    echo "  calls ", calls, " with sure ", surePats, " with pairs ", pairPats, " differ ", bad.len
    for b in bad: echo "  ", b
    check bad.len == 0
    check surePats >= 8
    check pairPats >= 2

  test "two-byte containment":
    check symexFind(twoBounded, tLabel("cf_rp_two")).status == sxUnsat
    check symexFind(twoStays, tLabel("cf_rp_two_sat")).status == sxSat

  test "verbs and LIMIT":
    check symexFind(skipSure, tLabel("cf_rp_skip")).status == sxUnsat
    check symexFind(commitSure, tLabel("cf_rp_commit")).status == sxUnsat
    check symexFind(commitStays, tLabel("cf_rp_commit_sat")).status == sxSat
    check symexFind(pruneSure, tLabel("cf_rp_prune")).status == sxUnsat
    check symexFind(limitSure, tLabel("cf_rp_limit")).status == sxUnsat

  test "UTF: an invalid subject keeps its bytes":
    check "a\xff".replace(re"(*UTF)a", "-") == "a\xff"
    check symexFind(utfValid, tLabel("cf_rp_utf")).status == sxUnsat
    check symexFind(utfInvalid, tLabel("cf_rp_utf_inv")).status == sxSat

  test "count over a replace value":
    check "xaxax".replace(re"a", "-").count('-') == 2
    check symexFind(countNo, tLabel("cf_rp_count")).status == sxUnsat
    check symexFind(countBy, tLabel("cf_rp_count_sat")).status == sxSat
