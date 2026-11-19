## RFC-0016 S8co (PRC-33 item 9) -- `replace`'s facts with a `(*SKIP:NAME)`
## some path reaches without its MARK (`Nfa.hasNeverSkip`, the
## interpreter). pcre_exec.c ignores such a SKIP: it re-runs the attempt at
## the same start with the SKIP's count in `ignore_skip_arg`, which an
## attempt can leave for the next one (`attemptIgns`). The facts
## (`pcre_select.replaceFacts`: `first`, `sure`, `pairs`) now range over
## every value an attempt can start with, and over the bumpalong's CRLF
## start state the attempt reads; they declined before. The automaton is
## the walker's for a pattern with no limit (`limitNfa`): one that counts
## `match()`'s calls still declines a count kept across attempts
## (`costStaleWhy`). Each fact is compared with std/re on every short
## subject, and the walker decides calls that declined.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
from ./s8cu_helpers import pinFind

const
  # An attempt that leaves `ignore_skip_arg` for the next one: at `a` the
  # unmarked SKIP:z re-runs it with 1, and the SKIP's jump keeps it, so the
  # attempt at `c` ignores its SKIP:x and matches the last branch; started
  # with 0, SKIP:x moves the search on and no match starts at `c`.
  carry = "a(*SKIP:z)(*FAIL)|ab(*SKIP)(*FAIL)|(*MARK:x)c(*SKIP:x)(*FAIL)|c"
  pats = ["a(*SKIP:x)b|a", "a(*SKIP:x)b|.", "a(*SKIP:x)b|c", "(*MARK:x)a(*SKIP:x)b|a",
    "a(*SKIP:x)(*FAIL)|ab", "(?:a(*SKIP:x)b|c)+", "a+(*SKIP:x)b|a",
    "(?:a(*MARK:x)|b)(*SKIP:x)c|b", "a(*SKIP:x)b(*SKIP:y)c|a", "ab(*SKIP:x)c|b",
    "a(*SKIP:x)(*SKIP:y)b|a", "(*CRLF)\\n(*SKIP:x)a|\\n", "(*CRLF)a(*SKIP:x)\\n|\\r",
    "a(*SKIP:x)b|a(*MARK:x)c", "(?:a(*SKIP:x)b)?c", carry]
  alpha = "abcx\n\r"

proc words(k: int): seq[string] =
  result = @[""]
  var fr = @[""]
  for _ in 1 .. k:
    var nx: seq[string]
    for w in fr:
      for c in alpha: nx.add w & c
    result.add nx
    fr = nx

proc factsOf(p: string): ReplaceFacts =
  let pr = parsePcre(p)
  replaceFacts(buildNfa(pr, pcreSearchEngine()), pr.root)

proc skipSure(s: string) =
  if s.replace(re"a(*SKIP:x)b|a", "-").contains("a"):
    symexTarget("co_skn_sure")

proc skipFirst(s: string) =
  if s.replace(re"a(*SKIP:x)b|c", "") != s and not s.contains('a') and
     not s.contains('c'):
    symexTarget("co_skn_first")

proc skipSat(s: string) =
  if s.len <= 4 and s.replace(re"a(*SKIP:x)b|a", "-") == "-c":
    symexTarget("co_skn_sat")

suite "S8co item 9: replace's facts with an unmarked SKIP:NAME":
  test "the facts against std/re":
    var calls, never, firsts, sures = 0
    var bad: seq[string]
    let ws = words(4)
    for p in pats:
      let pr = parsePcre(p)
      check pr.status == psOk
      let n = buildNfa(pr, pcreSearchEngine())
      check n.ok
      if n.hasNeverSkip: inc never
      let f = replaceFacts(n, pr.root)
      if f.first.card < 256: inc firsts
      if f.sure.card > 0: inc sures
      echo "  ", p, ": never ", n.hasNeverSkip, " first ", f.first.card,
           " sure ", f.sure.card, " pairs ", f.pairs.len
      let rx = re(p)
      for s in ws:
        inc calls
        let r0 = s.replace(rx, "")
        let r = s.replace(rx, "QQQ")
        let r1 = s.replace(rx, "-")
        let c = s.len - r0.len
        let k = (r.len - s.len + c) div 3
        var why = ""
        if k == 0 and r != s: why = "no match, r != s"
        if f.mn >= 1 and k >= 1:
          var hit = false
          for ch in s:
            if ch in f.first: hit = true
          if not hit: why = "a match, no first byte"
        for b in f.sure:
          if b in r0: why = "sure byte " & escape($b) & " left"
        for (x, y) in f.pairs:
          if ($x & $y) in r1: why = "pair " & escape($x & $y) & " left"
        if why.len > 0 and bad.len < 30:
          bad.add p & " on " & escape(s) & ": " & why
    echo "  calls ", calls, " unmarked ", never, " first ", firsts, " sure ",
         sures, " differ ", bad.len
    for b in bad: echo "  ", b
    check bad.len == 0
    if pcreSearchEngine() == peInterp:
      check never >= 10
      check firsts >= 10
      check sures >= 3

  test "the facts":
    let f = factsOf("a(*SKIP:x)b|a")
    check f.first == {'a'}
    check 'a' in f.sure
    check factsOf("a(*SKIP:x)b|c").first == {'a', 'c'}
    # A count carried into the next attempt (`attemptIgns`).
    let pr = parsePcre(carry)
    let n = buildNfa(pr, pcreSearchEngine())
    echo "  carry: igns ", attemptIgns(n), " replace ",
         "abc".replace(re(carry), "-")
    if pcreSearchEngine() == peInterp:
      check attemptIgns(n) == @[0'i8, 1]
      check 'c' in replaceFacts(n, pr.root).first
      check "abc".replace(re(carry), "-") == "ab-"

  test "the walker decides a symbolic call":
    check parseInt(symexWalkerVersion) >= 390
    check pinFind(skipSure, tLabel("co_skn_sure")).status == sxUnsat
    check pinFind(skipFirst, tLabel("co_skn_first")).status == sxUnsat
    check pinFind(skipSat, tLabel("co_skn_sat")).status == sxSat
