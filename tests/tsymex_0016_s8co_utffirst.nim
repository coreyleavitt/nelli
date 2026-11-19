## RFC-0016 S8co (PRC-33 item 9) -- `replace`'s `first` bytes in UTF mode
## (`pcre_select.replaceFacts`). A match starts at a character boundary of a
## valid subject, so the byte there is read from the UTF-8 validator's
## boundary state and the verifier after it from the state that byte leaves
## (a lead byte's continuation bytes still to come); a byte no valid
## character starts with starts no match. The JIT's prefix scan can stop at
## a continuation byte (inside a multi-byte newline under `(*ANY)`), but no
## attempt there matches: no continuation byte is `first` on either engine.
## An invalid subject is an error and kept whole, so the fact holds of every
## subject. Each `first` is compared with std/re on every short subject,
## valid or not (and each match `replace` makes starts at a `first` byte),
## and the walker decides a call over a receiver of any length.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
from ./s8cu_helpers import pinFind

const
  pats = ["(*UTF)a", "(*UTF)\\x{e9}", "(*UTF)\\x{e9}+b", "(*UTF).", "(*UTF)..",
    "(*UTF)[^a]", "(*UTF)\\x{2028}|b", "(*UTF)\\w", "(*UTF)\\W", "(*UTF)(?i)\\x{e9}",
    "(*UTF)(*ANY)\\s", "(*UTF)(*ANY)\\x{85}", "(*UTF)(*ANY)\\sb", "(*UTF)(*ANY).",
    "(*UTF)(*ANY)(?m)^a", "(*UTF)(*CRLF)\\s", "(*UTF)\\x{85}",
    "(*UTF)a(*SKIP)b|.", "(*UTF)[\\x{e0}-\\x{ff}]",
    "(*UTF)\\x{10000}", "(*UTF)(*ANY)\\x{a9}b"]
  # U+00A9 (`\xc2\xa9`) and U+2029 put `\x{a9}b` after each multi-byte
  # newline (U+0085, U+2028, U+2029) within three letters.
  alpha = ["a", "b", "\xc3\xa9", "\xc2\x85", "\xe2\x80\xa8", "\xe2\x80\xa9", "\n",
           "\r", "\xc3", "\xa9", "\xc2\xa9", "\xf0\x90\x80\x80"]

proc words(k: int): seq[string] =
  result = @[""]
  var fr = @[""]
  for _ in 1 .. k:
    var nx: seq[string]
    for w in fr:
      for c in alpha: nx.add w & c
    result.add nx
    fr = nx

proc firstOf(p: string): set[char] =
  let pr = parsePcre(p)
  replaceFacts(buildNfa(pr, pcreSearchEngine(), limitRoom = 0), pr.root).first

proc utfFirst(s: string) =
  if s.replace(re"(*UTF)\x{e9}+", "-") != s and not s.contains('\xc3'):
    symexTarget("co_utf_first")

proc utfFirstSat(s: string) =
  if s.len <= 4 and s.replace(re"(*UTF)\x{e9}+", "-") != s:
    symexTarget("co_utf_first_sat")

proc utfRange(s: string) =
  # U+00E0 .. U+00FF all start with C3.
  if s.replace(re"(*UTF)[\x{e0}-\x{ff}]", "") != s and
     not s.contains('\xc3'):
    symexTarget("co_utf_range")

suite "S8co item 9: replace's first bytes in UTF mode":
  test "the first bytes against std/re":
    var calls, computed, starts, a9Starts = 0
    var bad: seq[string]
    let ws = words(3)
    for p in pats:
      let pr = parsePcre(p)
      check pr.status == psOk
      if pr.status != psOk: continue
      let n = buildNfa(pr, pcreSearchEngine(), limitRoom = 0)
      if not n.ok:
        echo "  ", p, ": not built, ", n.why
        continue
      let f = replaceFacts(n, pr.root)
      if f.first.card < 256: inc computed
      echo "  ", p, ": first ", f.first.card, " mn ", f.mn
      let rx = re(p)
      for s in ws:
        inc calls
        let r = s.replace(rx, "Q")
        if r == s: continue
        # A match: with no empty one, it starts at a byte of `first`.
        if f.mn >= 1:
          var hit = false
          for ch in s:
            if ch in f.first: hit = true
          if not hit and bad.len < 30:
            bad.add p & " on " & escape(s) & " -> " & escape(r)
          # Each match `replace` makes starts at a byte of `first`: std/re's
          # own loop (no empty match, so no NOTEMPTY_ATSTART), which reads
          # where the JIT's scan lets an attempt start.
          var prev = 0
          while prev < s.len:
            let (a, b) = findBounds(s, rx, prev)
            if a < 0: break
            inc starts
            if p == "(*UTF)(*ANY)\\x{a9}b": inc a9Starts
            if s[a] notin f.first and bad.len < 30:
              bad.add p & " on " & escape(s) & ": a match at " & $a
            prev = b + 1
    echo "  calls ", calls, " computed ", computed, " starts ", starts,
         " differ ", bad.len
    for b in bad: echo "  ", b
    check bad.len == 0
    check computed >= 18
    # `\x{a9}b` matches, after each multi-byte newline among others.
    check a9Starts >= 20
    check starts >= 10000

  test "the first bytes":
    check firstOf("(*UTF)a") == {'a'}
    check firstOf("(*UTF)\\x{e9}") == {'\xc3'}
    check firstOf("(*UTF)\\x{e9}|\\x{2028}") == {'\xc3', '\xe2'}
    check firstOf("(*UTF)\\x{10000}") == {'\xf0'}
    # No continuation byte, nor a byte no character starts with.
    let dot = firstOf("(*UTF).")
    check dot * {'\x80' .. '\xbf', '\xc0', '\xc1', '\xf5' .. '\xff'} == {}
    check {'a', '\xc3', '\xe2', '\xf0'} <= dot
    # Under `(*ANY)`, where the JIT's scan can stop inside a multi-byte
    # newline (after U+2029's E2 80, at its A9), no continuation byte: the
    # attempt there compares OP_CHAR's bytes C2 A9 and fails.
    let pr = parsePcre("(*UTF)(*ANY)\\x{a9}b")
    let n = buildNfa(pr, pcreSearchEngine(), limitRoom = 0)
    check n.ok
    let anyPre = replaceFacts(n, pr.root).first
    echo "  engine ", n.engine, " jit scan observable ", jitScanObservable(n)
    check jitScanObservable(n) == (n.engine == peJit837)
    check anyPre == {'\xc2'}

  test "the walker decides a symbolic call":
    check parseInt(symexWalkerVersion) >= 388
    check pinFind(utfFirst, tLabel("co_utf_first")).status == sxUnsat
    check pinFind(utfFirstSat, tLabel("co_utf_first_sat")).status == sxSat
    check pinFind(utfRange, tLabel("co_utf_range")).status == sxUnsat
