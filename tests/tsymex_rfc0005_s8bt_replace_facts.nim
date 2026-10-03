## RFC-0005 S8bt (item 7) -- the facts the walker states of every
## `replace(s, re, by)` value (`pcre_select.replaceFacts`, read by
## `regex_parser.replaceLemmas`), against the real `std/re`.
##
## For every pattern of a corpus and every subject over a small alphabet up
## to length 4, three replaces (`by` = "", "QQQ" -- a byte no subject holds
## -- and "a") give the number of matches `k` and the bytes they removed
## `c`; the facts must hold of them:
##   * `0 <= c <= len(s)`, `k * mn <= c`, `c <= k * mx` (bounded `mx`), at
##     most `2 * len(s) + 1` matches when `mn == 0`, and `len(r) == len(s)
##     - c + k * len(by)` for each `by`;
##   * a `sure` byte is in `r` only when it is in `by`;
##   * no match leaves `r == s`, and with no empty match (`mn >= 1`) a
##     match needs a byte of `first` in `s`.
import std/[unittest, strutils, re]
import nelli/smt/[pcre_syntax, pcre_select]

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

const corpus = [
  "a", "[0-9]", "[0-9]|x", "(?:ab|a)+", "ab|cd", "a(*COMMIT)b|a", "a*?",
  "a*", "x*", "a|", "$", "^a", "^|a", "ab", "a+b?", "(a)|b",
  "a(*ACCEPT)b|b", "(?i)a", "\\s", "\\s+", "\\S", ".", "(*CRLF).",
  "(*CRLF)\\s", "(*ANY)\\v", "(*ANYCRLF)[\\r\\n]|b", "(?m)^a", "(?m)a$",
  "a$", "a\\z", "[ab]{2}", "a{2,3}", "(?:a|b)*", "(?:a|bc)", "(*UTF)a",
  "(*UTF).", "\\n", "\\r\\n|x", "(*CRLF)\\r?\\n", "(*CRLF)\\n|a",
  "a(*SKIP)b|.", "a(*PRUNE)b|a", "(?:a(*THEN)x|a)", "(*LIMIT_MATCH=0)a",
  "(*CR)a|\\r", "(*CR).", "(*CRLF)$", "(*NO_START_OPT)a|b", "b*a",
  "(?:a|)b?", "\\xe9+", "[^a]", "[^\\n]+", "a(*MARK:x)|b", "(a|ab)(c|bcd)",
  "(?s).", "\\x00|a", "a{0}", "(?:)", "a?b", "\\bx"]

const alpha = "ab0x\n\r\xe9"

suite "S8bt (7): replace facts against std/re":

  test "lengths, match counts and sure bytes":
    let subjects = words(alpha, 4)
    var checked, bad = 0
    var msgs: seq[string]
    for p in corpus:
      let pr = parsePcre(p)
      if pr.status != psOk: continue
      let n = buildNfa(pr)
      if not n.ok: continue
      let f = replaceFacts(n, pr.root)
      let rx = re(p)
      for s in subjects:
        inc checked
        let r0 = replace(s, rx, "")
        let r3 = replace(s, rx, "QQQ")
        let ra = replace(s, rx, "a")
        let c = s.len - r0.len
        let k3 = r3.len - s.len + c
        var why = ""
        if k3 mod 3 != 0: why = "k not integral"
        let k = k3 div 3
        if c < 0 or c > s.len: why = "c out of range"
        elif k < 0: why = "k < 0"
        elif c < k * f.mn: why = "c < k*mn"
        elif f.mx >= 0 and c > k * f.mx: why = "c > k*mx"
        elif f.mn == 0 and k > 2 * s.len + 1: why = "k > 2*len+1"
        elif ra.len != s.len - c + k: why = "len(r) for by = \"a\""
        if k == 0 and (r0 != s or r3 != s or ra != s): why = "k == 0, r != s"
        if f.mn >= 1 and k >= 1:
          var hit = false
          for ch in s:
            if ch in f.first: hit = true
          if not hit: why = "a match, no first byte in s"
        for b in f.sure:
          if b in r0 or (b in r3 and b != 'Q') or (b in ra and b != 'a'):
            why = "sure byte " & escape($b) & " left"
        if why.len > 0:
          inc bad
          if msgs.len < 20:
            msgs.add escape(p) & " on " & escape(s) & ": " & why &
                     " (mn=" & $f.mn & " mx=" & $f.mx & ")"
    echo "  ", checked, " replaces checked, ", bad, " differ"
    checkpoint msgs.join("\n")
    check bad == 0
    check checked > 50_000

  test "the sure bytes where a match always starts":
    proc sureOf(p: string): set[char] =
      let pr = parsePcre(p)
      replaceFacts(buildNfa(pr), pr.root).sure
    check {'0'..'9', 'x'} <= sureOf("[0-9]|x")
    check 'a' in sureOf("(?:ab|a)+")
    check 'a' in sureOf("a*?")
    check {'a'..'z'} <= sureOf("[a-z]")
    check '\xe9' in sureOf("\\xe9+")
    check '\n' in sureOf("\\s")
    # None where a match needs what follows, an anchor, a verb or UTF.
    check sureOf("ab") == {}
    check sureOf("^a") == {}
    check sureOf("a$") == {}
    check sureOf("a(*COMMIT)b|a") == {}
    check sureOf("(*UTF)a") == {}
    # The CRLF skip can pass over an LF.
    check '\n' notin sureOf("(*CRLF)\\s")

  test "the first bytes":
    proc firstOf(p: string): set[char] =
      let pr = parsePcre(p)
      replaceFacts(buildNfa(pr), pr.root).first
    check firstOf("a") == {'a'}
    check firstOf("ab|cd") == {'a', 'c'}
    check firstOf("^a") == {'a'}
    check firstOf("(?i)a") == {'a', 'A'}
    check firstOf("[0-9]|x") == {'0'..'9', 'x'}
    check firstOf("a(*COMMIT)b|c") == {'a', 'c'}
    # Not computed in UTF mode.
    check firstOf("(*UTF)a").card == 256

  test "the match lengths":
    proc lens(p: string): (int, int) =
      let pr = parsePcre(p)
      let f = replaceFacts(buildNfa(pr), pr.root)
      (f.mn, f.mx)
    check lens("ab|cd") == (2, 2)
    check lens("a+") == (1, -1)
    check lens("a*?") == (0, -1)
    check lens("a(*ACCEPT)bc") == (0, 3)
