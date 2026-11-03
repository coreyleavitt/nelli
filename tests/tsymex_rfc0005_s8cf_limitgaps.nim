## RFC-0005 S8cf (item 4) -- limit accounting the automata do not hold: a
## possessive (*CRLF) dot run and a possessive non-ASCII UTF run. A concrete
## call reads them, each compared with native PCRE's interpreter. A kept
## `ignore_skip_arg` under a limit stays unread (`costStaleWhy`): counted, the
## model and native differ on `abab` at LIMIT_MATCH=5.
import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/regex_parser
import ./s8bt_harness/limit_oracle

const
  gapPatterns = ["(*CRLF).*", "(*CRLF).*$", "(*CRLF)a.*", "(*CRLF)(?:.*)b|.*",
    "(*UTF)\\x{e9}*", "(*UTF)[\\x{e9}\\x{100}]*", "(*UTF)a\\x{e9}*$",
    "(*UTF)[\\x{e9}a]*", "(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c",
    "a(*SKIP:X)b|(*MARK:X)a|c"]
  gapSubjects = ["", "a", "ab", "aab", "a\r\n", "\r\n", "a\rb", "a\r\nb",
    "\xc3\xa9", "\xc3\xa9\xc3\xa9", "a\xc3\xa9", "\xc4\x80\xc3\xa9b", "abab",
    "ababab", "abq", "ababc", "abc"]

proc crlfSym(s: string) =
  if s == "a\r\nb" and s.replace(re"(*LIMIT_MATCH=5)(*CRLF).*", "y") == "yy\r\ny":
    symexTarget("cf_gap_crlf")

proc crlfSymNo(s: string) =
  if s == "a\r\nb" and s.replace(re"(*LIMIT_MATCH=5)(*CRLF).*", "y") == "nope":
    symexTarget("cf_gap_crlf_no")

proc utfSym(s: string) =
  if s == "\xc3\xa9\xc3\xa9" and s.matchLen(re"(*LIMIT_MATCH=9)(*UTF)\x{e9}*") == 4:
    symexTarget("cf_gap_utf")

suite "S8cf: limit accounting gaps":
  test "anchored and unanchored against native":
    var calls, stops, unread = 0
    var bad: seq[string]
    for p in gapPatterns:
      for lim in [1, 2, 3, 4, 5, 8, 13]:
        let q = "(*LIMIT_MATCH=" & $lim & ")" & p
        let pr = parsePcre(q)
        check pr.status == psOk
        let n = buildNfa(pr, limitRoom = 0, concrete = true)
        if not n.ok:
          echo "  declined ", q, ": ", n.why
          continue
        let o = initLimitOracle(q)
        for s in gapSubjects:
          if pr.utf and utf8Error(s) >= 0: continue
          for anch in [true, false]:
            inc calls
            let got = pcreExec(n, s, 0, anch)
            if got[0] == pcreUnmodelled:
              inc unread
              continue
            if got[0] < -1: inc stops
            let want = o.execInterp(s, 0, anch)
            if got != want and bad.len < 30:
              bad.add escape(q) & (if anch: " anch " else: " ") & escape(s) &
                ": model " & $got & " native " & $want
    echo "  calls ", calls, " stops ", stops, " unread ", unread, " differ ", bad.len
    for b in bad: echo "  ", b
    check bad.len == 0
    check stops > 0

  test "the walker reads them":
    check "a\r\nb".replace(re"(*LIMIT_MATCH=5)(*CRLF).*", "y") == "yy\r\ny"
    check symexFind(crlfSym, tLabel("cf_gap_crlf")).status == sxSat
    check symexFind(crlfSymNo, tLabel("cf_gap_crlf_no")).status == sxUnsat
    check symexFind(utfSym, tLabel("cf_gap_utf")).status == sxSat
