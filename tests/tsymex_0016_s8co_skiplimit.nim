## RFC-0016 S8co (PRC-33 item 4) -- a kept `ignore_skip_arg` under a limit.
## An attempt that starts with pcre_exec.c's `ignore_skip_arg` set (kept by a
## SKIP's jump past the start, or by a re-run past a CRLF's LF) skips the
## RMATCH of each SKIP:NAME it covers: one `match()` call fewer, and the
## continuation one frame shallower. Which SKIP:NAMEs it covers is their run
## number, final only when they reach the agenda's front. A concrete call
## under a match or recursion limit reads it, each compared with native
## PCRE's interpreter, and the walker decides a call it used to decline.
import std/[unittest, re, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/regex_parser
import ./s8bt_harness/limit_oracle
from ./s8cu_helpers import pinFind

const
  patterns = [
    "(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c",
    "a(*SKIP:X)b|(*MARK:X)a|c",
    "a(*SKIP:N)c|ab(*SKIP)d|b",
    "(?:a(*SKIP:N)c|ab(*SKIP)d)+|b",
    "a(*SKIP:N)(*SKIP:M)c|ab(*SKIP)d|.",
    "(?:a(*SKIP:N)c|a(*SKIP:N)b(*SKIP)x|b)+",
    "a(?:(*SKIP:N)c|(*SKIP:M)d)|ab(*SKIP)q|b+",
    "(?:x(*SKIP:N)y|xa(*SKIP)b|(*MARK:N)a)+",
    "a+(*SKIP:N)c|ab(*SKIP)q|ab",
    "(a(*SKIP:N)c|ab(*SKIP)q|b)+c?",
    "(*CRLF)(?:\\n(*SKIP:N)x|.)+",
    "(*CRLF)(?:a(*SKIP:N)x|\\n(*SKIP:N)y|\\r(*SKIP)z)|b"]
  subjects = ["", "a", "ab", "abab", "ababab", "abq", "abqab", "abqbx",
    "abqbxab", "abqabq", "abdab", "abdabc", "ac", "abdac", "abqac", "xab",
    "xabxa", "abqaac", "a\r\nb", "\r\n\r\nx", "a\r\nay", "\r\nz\r\nb",
    "abqabqabqc", "abqbxabqbxc", "bbab", "abxaaab", "abxaaac", "abxaab",
    "abdaaac", "abxaaaab", "abdaab"]

proc runCorpus(declined, bad: var seq[string]; calls, stops, kept: var int) =
  for p in patterns:
    for lim in [1, 2, 3, 4, 5, 6, 7, 8, 10, 13, 21]:
      for lk in ["LIMIT_MATCH", "LIMIT_RECURSION"]:
        let q = "(*" & lk & "=" & $lim & ")" & p
        let pr = parsePcre(q)
        if pr.status != psOk:
          declined.add q & ": parse " & $pr.status & " " & pr.reason
          continue
        let n = buildNfa(pr, limitRoom = 0, concrete = true)
        if not n.ok:
          declined.add q & ": " & n.why
          continue
        let o = initLimitOracle(q)
        for s in subjects:
          for anch in [true, false]:
            inc calls
            let got = pcreExec(n, s, 0, anch)
            if got[0] == pcreUnmodelled:
              declined.add q & " " & escape(s) & ": unmodelled"
              continue
            if got[0] < -1: inc stops
            let want = o.execInterp(s, 0, anch)
            if got != want and bad.len < 40:
              bad.add escape(q) & (if anch: " anch " else: " ") & escape(s) &
                ": model " & $got & " native " & $want
  # How many unlimited calls keep an `ignore_skip_arg` into an attempt: the
  # corpus must reach the case.
  for p in patterns:
    let pr = parsePcre(p)
    if pr.status != psOk: continue
    let n = buildNfa(pr, limitRoom = 0, concrete = true)
    if not n.ok: continue
    for s in subjects:
      var x = 0
      var ign = 0'i32
      while x <= s.len:
        let (oc, pos, ig) = runAttempt(n, s, x, 0, anchored = false, ign0 = ign)
        if ign > 0: inc kept
        if oc in {okMatch, okCommit, okStale, okLimitM, okLimitR}: break
        x = (if oc == okSkip and pos > x: pos else: x + 1)
        ign = ig

proc keptSym(s: string) =
  if s == "abab" and
     s.find(re"(*LIMIT_MATCH=5)(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") == -1:
    symexTarget("co_kept")

proc keptSymNo(s: string) =
  if s == "abab" and
     s.find(re"(*LIMIT_MATCH=5)(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c") != -1:
    symexTarget("co_kept_no")

suite "S8co item 4: a kept ignore_skip_arg under a limit":
  test "every call is read, and agrees with native":
    var declined, bad: seq[string]
    var calls, stops, kept = 0
    runCorpus(declined, bad, calls, stops, kept)
    echo "  calls ", calls, " stops ", stops, " kept ", kept, " declined ",
      declined.len, " differ ", bad.len
    for d in declined[0 ..< min(declined.len, 20)]: echo "  declined ", d
    for b in bad: echo "  ", b
    check declined.len == 0
    check bad.len == 0
    check stops > 0
    check kept > 0

  test "the walker reads them":
    check parseInt(symexWalkerVersion) >= 419
    let rx = re"(*LIMIT_MATCH=5)(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c"
    check "abab".find(rx) == -1
    check pinFind(keptSym, tLabel("co_kept")).status == sxSat
    check pinFind(keptSymNo, tLabel("co_kept_no")).status == sxUnsat
