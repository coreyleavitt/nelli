## RFC-0005 S8cf (item 3) -- 8.37's JIT's LIMIT_MATCH: `count_match` sites, not
## `match()` calls. On a JIT libpcre each corpus call is checked against native
## std/re; the automaton is pinned anywhere.
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8cf_jitlimit`. Split so that each part compiles and runs in
## under 60 s on the Windows legs (the whole file took 68 s).

import std/[unittest, re, strutils]
import nelli/symex
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/pcre_engine
import ./s8bt_harness/limit_corpus

suite "S8cf: the JIT's LIMIT_MATCH":
  test "native JIT against the automaton":
    if not pcreRunsJit() or pcreVersion() != "8.37 2015-04-28":
      skip()
    else:
      var bad: seq[string]
      var calls, skipped = 0
      for p in limitCorpus():
        let pr0 = parsePcre(p)
        if pr0.status != psOk: continue
        for lim in [1, 2, 3, 5, 8]:
          let q = "(*LIMIT_MATCH=" & $lim & ")" & p
          let n = buildNfa(parsePcre(q), peJit837, limitRoom = 0)
          if not n.ok or limitEffect(n)[0] == leUnknown:
            inc skipped
            if skipped < 6: echo "  skip ", q, " ok=", n.ok, " why=", n.why, " eff=", limitEffect(n)[0]
            continue
          let rx = re(q)
          for s in limitSubjects():
            inc calls
            let got = pcreExec(n, s, 0, false)
            if got[0] == pcreUnmodelled: inc skipped; continue
            let want = find(s, rx)
            let g = if got[0] >= 0: got[1] else: got[0]
            if g != want and bad.len < 40:
              bad.add escape(q) & " on " & escape(s) & ": model " & $g &
                      " native " & $want
      echo "  calls ", calls, " skipped ", skipped, " differ ", bad.len
      for b in bad: echo "  ", b
      check bad.len == 0
