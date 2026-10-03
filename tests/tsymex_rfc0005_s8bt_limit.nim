## RFC-0005 S8bt (item 3) -- `match()`'s call accounting: the concrete
## reference (`pcre_select.pcreLimits`: the agenda with each `match()` entry
## pcre_exec.c makes, in its depth-first order) against libpcre itself
## (`s8bt_harness/limit_oracle`: the least `match_limit` /
## `match_limit_recursion` without the error, on the interpreter), for
## unanchored and anchored calls; then a `(*LIMIT_MATCH=)` /
## `(*LIMIT_RECURSION=)` between 0 and the default against std/re.
import std/[unittest, strutils, times, re]
import nelli/smt/[pcre_syntax, pcre_select]
import ./s8bt_harness/[limit_corpus, limit_oracle]

when not declared(s8btLimitPart):
  const s8btLimitPart = 0
const limitParts = 4

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

suite "S8bt: match()'s call accounting (part " & $s8btLimitPart & ")":

  test "the reference's counts are libpcre's":
    var bad: seq[string]
    var pats, calls, unread = 0
    for i, p in limitCorpus():
      if i mod limitParts != s8btLimitPart: continue
      let pr = parsePcre(p)
      if pr.status != psOk:
        inc unread
        continue
      let n = buildNfa(pr)
      check n.ok
      if not n.ok: continue
      inc pats
      let o = initLimitOracle(p)
      for s in limitSubjects():
        for st in 0 .. min(s.len, 1):
          for anch in [false, true]:
            inc calls
            let want = (o.threshold(s, st, false, anch),
                        o.threshold(s, st, true, anch))
            let got = pcreLimits(n, s, st, anch)
            if got != want and bad.len < 40:
              bad.add escape(p) & (if anch: " anchored(" else: " (") &
                      escape(s) & ", " & $st & ") = " & $got & ", pcre: " &
                      $want
    echo "  ", pats, " patterns, ", calls, " calls, ", unread, " unread, ",
         bad.len, " differ, ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0

  test "a limit between 0 and the default, against std/re":
    var bad: seq[string]
    var calls = 0
    for i, p in limitCorpus():
      if i mod (limitParts * 4) != s8btLimitPart: continue
      let pr0 = parsePcre(p)
      if pr0.status != psOk: continue
      for lim in [1, 2, 3, 5, 8, 13]:
        for kind in ["LIMIT_MATCH", "LIMIT_RECURSION"]:
          let q = "(*" & kind & "=" & $lim & ")" & p
          let n = buildNfa(parsePcre(q))
          check n.ok
          if not n.ok: continue
          let rx = re(q)
          for s in limitSubjects():
            for st in 0 .. min(s.len, 1):
              inc calls
              let (rc, a, b) = pcreExec(n, s, st, false)
              let got = (if rc == 1: (a, b - 1) elif rc == -1: (-1, 0)
                         else: (rc, 0))
              let want = (find(s, rx, st), findBounds(s, rx, st).last)
              if got != want and bad.len < 40:
                bad.add escape(q) & " find/last(" & escape(s) & ", " & $st &
                        ") = " & $got & ", re: " & $want
              let (rcA, _, bA) = pcreExec(n, s, st, true)
              let gotLen = (if rcA == 1: bA - st else: rcA)
              if gotLen != matchLen(s, rx, st) and bad.len < 40:
                bad.add escape(q) & " matchLen(" & escape(s) & ", " & $st &
                        ") = " & $gotLen & ", re: " & $matchLen(s, rx, st)
            if replace(s, rx, "-") != pcreReplace(n, s, "-") and bad.len < 40:
              bad.add escape(q) & " replace(" & escape(s) & ")"
    echo "  ", calls, " calls, ", bad.len, " differ, ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0
