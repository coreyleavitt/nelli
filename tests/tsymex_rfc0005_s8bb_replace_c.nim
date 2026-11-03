## RFC-0005 (soundness channels) slice S8bb, item 6 -- `replace(s, re, by)`
## for an alternation, an anchor and a pattern that can match empty.
##
## At ae08bfd each of these declined (sxUnknown, `seZ3StringIncomplete`):
## S8aw / S8ay lowered only a fixed-length sequence of byte sets and one
## byte set under a greedy `+`. Each pin below is a verdict `std/re`
## decides concretely (probed against Nim 2.2.10's `std/re`, PCRE 8.45):
## Nim's loop takes PCRE's chosen match at the leftmost position, and
## after an empty match retries at the same position with
## NOTEMPTY_ATSTART.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8bb_replace`, `tsymex_rfc0005_s8bb_replace_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 90 s).

import std/[unittest, strutils, re, times, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/regex_parser
import z3

# ---- the step table against std/re, exhaustively ------------------------------
#
# `runTable` is the Pike run the walker's recursive functions step; read
# here by a direct interpreter of the same two functions (`runRef`,
# `repRef` -- `regex_parser.replaceRunZ3`'s `run` and `rep`), its
# value is Nim's `replace` on every subject up to 4 bytes (5 under
# `-d:nelliRegexExhaustive`) over a, b, LF, CR.

const widen = (when defined(nelliRegexExhaustive): 1 else: 0)

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

const repPatterns = [
  "x*", "a*", "a+?", "a|ab", "ab|a", "a*?", "a|", "|a", "(?:ab)*?b?",
  "(a|b)*?b", "b??", "a{0,2}", "a{0,2}?", "(a*)*", "(a|)+", "(?:$|a)+",
  "$", "^", "^a", "a$", "^|a", "\\z", "\\Z", "\\A", "a\\z", "\\Aa|b",
  "a(*ACCEPT)b|b", "(?:a(*ACCEPT))*b", "(?i)A|", "(?<n>a)|b",
  "(*CR)$", "(*CR).", "(*CRLF)a$", "(*CRLF)$", "(*CRLF).", "(*CRLF)\\r",
  "(*CRLF)\\r\\n|", "(*ANYCRLF)$", "(*ANYCRLF).", "(*ANY)a$", "(*ANY)$",
  "(*LF)\\n|", "(?:a|\\n)+?", "\\n$", "\\r?$"]

proc ctxOf(nl: NlConv; u: string): int =
  if u.len == 0: rcEnd
  elif (u.len == 1 and u[0] in nlBytes(nl)) or
       (nlPair(nl) and u == "\r\n"): rcNll
  else: rcOther

proc runRef(t: RunTable; nl: NlConv; u: string; st0: int): int =
  result = -1
  var st = st0
  for j in 0 .. u.len:
    let c = ctxOf(nl, u[j .. ^1])
    let lf = j < u.len and u[j] == '\n'
    if t.matched[st][c][ord(lf)]: result = j
    if c == rcEnd: break
    st = t.next[st][c][ord(u[j])]
    if st < 0: break

proc repRef(t: RunTable; nl: NlConv; s, by: string): string =
  if s.len == 0: return s
  var p = 0
  var ne = false
  var st0 = true
  while true:
    let u = s[p .. ^1]
    let e = runRef(t, nl, u, t.start[ord(st0)][ord(ne)])
    if e >= 0:
      result.add by
      if e == u.len: break
      if e == 0:
        ne = true
        continue
      p += e
    else:
      if u.len == 0: break
      result.add u[0]
      inc p
    ne = false
    st0 = false

suite "S8bb (6): the step table is Nim's replace":

  test "every subject, every pattern":
    var runs, declined = 0
    var bad: seq[string]
    for p in repPatterns:
      let pr = parsePcre(p)
      check pr.status == psOk
      let n = buildNfa(pr)
      if not legacyRun(n):
        # RFC-0005 S8bj: an observable CRLF start skip is the agenda's
        # step table's (`tsymex_rfc0005_s8bj_replace`).
        inc declined
        check crlfSkipObservable(n)
        continue
      let t = runTable(n)
      check t.ok
      let rx = re(p)
      for subj in words("ab\n\r", 4 + widen):
        inc runs
        let want = subj.replace(rx, "-")
        let got = repRef(t, pr.nl, subj, "-")
        if got != want and bad.len < 10:
          bad.add escape(p) & " " & escape(subj) & " got " & escape(got) &
                  " want " & escape(want)
    echo "  replace runs: ", runs, " (", declined, " patterns declined)"
    checkpoint $bad
    check bad.len == 0
    check runs > 10_000

suite "S8bb (6): the Z3 term is Nim's replace":

  test "every subject up to 3 bytes, every pattern: the only value":
    var checked, declined = 0
    var bad: seq[string]
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    for p in repPatterns:
      let pr = parsePcre(p)
      let n = buildNfa(pr)
      if not legacyRun(n):
        inc declined
        continue
      let t = runTable(n)
      let t0 = epochTime()
      let rx = re(p)
      let ctx = newContext()
      setCurrentContext(ctx)
      let sv = mkStringVar("s")
      let r = replaceRunZ3(sv, mkString("-"), t, pr.nl, fresh)
      for subj in words("ab\n\r", 3 + widen):
        inc checked
        # A solver per subject: an incremental one (push / pop) does not
        # substitute the subject and took minutes for the same queries.
        let sol = newSolver(ctx)
        let prm = newParams(ctx)
        prm.set("timeout", 10000)
        sol.setParams(prm)
        sol.add sv == mkString(subj)
        sol.add r != mkString(subj.replace(rx, "-"))
        let res = $sol.check()
        if res != "zsUnsat" and bad.len < 10:
          bad.add escape(p) & " " & escape(subj) & " " & res
      if epochTime() - t0 > 1.0:
        echo "    ", escape(p), " ", formatFloat(epochTime() - t0, ffDecimal, 1)
    echo "  replace Z3 values: ", checked, " cases (", declined,
         " patterns declined)"
    checkpoint $bad
    check bad.len == 0
    check checked > 3_000

suite "S8bb: walker version floor":
  test "symexWalkerVersion >= 201":
    check parseInt(symexWalkerVersion) >= 201
