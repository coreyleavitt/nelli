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
import std/[unittest, strutils, re, times, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/regex_parser
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

const seqBudget = SymexSettings(budget: ResourceBudget(
  seqQueryRLimit: 100_000_000'u))

template verdict(sut: untyped; label: string): SymexResult =
  let t0 = epochTime()
  let r = symexFind(sut, tLabel(label))
  echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t0,
                                                     ffDecimal, 1), " s"
  checkpoint $r.status & " " & show(r.errors) & " witness=" &
             (if r.status in {sxSat, sxRaised}: $r.witness else: "-")
  r

proc emptyEverywhere(s: string) =
  if s == "ab" and s.replace(re"x*", "-") != "-a-b-":
    symexTarget("bb_rep_empty")

proc emptyAfterMatch(s: string) =
  # The empty match at the end of "aa" is a match of its own.
  if s == "aab" and s.replace(re"a*", "-") != "--b-":
    symexTarget("bb_rep_empty_after")

proc alternation(s: string) =
  if s == "ab" and s.replace(re"a|ab", "-") != "-b":
    symexTarget("bb_rep_alt")

proc lazyStar(s: string) =
  # `a*?` takes the empty match first; NOTEMPTY_ATSTART then takes one `a`.
  if s == "baaa" and s.replace(re"a*?", "-") != "-b------":
    symexTarget("bb_rep_lazy")

proc emptyAlternative(s: string) =
  if s == "aaa" and s.replace(re"a|", "-") != "---":
    symexTarget("bb_rep_empty_alt")

proc dollar(s: string) =
  # `$` holds before the final newline and at the end.
  if s == "a\n" and s.replace(re"$", "-") != "a-\n-":
    symexTarget("bb_rep_dollar")

proc caret(s: string) =
  if s == "aa" and s.replace(re"^a", "-") != "-a":
    symexTarget("bb_rep_caret")

proc caretOrA(s: string) =
  # NOTEMPTY_ATSTART refuses `^` at 0 on the retry; `a` matches at 1.
  if s == "ba" and s.replace(re"^|a", "-") != "-b-":
    symexTarget("bb_rep_caret_or")

proc crlfDollar(s: string) =
  if s == "xa\r\n" and s.replace(re"(*CRLF)a$", "-") != "x-\r\n":
    symexTarget("bb_rep_crlf_dollar")

proc acceptAlt(s: string) =
  if s == "ab" and s.replace(re"a(*ACCEPT)b|b", "-") != "--":
    symexTarget("bb_rep_accept")

proc symbolicAlt(s: string) =
  # PCRE takes `a` before `ab`: "ab" gives "xb" (the longest match would
  # give "x"), so this is reached, by "ab" alone (replay-confirmed).
  # (`s.len == 2 and ... == "x"`, unsat, is undecided under the walker's
  # budget: `beSolverUndef`, RFC-0005 S8bb's measurements.)
  if s.len == 2 and s[0] == 'a' and s.replace(re"a|ab", "x") == "xb":
    symexTarget("bb_rep_sym_alt")

proc symbolicEmpty(s: string) =
  # `x*` on one byte: "x" gives "-", any other byte c gives "-c-"; never
  # "--".
  if s.len == 1 and s.replace(re"x*", "-") == "--":
    symexTarget("bb_rep_sym_empty")

proc symbolicEmptyHit(s: string) =
  # `$` matches empty at the end only: "q-" comes from "q" alone
  # (replay-confirmed).
  if s.len == 1 and s.replace(re"$", "-") == "q-":
    symexTarget("bb_rep_sym_empty_hit")

suite "S8bb (6): replace takes PCRE's chosen match, Nim's empty-match retry":

  test "a pattern that can match empty":
    check verdict(emptyEverywhere, "bb_rep_empty").status == sxUnsat
    check verdict(emptyAfterMatch, "bb_rep_empty_after").status == sxUnsat
    check verdict(lazyStar, "bb_rep_lazy").status == sxUnsat
    check verdict(emptyAlternative, "bb_rep_empty_alt").status == sxUnsat

  test "an alternation takes its first alternative that matches":
    check verdict(alternation, "bb_rep_alt").status == sxUnsat
    check verdict(acceptAlt, "bb_rep_accept").status == sxUnsat

  test "anchors, under the newline convention":
    check verdict(dollar, "bb_rep_dollar").status == sxUnsat
    check verdict(caret, "bb_rep_caret").status == sxUnsat
    check verdict(caretOrA, "bb_rep_caret_or").status == sxUnsat
    check verdict(crlfDollar, "bb_rep_crlf_dollar").status == sxUnsat

  test "a symbolic receiver":
    let alt = verdict(symbolicAlt, "bb_rep_sym_alt")
    check alt.status == sxSat
    if alt.status == sxSat:
      check alt.witness[0] == "ab"
    check verdict(symbolicEmpty, "bb_rep_sym_empty").status == sxUnsat
    # RFC-0005 batch 7: since S8bp solves this label query in a context
    # of its own, its cost is the query text's alone. Z3 5.1 decides it
    # in 198,718 units; Z3 4.13.4 needs 18,801,883 (12,755,004 in the
    # walk's context at batch 6), and step 1 has half of
    # `seqQueryRLimit`'s 20M, so on 4.13.4 the default walk declines.
    # Under the defaults the pin is sxSat or that decline, never sxUnsat;
    # under an explicit 100M sequence budget it is Nim's witness on both
    # Z3s.
    let hit = verdict(symbolicEmptyHit, "bb_rep_sym_empty_hit")
    check hit.status in {sxSat, sxUnknown}
    if hit.status == sxSat:
      check hit.witness[0] == "q"
    else:
      check hit.errors.anyIt(it.kind == beSolverUndef)
    let wide = symexFind(symbolicEmptyHit, tLabel("bb_rep_sym_empty_hit"),
                         seqBudget)
    check wide.status == sxSat
    if wide.status == sxSat:
      check wide.witness[0] == "q"
      check "q".replace(re"$", "-") == "q-"

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
