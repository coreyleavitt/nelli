## RFC-0005 S8bt (item 2) -- `replace(s, re, by)` on PCRE 8.37's JIT:
##   * the agenda's step table (`pcre_select.stepTable` of
##     `buildNfa(.., peJit837)`), read by a direct interpreter inside the
##     JIT's search loop (its prefix scan, a SKIP landing without the CRLF
##     start skip, the bumpalong by a UTF-8 lead byte's length), is the
##     concrete JIT reference's `replace` (`pcreReplace`, pinned against
##     the JIT itself by `tsymex_rfc0005_s8bt_jit`);
##   * the Z3 term (`regex_parser.replaceStepZ3`) has that value as its
##     only value;
##   * the patterns the walker reads without the agenda (S8bb's run, the
##     S8aw / S8ay shapes: no verb but MARK, no observable CRLF start skip,
##     no UTF) read the same on both engines.
import std/[unittest, strutils, times, tables, sets]
import z3
import nelli/smt/[pcre_syntax, pcre_select, regex_parser]
import ./s8bt_harness/[jit_corpus, stepref]

const deltaText = staticRead("s8bt_harness/jit837-delta.txt")

proc repPatterns(): seq[string] =
  for p in jitLongCorpus(): result.add p
  for cv in jitConventions:
    for h in ["\\sa", "\\r\\na", "aba", "(?:ab|ba)a", "\\s{2}"]:
      for t in ["", "(*SKIP)", "(*COMMIT)", "(*SKIP:A)b|.",
                "(*MARK:A)(*SKIP:A)"]:
        result.add cv & h & t
  for cv in ["(*UTF)", "(*UTF)(*CRLF)"]:
    for h in ["\\sé", "aéa", "\\x{20ac}a"]:
      for t in ["", "(*SKIP)", "(*COMMIT)"]:
        result.add cv & h & t

proc subjectsFor(p: string; maxLen: int): seq[string] =
  if p.startsWith("(*UTF)"):
    result = @[""]
    var frontier = @[""]
    for _ in 1 .. maxLen - 1:
      var nx: seq[string]
      for w in frontier:
        for c in ["a", "é", "€", "\r", "\n"]: nx.add w & c
      result.add nx
      frontier = nx
  else:
    result = words("ab\r\n", maxLen)

# The patterns are split three ways between this file and its `_b` / `_c`
# twins (which include this one with `s8btReplacePart = 1` / `2`), so each
# runs under 60 s on the Windows legs; the engines' agreement is part 0's.
when not declared(s8btReplacePart):
  const s8btReplacePart = 0

proc inPart(i: int): bool = i mod 3 == s8btReplacePart

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

suite "S8bt: replace on PCRE 8.37's JIT (part " & $s8btReplacePart & ")":

  test "the step table, read in the JIT's loop, is the JIT's replace":
    var runs = 0
    var bad: seq[string]
    for i, p in repPatterns():
      if not inPart(i): continue
      let pr = parsePcre(p)
      check pr.status == psOk
      let n = buildNfa(pr, peJit837)
      check n.ok
      if not n.ok: continue
      let t = stepTable(n)
      checkpoint escape(p) & " " & t.why
      check t.ok
      if not t.ok: continue
      for subj in subjectsFor(p, 4):
        inc runs
        let want = pcreReplace(n, subj, "-")
        let got = replaceRef(n, t, subj, "-")
        if got != want and bad.len < 20:
          bad.add escape(p) & " " & escape(subj) & " got " & escape(got) &
                  " want " & escape(want)
    echo "  step-table replace runs: ", runs, ", ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0
    check runs > 6_000

  test "the Z3 term's only value is the JIT's replace":
    var checked = 0
    var bad: seq[string]
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    for i, p in repPatterns():
      # A sixth of the part's patterns: each Z3 check takes ~10 ms.
      if not inPart(i) or (i div 3) mod 6 != 0: continue
      let pr = parsePcre(p)
      let n = buildNfa(pr, peJit837)
      let t = stepTable(n)
      if not t.ok: continue
      let tp = epochTime()
      let ctx = newContext()
      setCurrentContext(ctx)
      let sv = mkStringVar("s")
      let r = replaceStepZ3(sv, mkString("-"), n, t, fresh)
      for subj in subjectsFor(p, 3):
        inc checked
        let sol = newSolver(ctx)
        let prm = newParams(ctx)
        prm.set("timeout", 10000)
        sol.setParams(prm)
        sol.add sv == mkString(subj)
        sol.add r != mkString(pcreReplace(n, subj, "-"))
        let res = $sol.check()
        if res != "zsUnsat" and bad.len < 20:
          bad.add escape(p) & " " & escape(subj) & " " & res
      if epochTime() - tp > 1.0:
        echo "    ", escape(p), " ", formatFloat(epochTime() - tp, ffDecimal, 1)
    echo "  step-table replace Z3 values: ", checked, " cases, ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0
    check checked > 300

  when s8btReplacePart == 0:
    test "a pattern read without the agenda reads the same on both engines":
      # Every corpus pattern whose JIT results differ needs the agenda.
      var differing = initHashSet[string]()
      var cur = ""
      for line in deltaText.splitLines():
        let f = line.split('\t')
        if f[0] == "P": cur = f[1].unescape()
        elif f[0] in ["C", "R", "K"]: differing.incl cur
      check differing.len >= 240
      var legacyN = 0
      for p in differing:
        let pr = parsePcre(p)
        if pr.status != psOk: continue
        let ni = buildNfa(pr)
        check not legacyRun(ni)
      # And concretely, on the short corpus: the S8bb-run patterns.
      var bad: seq[string]
      for p in jitCorpus() & jitLongCorpus():
        let pr = parsePcre(p)
        let ni = buildNfa(pr)
        if not legacyRun(ni): continue
        inc legacyN
        let nj = buildNfa(pr, peJit837)
        for subj in words("ab\r\n", 4):
          for st in 0 .. subj.len:
            if pcreExec(ni, subj, st, false) != pcreExec(nj, subj, st, false):
              bad.add escape(p) & " " & escape(subj) & " " & $st
      echo "  legacy-run patterns: ", legacyN, ", ", bad.len, " differ"
      checkpoint bad[0 ..< min(bad.len, 20)].join("\n")
      check bad.len == 0
      check legacyN > 50
