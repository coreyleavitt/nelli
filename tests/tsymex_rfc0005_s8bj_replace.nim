## RFC-0005 S8bj -- `replace(s, re, by)` for the patterns S8bb's run does
## not read (a verb, a `(?m)` anchor, UTF mode, an observable CRLF start
## skip), against the real `std/re`:
##   * the agenda's step table (`pcre_select.stepTable`), read by a direct
##     interpreter of its leaves and registers inside pcre_exec.c's loop,
##     is Nim's `replace` on every subject up to 4 bytes over a, b, CR, LF;
##   * the Z3 term (`regex_parser.replaceStepZ3`) has std/re's value as its
##     only value on every subject up to 3 bytes.
## RFC-0005 S8bt: the automaton is the engine's std/re runs `replace`'s
## calls on (`pcre_engine.pcreSearchEngine`), the table read in that
## engine's loop (`s8bt_harness/stepref`).
import std/[unittest, strutils, re, times, tables]
import z3
import nelli/smt/[pcre_syntax, pcre_select, regex_parser, pcre_engine]
import ./s8bt_harness/stepref

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
  "a(*COMMIT)b|.", "(*COMMIT)a|b", "a+(*COMMIT)b|a", "a(*PRUNE)b|.",
  "a(*SKIP)b|.", "aa(*SKIP)b|a+", "a+(*SKIP)b|.|", "(*MARK:A)a(*SKIP:A)b|.",
  "a(*MARK:A)a(*SKIP:A)b|.", "a(*SKIP:B)b|.", "(?:a(*THEN)b|ab)",
  "(?:a(*THEN)b|a)b?", "(?:a(*THEN)|b)+c|a", "x?(*COMMIT)a|", "(*PRUNE)a?",
  "(?m)^", "(?m)$", "(?m)^a|b$", "(*CRLF)(?m)$", "(*CRLF)(?m)^",
  "(*ANYCRLF)(?m)^.?", "(*CR)(?m)$", "(*ANY)(?m)^\\s?",
  "(*CRLF)\\s?", "(*CRLF)a*", "(*ANYCRLF)\\s?$", "(*ANY)\\v?",
  "(*CRLF)[\\x09-\\x0b]\\z", "(*CRLF)\\s(*SKIP)b", "(*NO_START_OPT)a(*COMMIT)b|.",
  "(*CRLF)(*COMMIT)\\s|b", "(*LIMIT_MATCH=0)a"]

suite "S8bj: replace by the agenda's step table, against std/re":

  test "the table, read directly, is Nim's replace":
    var runs = 0
    var bad: seq[string]
    for p in repPatterns:
      let pr = parsePcre(p)
      check pr.status == psOk
      let n = buildNfa(pr, pcreSearchEngine())
      check n.ok
      if limitEffect(n)[0] != leNone: continue   # the walker's own rule
      let t = stepTable(n)
      checkpoint escape(p) & " " & t.why
      check t.ok
      if not t.ok: continue
      let rx = re(p)
      for subj in words("ab\r\n", 4):
        inc runs
        let want = subj.replace(rx, "-")
        let got = replaceRef(n, t, subj, "-")
        if got != want and bad.len < 20:
          bad.add escape(p) & " " & escape(subj) & " got " & escape(got) &
                  " want " & escape(want)
    echo "  step-table replace runs: ", runs
    checkpoint bad.join("\n")
    check bad.len == 0
    check runs > 5_000

  test "the Z3 term's only value is Nim's replace":
    var checked = 0
    var bad: seq[string]
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    for p in repPatterns:
      let pr = parsePcre(p)
      let n = buildNfa(pr, pcreSearchEngine())
      if limitEffect(n)[0] != leNone: continue
      let t = stepTable(n)
      if not t.ok: continue
      let t0 = epochTime()
      let rx = re(p)
      let ctx = newContext()
      setCurrentContext(ctx)
      let sv = mkStringVar("s")
      let r = replaceStepZ3(sv, mkString("-"), n, t, fresh)
      for subj in words("ab\r\n", 3):
        inc checked
        let sol = newSolver(ctx)
        let prm = newParams(ctx)
        prm.set("timeout", 10000)
        sol.setParams(prm)
        sol.add sv == mkString(subj)
        sol.add r != mkString(subj.replace(rx, "-"))
        let res = $sol.check()
        if res != "zsUnsat" and bad.len < 20:
          bad.add escape(p) & " " & escape(subj) & " " & res
      if epochTime() - t0 > 1.0:
        echo "    ", escape(p), " ", formatFloat(epochTime() - t0, ffDecimal, 1)
    echo "  step-table replace Z3 values: ", checked, " cases"
    checkpoint bad.join("\n")
    check bad.len == 0
    check checked > 1_000
