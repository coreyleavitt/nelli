## RFC-0005 S8bt (item 6) probe -- not a suite. The real costs behind the
## size caps (4000 automaton states, 512 step-table states, 6 registers),
## built with the caps raised (`tprobe_s8bt_caps.nim.cfg`): per pattern
## family and size, the automaton / table size, its build time, and a
## representative Z3 query's status, time and `rlimit` (the walker's
## string budget is `seqQueryRLimit` = 20M).
import std/[strutils, times, tables]
import z3
import nelli/smt/[pcre_syntax, pcre_select, regex_parser]

proc rl(sol: Z3Solver): int =
  let st = sol.getStatistics()
  if st.contains("rlimit count"):
    (if st.isInt("rlimit count"): st.getInt("rlimit count")
     else: int(st.getFloat("rlimit count")))
  else: 0

var ctr = 0
proc fresh(tag: string): string =
  inc ctr
  tag & "#" & $ctr

proc entryQuery(p, entry: string; maxLen, want: int): string =
  ## `entry(s, re"p")` == `want` for a free `s` of length at most `maxLen`.
  let ctx = newContext()
  setCurrentContext(ctx)
  let s = mkStringVar("s")
  let sp = RegexSpec(entry: entry, flag: "re", pattern: p)
  let t0 = epochTime()
  let r = lowerRegexEntry(sp, parseSpec(sp), s, mkInt(0), fresh)
  let tl = epochTime() - t0
  if r.outcome != roValue:
    return "lower " & $r.outcome & " " & r.msg[0 ..< min(80, r.msg.len)] &
           " (" & formatFloat(tl, ffDecimal, 2) & " s)"
  let sol = newSolver(ctx)
  let prm = newParams(ctx)
  prm.set("rlimit", 60_000_000'u)
  sol.setParams(prm)
  for d in r.defs: sol.add d
  sol.add len(s) <= mkInt(maxLen)
  sol.add r.i == mkInt(want)
  let t1 = epochTime()
  let res = $sol.check()
  "lower " & formatFloat(tl, ffDecimal, 2) & " s, " & res & " " &
    formatFloat(epochTime() - t1, ffDecimal, 2) & " s rlimit " & $rl(sol)

proc replaceQuery(n: Nfa; t: StepTable; maxLen: int; target: string): string =
  let ctx = newContext()
  setCurrentContext(ctx)
  let s = mkStringVar("s")
  let t0 = epochTime()
  let r = replaceStepZ3(s, mkString("-"), n, t, fresh)
  let tl = epochTime() - t0
  let sol = newSolver(ctx)
  let prm = newParams(ctx)
  prm.set("rlimit", 60_000_000'u)
  sol.setParams(prm)
  sol.add len(s) <= mkInt(maxLen)
  sol.add r == mkString(target)
  let t1 = epochTime()
  let res = $sol.check()
  "term " & formatFloat(tl, ffDecimal, 2) & " s, " & res & " " &
    formatFloat(epochTime() - t1, ffDecimal, 2) & " s rlimit " & $rl(sol)

echo "caps: dfa ", maxDfaStates, " step ", maxStepStates, " regs ", maxRegs

echo "== A. automaton states: the attempt's and the search's languages"
proc words(k: int): string =
  ## `k` alternatives of distinct 4-byte words (a trie of ~3k states).
  var alts: seq[string]
  for i in 0 ..< k:
    var w = ""
    var x = i * 7919 + 13
    for _ in 0 ..< 4:
      w.add char(ord('a') + x mod 26)
      x = x div 26 + i
    alts.add w
  "(?:" & alts.join("|") & ")"
for (k, fam) in [(2, "(*UTF)(?:a|b)*a(?:a|b){K}c"), (3, "(*UTF)(?:a|b)*a(?:a|b){K}c"),
                 (4, "(*UTF)(?:a|b)*a(?:a|b){K}c"), (5, "(*UTF)(?:a|b)*a(?:a|b){K}c"),
                 (3, "(*UTF)(?:a|b)*?a(?:a|b){K}c"), (3, "(*UTF)(?:a|b|c)*a(?:a|b|c){K}$"),
                 (4, "(*UTF)(?:a|b|c)*a(?:a|b|c){K}$"),
                 (50, "W"), (200, "W"), (500, "W"), (1000, "W"), (2000, "W"),
                 (200, "Wx+"), (1000, "Wx+")]:
    let p = (if fam.startsWith("W"): words(k) & fam[1 .. ^1]
             else: fam.replace("K", $k))
    let n = buildNfa(parsePcre(p))
    var t0 = epochTime()
    let m = selectionLangV(n, "probe:" & p, lkMark, pcOther)
    let tm = epochTime() - t0
    t0 = epochTime()
    let f = searchLangV(n, "probe:" & p, skFirst, pcOther)
    let tf = epochTime() - t0
    var line = p & " | lkMark " & $m.ok & " " & $m.states & "/" &
               $m.minStates & " " & formatFloat(tm, ffDecimal, 2) & " s"
    line.add " | skFirst " & $f.ok & " " & $f.states & "/" & $f.minStates &
             " " & formatFloat(tf, ffDecimal, 2) & " s"
    if not f.ok: line.add " (" & f.why & ")"
    if m.ok and f.ok:
      line.add " | find " & entryQuery(p, "find", min(k, 6) + 4, 1)
    echo line
    flushFile(stdout)

echo "== B. step-table states: replace"
for k in [2, 4, 6, 8, 10]:
  for fam in ["(*UTF)(?:a|b)*a(?:a|b){K}", "(*UTF)a(*SKIP)(?:a|b){K}c|.",
              "(*UTF)(?:ab|a){K}c"]:
    let p = fam.replace("K", $k)
    let n = buildNfa(parsePcre(p))
    let t0 = epochTime()
    let t = stepTable(n)
    let tb = epochTime() - t0
    var line = p & " | table " & $t.ok & " " & $t.rows.len & " rows " &
               formatFloat(tb, ffDecimal, 2) & " s"
    if not t.ok: line.add " (" & t.why & ")"
    else:
      line.add " | replace " & replaceQuery(n, t, 6, "x-")
    echo line
    flushFile(stdout)

echo "== C. registers: pending positions"
var regHist = initCountTable[int]()
proc regsOf(t: StepTable): int =
  for r in t.rows:
    for lf in r.other & r.nll & @[r.atEnd]:
      result = max(result, lf.regMap.len)
for k in [2, 4, 6, 8]:
  for fam in ["(*CRLF)(?m)(?:a$\\r?){K}b",
              "(*UTF)(?:a(*THEN)b|a){K}c", "(*UTF)(?:a(*SKIP)b|a\\s){K}",
              "(*CRLF)(?m)(?:.$){K}x|."]:
    let p = fam.replace("K", $k)
    let n = buildNfa(parsePcre(p))
    if not n.ok:
      echo p, " | nfa ", n.why
      continue
    let t0 = epochTime()
    let t = stepTable(n)
    let tb = epochTime() - t0
    var line = p & " | table " & $t.ok & " " & $t.rows.len & " rows, regs " &
               $regsOf(t) & " " & formatFloat(tb, ffDecimal, 2) & " s"
    if not t.ok: line.add " (" & t.why & ")"
    else:
      regHist.inc regsOf(t)
      line.add " | replace " & replaceQuery(n, t, 6, "x-")
    echo line
    flushFile(stdout)
echo "regs histogram: ", regHist
