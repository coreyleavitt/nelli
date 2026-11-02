## RFC-0005 S8bt (item 6) probe -- not a suite (run it by hand: `nim c -r
## tests/s8bt_harness/caps_probe.nim A|B|C`). The real costs behind the
## size caps (4000 automaton states, 512 step-table states, 6 registers),
## built with the caps raised (`caps_probe.nim.cfg`): per pattern
## family and size, the automaton / table size, its build time, and a
## representative Z3 query's status, time and `rlimit` (the walker's
## string budget is `seqQueryRLimit` = 20M).
import std/[strutils, times, tables, os]
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
  prm.set("rlimit", 20_000_000'u)
  sol.setParams(prm)
  sol.add len(s) <= mkInt(maxLen)
  sol.add r == mkString(target)
  let t1 = epochTime()
  let res = $sol.check()
  "term " & formatFloat(tl, ffDecimal, 2) & " s, " & res & " " &
    formatFloat(epochTime() - t1, ffDecimal, 2) & " s rlimit " & $rl(sol)

echo "caps: dfa ", maxDfaStates, " step ", maxStepStates, " regs ", maxRegs
# One section per process (`A`, `B`, `C`; all without an argument): A's
# automata past the default caps take gigabytes.
let section = (if paramCount() >= 1: paramStr(1) else: "ABC")

if 'A' in section: echo "== A. automaton states: the attempt's and the search's languages"
if 'A' in section:
 for (k, fam) in [(2, "(*UTF)(?:a|b)*a(?:a|b){@}c"), (3, "(*UTF)(?:a|b)*a(?:a|b){@}c"),
                 (4, "(*UTF)(?:a|b)*a(?:a|b){@}c"), (5, "(*UTF)(?:a|b)*a(?:a|b){@}c"),
                 (3, "(*UTF)(?:a|b)*?a(?:a|b){@}c"), (3, "(*UTF)(?:a|b|c)*a(?:a|b|c){@}$"),
                 (4, "(*UTF)(?:a|b|c)*a(?:a|b|c){@}$")]:
    let p = fam.replace("@", $k)
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
    else: line.add " regex " & $f.re.size & " nodes"
    # Past the default regex cap Z3 measured running past its `rlimit`
    # (k = 4: killed after 2400 s under a 60M limit): not queried.
    if m.ok and f.ok and f.re.size <= 40_000:
      line.add " | find " & entryQuery(p, "find", min(k, 6) + 4, 1)
    echo line
    flushFile(stdout)

if 'B' in section: echo "== B. step-table states: replace"
if 'B' in section:
 for k in [2, 4, 6, 8, 10]:
  for fam in ["(*UTF)(?:a|b)*a(?:a|b){@}", "(*UTF)a(*SKIP)(?:a|b){@}c|.",
              "(*UTF)(?:ab|a){@}c"]:
    let p = fam.replace("@", $k)
    let n = buildNfa(parsePcre(p))
    let t0 = epochTime()
    let t = stepTable(n)
    let tb = epochTime() - t0
    var line = p & " | table " & $t.ok & " " & $t.rows.len & " rows " &
               formatFloat(tb, ffDecimal, 2) & " s"
    if not t.ok: line.add " (" & t.why & ")"
    else:
      line.add " | replace " & replaceQuery(n, t, 4, "x-")
    echo line
    flushFile(stdout)

var regHist = initCountTable[int]()
proc regsOf(t: StepTable): int =
  for r in t.rows:
    for lf in r.other & r.nll & @[r.atEnd]:
      result = max(result, lf.regMap.len)
if 'C' in section: echo "== C. registers: pending positions"
proc ladder(k: int): string =
  ## `a{k}|a{k-1}|..|a`: each shorter match is pending (a
  ## register) while a longer, earlier alternative still runs.
  var alts: seq[string]
  for i in countdown(k, 1): alts.add "a{" & $i & "}"
  "(*UTF)(?:" & alts.join("|") & ")"
if 'C' in section:
 for k in [3, 5, 6, 7, 8, 10]:
  for fam in [ladder(k), "(*CRLF)(?m)(?:a$\\r?){@}b",
              "(*UTF)(?:a(*THEN)b|a){@}c", "(*UTF)(?:a(*SKIP)b|a\\s){@}",
              "(*CRLF)(?m)(?:.$){@}x|."]:
    let p = fam.replace("@", $k)
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
      line.add " | replace " & replaceQuery(n, t, 4, "x-")
    echo line
    flushFile(stdout)
if 'C' in section: echo "regs histogram: ", regHist
