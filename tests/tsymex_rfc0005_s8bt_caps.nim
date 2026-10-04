## RFC-0005 S8bt (item 6) -- the size caps' real cost, and the lazy
## encoding past them. Measured (`tests/s8bt_harness/caps_probe`, caps
## raised): on the priority automaton's route a UTF pattern's `find` query
## costs Z3 16.7M `rlimit` at 34 minimized states and 20.3M (past the
## walker's 20M budget) at 50, and from `(?:a|b)*a(?:a|b){5}c` on the
## determinized regex is past its 2M-node cap before the 4000-state cap is
## reached; a recursive function over the automaton's states measured
## worse (60M, undecided). So the caps stay, and a UTF-mode pattern with
## nothing PCRE's priority decides (no verb, no limit, LF newlines,
## anchors at the edges) takes S8ay's edge-split reading instead
## (`regex_parser.lazyUtf`): its languages as Z3 regexes over the UTF-8
## bytes, which Z3's derivatives explore lazily, with pcre_exec's UTF
## errors added. Pinned: the entries' formulas against std/re (UTF
## subjects, invalid ones, starts inside a character), the family's
## queries within the budget, and the walker.
import std/[unittest, strutils, re, times]
import z3
import nelli/symex
import nelli/smt/types
import nelli/smt/[pcre_syntax, regex_parser]

# Split three ways between this file and its `_b` / `_c` twins (which
# include it with `s8btCapsPart` = 1 / 2), so each runs under 60 s on the
# Windows legs: parts 0 and 1 the entries (patterns by parity), part 2 the
# family's queries and the walker.
when not declared(s8btCapsPart):
  const s8btCapsPart = 0

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

proc rl(sol: Z3Solver): int =
  let st = sol.getStatistics()
  if st.contains("rlimit count"):
    (if st.isInt("rlimit count"): st.getInt("rlimit count")
     else: int(st.getFloat("rlimit count")))
  else: 0

proc family(k: int): string = "(*UTF)(?:a|b)*a(?:a|b){" & $k & "}c"

proc words(alpha: seq[string]; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

const lazyPats = [
  "(*UTF)(?:a|b)*a(?:a|b){1}c", "(*UTF)\\p{Greek}+a", "(*UTF)(?i)\\x{e9}+$",
  "(*UTF)^\\x{3a3}|b", "(*UTF)[^a]{2}", "(*UTF)\\x{e9}|ab",
  "(*UTF)(*UCP)\\d\\s", "(*UTF)(?i)k\\z", "(*UTF)\\x{3a3}a*",
  "(*UTF)^\\x{e9}[ab]+$"]

proc lazyEntries(p: string): seq[string] =
  ## The entries `lazyUtf` routes for `p`: those PCRE's priority does not
  ## decide always, the others where `selectionForm` reads the choice.
  result = @["find", "contains", "match", "startsWith", "findBoundsFirstCap"]
  let (fine, edges, _) = splitEdges(parsePcre(p).root)
  doAssert fine
  if selectionForm(edges).kind != skNone:
    result.add ["matchLen", "endsWith", "findBoundsLast"]

suite "S8bt: UTF mode's plain patterns, lazily (item 6)":

  when s8btCapsPart in 0 .. 1:
    test "the entries' formulas against std/re":
      var bad, routed: seq[string]
      var checked = 0
      var ctr = 0
      let tAll = epochTime()
      proc fresh(tag: string): string =
        inc ctr
        tag & "#" & $ctr
      # a, b, c, e-acute, sigma, a lone lead byte (invalid), K (Kelvin).
      let alpha = @["a", "b", "\xC3\xA9", "\xCE\xA3", "\xC3", "\xE2\x84\xAA"]
      # (Two characters, at most four bytes.)
      for pi, p in lazyPats:
        if pi mod 2 != s8btCapsPart: continue
        let rx = re(p)
        let es = lazyEntries(p)
        routed.add escape(p) & " " & $es.len
        for subj in words(alpha, 2):
          if subj.len > 4: continue
          let ctx = newContext()
          setCurrentContext(ctx)
          var cases: seq[(string, int, int)]
          for st in [-1, 0, 1, subj.len]:
            if st > subj.len: continue
            cases.add ("matchLen", st, subj.matchLen(rx, st))
            cases.add ("match", st, int(subj.match(rx, st)))
            cases.add ("find", st, subj.find(rx, st))
            cases.add ("contains", st, int(subj.contains(rx, st)))
            cases.add ("findBoundsLast", st, subj.findBounds(rx, st).last)
            var m: array[0, tuple[first, last: int]]
            cases.add ("findBoundsFirstCap", st, subj.findBounds(rx, m, st).first)
          cases.add ("endsWith", 0, int(subj.endsWith(rx)))
          cases.add ("startsWith", 0, int(subj.startsWith(rx)))
          for (name, st, real) in cases:
            if name notin es: continue
            let sp = RegexSpec(entry: name, flag: "re", pattern: p)
            let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj),
                                    mkInt(st), fresh)
            let where = escape(p) & " " & escape(subj) & " " & name & "(" &
                        $st & ") real " & $real
            if r.outcome != roValue:
              bad.add $r.outcome & " " & r.msg & ": " & where
              continue
            inc checked
            let sol = newSolver(ctx)
            let prm = newParams(ctx)
            prm.set("timeout", 10000)
            sol.setParams(prm)
            for d in r.defs: sol.add d
            if name in ["endsWith", "match", "startsWith", "contains"]:
              sol.add(if real == 1: not r.b else: r.b)
            else:
              sol.add r.i != mkInt(real)
            let res = $sol.check()
            if res != "zsUnsat": bad.add res & " " & where
          if bad.len > 20: break
        echo "    ", escape(p), ": ", lap()
      echo "  ", lazyPats.len, " patterns, ", checked, " cases, ", bad.len,
           " differ, ", formatFloat(epochTime() - tAll, ffDecimal, 1), " s"
      echo "  entries routed: ", routed.join(", ")
      checkpoint bad.join("\n")
      check bad.len == 0
      check checked > 1_000

  when s8btCapsPart == 2:
    test "past the caps: the family's queries within the walker's budget":
      var ctr = 0
      proc fresh(tag: string): string =
        inc ctr
        tag & "#" & $ctr
      for k in [3, 5, 6]:
        let p = family(k)
        for (entry, want) in [("find", 1), ("find", -10), ("contains", 1)]:
          let ctx = newContext()
          setCurrentContext(ctx)
          let s = mkStringVar("s")
          let sp = RegexSpec(entry: entry, flag: "re", pattern: p)
          let r = lowerRegexEntry(sp, parseSpec(sp), s, mkInt(0), fresh)
          check r.outcome == roValue
          if r.outcome != roValue:
            echo "  ", p, " ", entry, ": ", r.msg
            continue
          let sol = newSolver(ctx)
          let prm = newParams(ctx)
          prm.set("rlimit", 20_000_000'u)
          sol.setParams(prm)
          for d in r.defs: sol.add d
          sol.add matches(s, star(range("\x00", "\xff")))
          sol.add len(s) <= mkInt(k + 4)
          if entry == "contains": sol.add r.b
          else: sol.add r.i == mkInt(want)
          let res = $sol.check()
          echo "  ", p, " ", entry, " ", want, ": ", res, " rlimit ", rl(sol)
          check res == "zsSat"
          if res == "zsSat":
            var w = ""
            for c in getStringContents(sol.model().eval(s, true)):
              w.add char(c)
            let real = (if entry == "contains": int(w.contains(re(p)))
                        else: w.find(re(p)))
            check real == want

proc famFind(s: string) =
  if s.len <= 9 and s.find(re"(*UTF)(?:a|b)*a(?:a|b){5}c") == 1:
    symexTarget("bt_caps_find")

proc famNever(s: string) =
  # 7 bytes at least: none in 6.
  if s.len <= 6 and s.contains(re"(*UTF)(?:a|b)*a(?:a|b){5}c"):
    symexTarget("bt_caps_never")

proc greekFind(s: string) =
  if s.len <= 6 and s.find(re"(*UTF)\p{Greek}+a") == 2:
    symexTarget("bt_caps_greek")

proc invalidFind(s: string) =
  if s.len <= 3 and s.find(re"(*UTF)(?:a|b)*a(?:a|b){5}c") == -10:
    symexTarget("bt_caps_invalid")

suite "S8bt: UTF mode's plain patterns, through the walker (item 6)":

  template verdict(sut: untyped; label: string; want = sxSat) =
    let t1 = epochTime()
    let r = symexFind(sut, tLabel(label))
    echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t1,
                                                       ffDecimal, 1), " s"
    check r.status == want

  when s8btCapsPart == 2:
    test "past the caps: sxSat with std/re's witness, sxUnsat where none":
      verdict(famFind, "bt_caps_find")
      verdict(famNever, "bt_caps_never", sxUnsat)
      verdict(greekFind, "bt_caps_greek")
      verdict(invalidFind, "bt_caps_invalid")
