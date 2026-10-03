## RFC-0005 S8bt (item 5) -- `(*ANY)` in UTF mode: U+0085 (C2 85), U+2028
## and U+2029 (E2 80 A8 / A9) are newlines for `.`, `$`, `\Z`, `(?m)^`,
## `(?m)$` and the line-start filter, and a lone 0x85 byte (inside another
## character) is none. The concrete reference (`pcreExec`, `pcreReplace`)
## against std/re; the attempt's and the search's languages against the
## reference in every start variant; the step table read directly and
## through Z3 (`replaceStepZ3`); and the entries' Z3 formulas.
import std/[unittest, strutils, re, times]
import z3
import nelli/smt/[pcre_syntax, pcre_select, regex_parser, pcre_engine]
import ./s8bt_harness/[member, stepref]

# Split five ways between this file and its `_b` .. `_e` twins (which
# include it with `s8btAnyPart` = 1 .. 4), so each runs under 60 s on the
# Windows legs: part 0 the concrete reference, parts 1, 2 the languages
# (patterns by parity) and the step table (part 2), part 3 the entries but
# `findBounds`, part 4 `findBounds`.
when not declared(s8btAnyPart):
  const s8btAnyPart = 0

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

const
  anyPats = [
    "(*UTF)(*ANY)a$", "(*UTF)(*ANY).+", "(*UTF)(*ANY)(?m)^a",
    "(*UTF)(*ANY)(?m)a$", "(*UTF)(*ANY)a\\Z", "(*UTF)(*ANY).*b",
    "(*UTF)(*ANY)(?m)$", "(*UTF)(*ANY)(?m)^", "(*UTF)(*ANY)\\N+$",
    "(*UTF)(*ANY)(?m)^.", "(*UTF)(*ANY)(?s).$", "(*UTF)(*ANY)a(*SKIP)$|.",
    "(*ANY)(*UTF)é$", "(*UTF)(*ANY)$", "(*UTF)(*ANY)(?m)a$|b",
    "(*UTF)(*ANY)[^a]$", "(*UTF)(*ANY)(?m)^\\x{85}", "(*UTF)(*ANY).\\z"]
  anyAlpha = ["a", "b", "\u0085", " ", " ", "\n", "\r", "é",
              "ą", " "]

proc anyWords(maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in anyAlpha: next.add w & c
    result.add next
    frontier = next

suite "S8bt: (*ANY) in UTF mode":

  when s8btAnyPart == 0:
    test "concretely, against std/re":
      var bad: seq[string]
      var calls = 0
      for p in anyPats:
        let pr = parsePcre(p)
        check pr.status == psOk
        if pr.status != psOk: continue
        let n = buildNfa(pr, pcreSearchEngine())
        check n.ok
        if not n.ok:
          bad.add escape(p) & ": " & n.why
          continue
        let rx = re(p)
        for s in anyWords(3):
          for st in 0 .. s.len:
            inc calls
            let want = (find(s, rx, st), findBounds(s, rx, st).last)
            let (rc, a, b) = pcreExec(n, s, st, false)
            let got = (if rc == 1: (a, b - 1) elif rc == -1: (-1, 0)
                       else: (rc, 0))
            if got != want and bad.len < 40:
              bad.add escape(p) & " find/last(" & escape(s) & ", " & $st &
                      ") = " & $got & ", std/re: " & $want
            let ml = s.matchLen(rx, st)
            let (rc2, _, b2) = pcreExec(n, s, st, true)
            let gotMl = (if rc2 == 1: b2 - st else: rc2)
            if gotMl != ml and bad.len < 40:
              bad.add escape(p) & " matchLen(" & escape(s) & ", " & $st &
                      ") = " & $gotMl & ", std/re: " & $ml
          if pcreReplace(n, s, "-") != replace(s, rx, "-") and bad.len < 40:
            bad.add escape(p) & " replace(" & escape(s) & ")"
      echo "  ", anyPats.len, " patterns, ", calls, " calls, ", bad.len,
           " differ, ", lap()
      checkpoint bad.join("\n")
      check bad.len == 0

  when s8btAnyPart in 1 .. 2:
    test "the attempt's and the search's languages, every variant":
      var bad: seq[string]
      var runs = 0
      for p in anyPats:
        if anyPats.find(p) mod 2 != s8btAnyPart - 1: continue
        let n = buildNfa(parsePcre(p), pcreSearchEngine())
        if not n.ok: continue
        let na = buildNfa(parsePcre(p))
        let key = "uany:" & p
        for pc in startClasses(n):
          let pre = prefixOf(pc)
          let mark = selectionLangV(na, key & "|a", lkMark, pc)
          let none = selectionLangV(na, key & "|a", lkNone, pc)
          let noOcc = searchLangV(n, key, skNoOcc, pc)
          let first = searchLangV(n, key, skFirst, pc)
          for l in [mark, none, noOcc, first]:
            check l.ok
            if not l.ok: bad.add escape(p) & " " & $pc & ": " & l.why
          if not (mark.ok and none.ok and noOcc.ok and first.ok): continue
          for u in anyWords(2):
            inc runs
            let s = pre & u
            let st = pre.len
            let w = escape(p) & " " & escape(u) & " after " & $pc
            let (k, pos, _) = runAttempt(na, s, st, st, true)
            if member(none.re, toSyms(u)) != (k != okMatch):
              bad.add "lkNone " & w
            let (rc, a, _) = pcreExec(n, s, st, false)
            let q = (if rc == 1: a - st else: -1)
            if member(noOcc.re, toSyms(u)) != (q == -1):
              bad.add "skNoOcc " & w
            for j in 0 .. u.len:
              let mw = toSyms(u[0 ..< j]) & @[markSym] & toSyms(u[j .. ^1])
              if member(mark.re, mw) != (k == okMatch and pos - st == j):
                bad.add "lkMark " & w & " " & $j
              if member(first.re, mw) != (q == j):
                bad.add "skFirst " & w & " " & $j
            if bad.len > 20: break
      echo "  ", runs, " runs, ", bad.len, " differ, ", lap()
      checkpoint bad.join("\n")
      check bad.len == 0

  when s8btAnyPart == 2:
    test "replace: the step table, directly and through Z3":
      var bad: seq[string]
      var runs, checked = 0
      var ctr = 0
      proc fresh(tag: string): string =
        inc ctr
        tag & "#" & $ctr
      for p in anyPats:
        let n = buildNfa(parsePcre(p), pcreSearchEngine())
        if not n.ok: continue
        let t = stepTable(n)
        check t.ok
        if not t.ok:
          bad.add escape(p) & " " & t.why
          continue
        let rx = re(p)
        for s in anyWords(3):
          inc runs
          if replaceRef(n, t, s, "-") != replace(s, rx, "-") and bad.len < 40:
            bad.add "table " & escape(p) & " " & escape(s)
        let ctx = newContext()
        setCurrentContext(ctx)
        let sv = mkStringVar("s")
        let r = replaceStepZ3(sv, mkString("-"), n, t, fresh)
        for k, s in anyWords(2):
          if k mod 3 != 0: continue
          inc checked
          let sol = newSolver(ctx)
          let prm = newParams(ctx)
          prm.set("timeout", 10000)
          sol.setParams(prm)
          sol.add sv == mkString(s)
          sol.add r != mkString(replace(s, rx, "-"))
          let res = $sol.check()
          if res != "zsUnsat" and bad.len < 40:
            bad.add "z3 " & escape(p) & " " & escape(s) & " " & res
      echo "  ", runs, " replace runs, ", checked, " Z3 values, ", bad.len,
           " differ, ", lap()
      checkpoint bad.join("\n")
      check bad.len == 0

  when s8btAnyPart in 3 .. 4:
    test "the entries' Z3 formulas":
      var bad: seq[string]
      var checked = 0
      var ctr = 0
      proc fresh(tag: string): string =
        inc ctr
        tag & "#" & $ctr
      for p in ["(*UTF)(*ANY)a$", "(*UTF)(*ANY)(?m)^a", "(*UTF)(*ANY)(?m)a$",
                "(*UTF)(*ANY).+"]:
        let rx = re(p)
        # The newlines, a lone 0x85 inside a character, and plain ones.
        for subj in ["", "a", "\u0085", "\u2028", "a\u2029", "a\u0085",
                     "\u0105\u2028", "\u2000b", "a\n", "\u00e9a", "ba"]:
          let ctx = newContext()
          setCurrentContext(ctx)
          var cases: seq[(string, int, int)]
          for st in 0 .. subj.len:
            if s8btAnyPart == 3:
              cases.add ("matchLen", st, subj.matchLen(rx, st))
              cases.add ("find", st, subj.find(rx, st))
            # (Z3 takes seconds on each of these: part 4, the start only,
            # a newline after a character, and a lone 0x85.)
            if st == 0 and s8btAnyPart == 4 and
               p in ["(*UTF)(*ANY).+", "(*UTF)(*ANY)(?m)a$"] and
               subj in ["a\u2029", "a\u0085", "\u0105\u2028"]:
              cases.add ("findBoundsLast", st, subj.findBounds(rx, st).last)
          if s8btAnyPart == 3:
            cases.add ("endsWith", 0, int(subj.endsWith(rx)))
            cases.add ("contains", 0, int(subj.contains(rx)))
          for (name, st, real) in cases:
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
            prm.set("timeout", 60000)
            sol.setParams(prm)
            for d in r.defs: sol.add d
            if name in ["endsWith", "contains"]:
              sol.add(if real == 1: not r.b else: r.b)
            else:
              sol.add r.i != mkInt(real)
            let res = $sol.check()
            if res != "zsUnsat": bad.add res & " " & where
          if bad.len > 20: break
      echo "  ", checked, " cases, ", bad.len, " differ, ", lap()
      checkpoint bad.join("\n")
      check bad.len == 0
