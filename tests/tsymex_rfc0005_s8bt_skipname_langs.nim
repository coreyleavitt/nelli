## RFC-0005 S8bt (item 4) -- the symbolic forms of a mixed `(*SKIP:NAME)`
## whose `ignore_skip_arg` outlives an attempt (a SKIP's jump or a re-run
## past a CRLF's LF after a SKIP:NAME without its MARK keeps it for the
## next one): the search languages (`searchLangV`, the verifiers keyed by
## the count before and after the attempt) and the step table (a start
## state per count, `Leaf.ign`) against the concrete reference
## (`pcreExec`, `pcreReplace`; pinned against std/re by
## `tsymex_rfc0005_s8bt_skipname*`), in every start variant; and
## `replace` through Z3 on a few subjects.
import std/[unittest, strutils, times]
import z3
import nelli/smt/[pcre_syntax, pcre_select, regex_parser]
import ./s8bt_harness/[member, stepref]
import ./s8bt_harness/jit_corpus

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

const pats = [
  "(b)(*MARK:A)(*SKIP:A)x|(a)(*SKIP:B)y|(a)(*SKIP)q|(b)",
  "bc(*MARK:A)(*SKIP:A)x|a(*SKIP:B)y|ab(*SKIP)q|c",
  "b(*MARK:A)(*SKIP:A)x|a(*SKIP:B)y|a(*SKIP)q|b",
  "a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x|.",
  "(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c",
  "(*CRLF)\\s(*SKIP:B)y|\\sb(*MARK:A)(*SKIP:A)x|b",
  "(*CRLF)[\\x09-\\x0b](*SKIP:B)a|[\\x09-\\x0b]",
  "(*CRLF)(*MARK:A)\\s(*SKIP:B)b(*SKIP:A)|(*SKIP)\\s"]

proc subjectsFor(p: string): seq[string] =
  if p.startsWith("(*CRLF)"): words("ab\r\n", 4) else: words("abcx", 4)

suite "S8bt: mixed (*SKIP:NAME), symbolically":

  test "the patterns keep a count across attempts":
    for p in pats:
      let n = buildNfa(parsePcre(p))
      check n.ok
      check n.countArgs

  test "search languages, every variant":
    var bad: seq[string]
    var srch, declined = 0
    for p in pats:
      let n = buildNfa(parsePcre(p))
      let key = "skipname:" & p
      for pc in startClasses(n):
        let pre = prefixOf(pc)
        let noOcc = searchLangV(n, key, skNoOcc, pc)
        let first = searchLangV(n, key, skFirst, pc)
        let span = searchLangV(n, key, skSpan, pc)
        if not (noOcc.ok and first.ok and span.ok):
          inc declined
          bad.add "declined: " & escape(p) & " " & $pc & " " & noOcc.why &
                  first.why & span.why
          continue
        for u in subjectsFor(p):
          let subj = pre & u
          let st = pre.len
          let (rc, a, b) = pcreExec(n, subj, st, false)
          doAssert rc >= -1
          inc srch
          let q = (if rc == 1: a - st else: -1)
          let e = (if rc == 1: b - st else: -1)
          let where = escape(p) & " " & escape(u) & " after " & $pc
          if member(noOcc.re, toSyms(u)) != (q == -1):
            bad.add "skNoOcc " & where
          for k in 0 .. u.len:
            let w = toSyms(u[0 ..< k]) & @[markSym] & toSyms(u[k .. ^1])
            if member(first.re, w) != (q == k):
              bad.add "skFirst " & where & " q " & $k
            for k2 in k .. u.len:
              let w2 = toSyms(u[0 ..< k]) & @[markSym] & toSyms(u[k ..< k2]) &
                       @[markSym2] & toSyms(u[k2 .. ^1])
              if member(span.re, w2) != (q == k and e == k2):
                bad.add "skSpan " & where & " " & $k & ".." & $k2
          if bad.len > 20: break
    echo "  ", pats.len, " patterns, ", srch, " searches, ", declined,
         " declined, ", bad.len, " differ, ", lap()
    checkpoint bad[0 ..< min(bad.len, 30)].join("\n")
    check declined == 0
    check bad.len == 0

  test "step table: find and replace":
    var bad: seq[string]
    var calls = 0
    var counts = 0
    for p in pats:
      let n = buildNfa(parsePcre(p))
      let t = stepTable(n)
      check t.ok
      if not t.ok:
        bad.add "declined: " & escape(p) & " " & t.why
        continue
      if t.igns.len > 1: inc counts
      for s in subjectsFor(p):
        for st in 0 .. s.len:
          inc calls
          let (rc, a, b) = pcreExec(n, s, st, false)
          let want = (if rc == 1: (a, b) else: (-1, 0))
          let got = execRef(n, t, s, st, false)
          if got != want:
            bad.add escape(p) & " find(" & escape(s) & ", " & $st & ") = " &
                    $got & ", model: " & $want
        let r = replaceRef(n, t, s, "-")
        if r != pcreReplace(n, s, "-"):
          bad.add escape(p) & " replace(" & escape(s) & ") = " & escape(r)
    echo "  ", pats.len, " patterns (", counts, " with a kept count), ",
         calls, " calls, ", bad.len, " differ, ", lap()
    checkpoint bad[0 ..< min(bad.len, 30)].join("\n")
    check bad.len == 0
    check counts >= 5

  test "capture languages of the found attempt, per kept count":
    var bad: seq[string]
    var caps, multi, kept = 0
    for p in pats:
      let pr = parsePcre(p)
      if pr.groups == 0: continue
      let n = buildNfa(pr)
      let igs = attemptIgns(n)
      if igs.len > 1: inc multi
      let key = "skipname:" & p
      for pc in startClasses(n):
        let pre = prefixOf(pc)
        for u in subjectsFor(p):
          let subj = pre & u
          let st = pre.len
          let ((rc, a, _), ign) = pcreExecIgn(n, subj, st, false)
          if rc != 1: continue
          let q = a - st
          # The found attempt's count: the one `skFirst` language that
          # holds of `u` marked at `q`.
          let w = toSyms(u[0 ..< q]) & @[markSym] & toSyms(u[q .. ^1])
          var found: seq[int8]
          for ig in igs:
            let f = searchLangV(n, key, skFirst, pc, foundIgn = ig)
            check f.ok
            if f.ok and member(f.re, w): found.add ig
          if found != @[ign]:
            bad.add "foundIgn " & escape(p) & " " & escape(u) & " " &
                    $found & ", reference " & $ign
            continue
          if ign != 0: inc kept
          let elig = n.hasNeverSkip and n.skipActive and a > st and
                     subj[a - 1] == '\r' and a < subj.len and subj[a] == '\n'
          let (e, cs) = chosenCapsAt(n, subj, a, st, false, ign)
          doAssert e >= 0
          let w2 = subj[a .. ^1]
          for g in 1 .. pr.groups:
            inc caps
            let pcA = classAt(subj, a)
            let setL = captureLangV(n, key, g, pcA, false, false, elig, ign)
            let capL = captureLangV(n, key, g, pcA, true, false, elig, ign)
            check setL.ok and capL.ok
            if not (setL.ok and capL.ok): continue
            let isSet = cs[g - 1][0] >= 0
            if member(setL.re, toSyms(w2)) != isSet:
              bad.add "capSet " & escape(p) & " g" & $g & " " & escape(subj)
            for x in 0 .. w2.len:
              for y in x .. w2.len:
                let wm = toSyms(w2[0 ..< x]) & @[markSym] &
                         toSyms(w2[x ..< y]) & @[markSym2] &
                         toSyms(w2[y .. ^1])
                let want = isSet and cs[g - 1] == (a + x, a + y)
                if member(capL.re, wm) != want:
                  bad.add "capMark " & escape(p) & " g" & $g & " " &
                          escape(subj) & " " & $x & ".." & $y
        if bad.len > 20: break
    echo "  ", caps, " captures (", multi, " patterns with a kept count, ",
         kept, " found attempts with one), ", bad.len, " differ, ", lap()
    checkpoint bad[0 ..< min(bad.len, 30)].join("\n")
    check bad.len == 0
    check multi >= 1
    check kept >= 1

  test "the Z3 replace term's only value is the reference's":
    var checked = 0
    var bad: seq[string]
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    for p in pats:
      let n = buildNfa(parsePcre(p))
      let t = stepTable(n)
      if not t.ok: continue
      let ctx = newContext()
      setCurrentContext(ctx)
      let sv = mkStringVar("s")
      let r = replaceStepZ3(sv, mkString("-"), n, t, fresh)
      let subs = subjectsFor(p)
      for k, subj in subs:
        # Every subject up to length 3, every seventh of length 4.
        if subj.len == 4 and k mod 7 != 0: continue
        let want = pcreReplace(n, subj, "-")
        inc checked
        let sol = newSolver(ctx)
        let prm = newParams(ctx)
        prm.set("timeout", 10000)
        sol.setParams(prm)
        sol.add sv == mkString(subj)
        sol.add r != mkString(want)
        let res = $sol.check()
        if res != "zsUnsat" and bad.len < 20:
          bad.add escape(p) & " " & escape(subj) & " " & res
    echo "  Z3 replace values: ", checked, " cases, ", lap()
    checkpoint bad.join("\n")
    check bad.len == 0
