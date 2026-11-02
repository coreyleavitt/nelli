## RFC-0005 S8bt (item 2) -- the search and capture languages of PCRE 8.37's
## JIT (`buildNfa(.., peJit837)`: the guess-and-verify search reads the
## JIT's prefix scan, each guess an obligation on the bytes ahead) against
## the concrete JIT reference (`pcreExec`, `chosenCapsAt`; pinned against
## the JIT itself by `tsymex_rfc0005_s8bt_jit`), in every start variant:
## the occurrence languages (`skNoOcc`, `skFirst`, `skSpan`) and the
## unanchored capture languages.
import std/[unittest, strutils, times]
import nelli/smt/[pcre_syntax, pcre_select]
import ./s8bt_harness/[jit_corpus, member]

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

# The patterns: the scan's shapes (the skip table, the offsets, an
# alternation, a dot) under each convention, every verb tail under the
# CRLF-ish conventions, groups, and UTF mode -- split six ways, by measured
# cost, between this file and its `_b` .. `_f` twins (which include this
# one with `s8btLangsPart = 1` .. `5`), so each runs under 60 s on the
# Windows legs.
when not declared(s8btLangsPart):
  const s8btLangsPart = 0

const langParts = [
  @["(*UTF)(*CRLF)aéa(*SKIP)", "(*CRLF)\\sa(*MARK:A)(*SKIP:A)", "(*ANYCRLF)\\sa(*COMMIT)", "(\\s)(*SKIP)(a)|(b)", "abab", "\\sa", "(*CR)\\sa", "(*UTF)aéa"],
  @["(*CRLF)abab", "(*ANYCRLF)aba", "(*ANYCRLF)\\sa", "a.ab", "\\r\\na", "(*CR)\\r\\na"],
  @["(*ANY)abab", "(*CRLF)(a)(*SKIP)b|(.)", "(*ANY)(\\s)(*SKIP)(a)|(b)", "(*ANY)(\\s)(a)", "(*CRLF)\\sa(*SKIP:A)b|.", "(?:ab|ba)ab", "aba", "(*CR)aba"],
  @["(*ANY)a.ab", "(*CRLF)(\\s)(*SKIP)(a)|(b)", "(*ANY)(a)(*SKIP)b|(.)", "(*CRLF)\\sa", "(*UTF)(*CRLF)\\sé", "(*ANY)aba", "(*CRLF)\\r\\na", "(*ANYCRLF)\\sa(*MARK:A)(*SKIP:A)"],
  @["(*CRLF)a.ab", "(*CRLF)aba", "(*ANY)\\sa", "(*ANYCRLF)\\sa(*SKIP)", "(*ANYCRLF)\\r\\na", "(\\s)(a)"],
  @["(*CRLF)(?:ab|ba)ab", "(*CRLF)\\sa(*SKIP)", "(*CRLF)(\\s)(a)", "(*ANYCRLF)\\sa(*SKIP:A)b|.", "(*CRLF)\\sa(*COMMIT)", "(*ANY)\\r\\na", "(a)(*SKIP)b|(.)"]]

proc subjectsFor(p: string): seq[string] =
  if p.startsWith("(*UTF)"):
    result = @[""]
    for a in utfChars:
      result.add a
      for b in utfChars: result.add a & b
  else:
    result = words("ab\r\n\x0c", 3)

suite "S8bt: the JIT's languages against its concrete reference (part " &
      $s8btLangsPart & ")":

  test "search and capture languages, every variant":
    var bad: seq[string]
    var pats, srch, caps, declined = 0
    for p in langParts[s8btLangsPart]:
      let tp = epochTime()
      let pr = parsePcre(p)
      check pr.status == psOk
      let n = buildNfa(pr, peJit837)
      check n.ok
      if not n.ok: continue
      inc pats
      let key = "jit:" & p
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
          if rc < -1: continue    # an error (UTF): the languages say nothing
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
      for g in 1 .. pr.groups:
        for pc in startClasses(n):
          let pre = prefixOf(pc)
          let setL = captureLangV(n, key, g, pc, false, false)
          let capL = captureLangV(n, key, g, pc, true, false)
          check setL.ok and capL.ok
          if not (setL.ok and capL.ok): continue
          for u in subjectsFor(p):
            let subj = pre & u
            let st = pre.len
            let (e, cs) = chosenCapsAt(n, subj, st, st, false)
            let isSet = e >= 0 and cs[g - 1][0] >= 0
            inc caps
            let where = escape(p) & " g" & $g & " " & escape(u) & " after " &
                        $pc
            if member(setL.re, toSyms(u)) != isSet:
              bad.add "capSet " & where
            for a in 0 .. u.len:
              for b in a .. u.len:
                let w = toSyms(u[0 ..< a]) & @[markSym] & toSyms(u[a ..< b]) &
                        @[markSym2] & toSyms(u[b .. ^1])
                let want = isSet and cs[g - 1] == (st + a, st + b)
                if member(capL.re, w) != want:
                  bad.add "capMark " & where & " " & $a & ".." & $b
      if epochTime() - tp > 1.0:
        echo "    ", escape(p), " ", formatFloat(epochTime() - tp, ffDecimal, 1)
      if bad.len > 20: break
    echo "  ", pats, " patterns, ", srch, " searches, ", caps, " captures, ",
         declined, " declined, ", bad.len, " differ, ", lap()
    checkpoint bad[0 ..< min(bad.len, 30)].join("\n")
    check bad.len == 0
    check declined == 0
    check pats == langParts[s8btLangsPart].len
