## RFC-0005 S8bj -- the selection, search and capture languages of the
## agenda (`pcre_select`) against the real `std/re`, for the backtracking
## verbs, `(?m)`, the newline conventions' CRLF start skip and the start
## options, in every start variant (what precedes the start offset:
## `PrevClass`).
##
## A variant's subject is a prefix of that class followed by `u`, the call
## starting after the prefix:
##   * `lkNone` / `lkMark` / `lkEnds`: the anchored attempt (`matchLen`);
##   * `skNoOcc` / `skFirst` / `skSpan`: the search (`find`, `findBounds`);
##   * the capture languages, anchored (`matchLen`'s captures) and
##     unanchored (`findBounds`' captures).
## RFC-0005 S8bt: the unanchored languages (the search, the unanchored
## captures) are those of the engine std/re runs the call on
## (`pcre_engine.pcreSearchEngine`: 8.37's JIT on the Windows legs).
import std/[unittest, strutils, re, times, tables]
import nelli/smt/[pcre_syntax, pcre_select, pcre_engine]

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

const markSym = 256
const markSym2 = 257

var memo: Table[(pointer, int), seq[int]]

proc ends(r: RNode; w: seq[int]; i: int): seq[int] =
  ## Every end of a match of the regex `r` from `i` in `w` (memoized per
  ## word: the regexes share subterms and nest stars).
  let key = (cast[pointer](r), i)
  if key in memo: return memo[key]
  case r.kind
  of rkEmpty: result = @[]
  of rkEps: result = @[i]
  of rkSet:
    result = (if i < w.len and w[i] < 256 and char(w[i]) in r.bytes: @[i + 1]
              else: @[])
  of rkMark:
    result = (if i < w.len and w[i] == markSym: @[i + 1] else: @[])
  of rkMark2:
    result = (if i < w.len and w[i] == markSym2: @[i + 1] else: @[])
  of rkCat:
    var cur = @[i]
    for k in r.kids:
      var nx: seq[int]
      for c in cur:
        for e in ends(k, w, c):
          if e notin nx: nx.add e
      cur = nx
    result = cur
  of rkAlt:
    for k in r.kids:
      for e in ends(k, w, i):
        if e notin result: result.add e
  of rkStar:
    result = @[i]
    var frontier = @[i]
    while frontier.len > 0:
      var nx: seq[int]
      for c in frontier:
        for e in ends(r.kids[0], w, c):
          if e notin result:
            result.add e
            nx.add e
      frontier = nx
  memo[key] = result

proc member(r: RNode; w: seq[int]): bool =
  memo.clear()
  w.len in ends(r, w, 0)

proc toSyms(s: string): seq[int] =
  for c in s: result.add ord(c)

proc prefixOf(pc: PrevClass): string =
  case pc
  of pcStart: ""
  of pcOther: "b"
  of pcLF: "\n"
  of pcCRLF: "\r\n"
  of pcCR: "\r"
  of pcNl: "\x0c"

const patterns = [
  # verbs
  "a(*COMMIT)b|.", "(*COMMIT)a|b", "a+(*COMMIT)b", "(?:a(*COMMIT)b|a)",
  "a(*PRUNE)b|.", "a+(*PRUNE)b|a", "a(*SKIP)b|.", "aa(*SKIP)b|a+",
  "a+(*SKIP)b|.", "(*MARK:A)a(*SKIP:A)b|.", "a(*MARK:A)a(*SKIP:A)b|.",
  "a(*SKIP:B)b|.", "(?:a(*SKIP:B)b|ab)", "(?:a(*THEN)b|ab)",
  "(?:a(*THEN)b|a)b?", "a(?:b(*THEN)c|bd)|abd", "(?:a(*THEN)|b)+c",
  "(?:a(*THEN)b|a){2}", "(a(*THEN)b|ab)", "(a)(*SKIP)b|(a)",
  "(?:(a)(*PRUNE)b|a)", "x?(*COMMIT)a", "a*(*THEN)b|ab",
  # (?m) and the conventions
  "(?m)^a", "(?m)a$", "(?m)^$", "(?m)^", "(*CRLF)(?m)$", "(*CRLF)(?m)^a",
  "(*ANYCRLF)(?m)^.", "(*CR)(?m)$\\r", "(*ANY)(?m)^", "(*CRLF)(?m)a$|b",
  # the CRLF start skip and the start-of-match scan
  "(*CRLF)\\s", "(*CRLF)[\\x09-\\x0b]\\z", "(*ANYCRLF)\\s?$", "(*ANY)\\v",
  "(*CRLF)\\s(*SKIP)b", "(*CRLF)(*COMMIT)\\s", "(*ANYCRLF).?b",
  "(*CRLF)(*NO_START_OPT)\\s", "(*NO_START_OPT)a(*COMMIT)b|.",
  "(*ANYCRLF)(?m)^\\s", "(*CRLF)(?:\\r|x)?(*COMMIT)."]


# RFC-0005 S8bj: the patterns are split by parity between this file and its
# `_b` twin (which includes this one with `s8bjPart = 1`), so each runs
# under 60 s on the Windows legs.
when not declared(s8bjPart):
  const s8bjPart = 0

proc inPart(i: int): bool = i mod 2 == s8bjPart

suite "S8bj: the agenda's languages against std/re (part " & $s8bjPart & ")":

  test "every pattern, every variant, every language":
    var bad: seq[string]
    var att, srch, caps = 0
    for i, p in patterns:
      if not inPart(i): continue
      let tp = epochTime()
      defer:
        if epochTime() - tp > 0.5:
          echo "    ", escape(p), " ", formatFloat(epochTime() - tp, ffDecimal, 1)
      let pr = parsePcre(p)
      checkpoint escape(p) & " " & $pr.status & " " & pr.reason
      check pr.status == psOk
      if pr.status != psOk: continue
      let rx = re(p)
      let n = buildNfa(pr)
      check n.ok
      if not n.ok: continue
      let ns = buildNfa(pr, pcreSearchEngine())
      check ns.ok
      let search = ns.ok
      for pc in startClasses(n):
        let pre = prefixOf(pc)
        let none = selectionLangV(n, p, lkNone, pc)
        let mark = selectionLangV(n, p, lkMark, pc)
        let endsL = selectionLangV(n, p, lkEnds, pc, nonEmpty = true)
        let noOcc = searchLangV(ns, p, skNoOcc, pc)
        let first = searchLangV(ns, p, skFirst, pc)
        let span = searchLangV(ns, p, skSpan, pc)
        check none.ok and mark.ok and endsL.ok and noOcc.ok and first.ok and
              span.ok
        if not (none.ok and mark.ok and endsL.ok and noOcc.ok and first.ok and
                span.ok):
          echo "    not ok: ", escape(p), " ", pc, " ", none.why, mark.why,
               endsL.why, noOcc.why, first.why, span.why
          continue
        for u in words("ab\r\n", 3):
          let subj = pre & u
          let st = pre.len
          let real = subj.matchLen(rx, st)
          let where = escape(p) & " " & escape(u) & " after " & $pc
          inc att
          if member(none.re, toSyms(u)) != (real == -1):
            bad.add "lkNone " & where
          if member(endsL.re, toSyms(u)) != (u.len >= 1 and real == u.len):
            bad.add "lkEnds " & where
          for k in 0 .. u.len:
            let w = toSyms(u[0 ..< k]) & @[markSym] & toSyms(u[k .. ^1])
            if member(mark.re, w) != (real == k):
              bad.add "lkMark " & where & " k " & $k
          if not search: continue
          inc srch
          let f = subj.find(rx, st)
          let fb = subj.findBounds(rx, st)
          let q = (if f < 0: -1 else: f - st)
          let e = (if f < 0: -1 else: fb.last + 1 - st)
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
      # The capture languages: anchored (the attempt at the start) and
      # unanchored (the attempt the search finds).
      for g in 1 .. pr.groups:
        for pc in startClasses(n):
          let pre = prefixOf(pc)
          for anch in [true, false]:
            if not anch and not search: continue
            let na = (if anch: n else: ns)
            let setL = captureLangV(na, p, g, pc, false, anch)
            let capL = captureLangV(na, p, g, pc, true, anch)
            check setL.ok and capL.ok
            if not (setL.ok and capL.ok): continue
            for u in words("ab\r\n", 3):
              # The concrete attempt at the start (pinned against std/re
              # below), anchored or not.
              let subj = pre & u
              let st = pre.len
              let (e, cs) = chosenCapsAt(na, subj, st, st, anch)
              let isSet = e >= 0 and cs[g - 1][0] >= 0
              inc caps
              let where = escape(p) & " g" & $g & " " & escape(u) & " after " &
                          $pc & " anchored " & $anch
              if member(setL.re, toSyms(u)) != isSet:
                bad.add "capSet " & where
              for a in 0 .. u.len:
                for b in a .. u.len:
                  let w = toSyms(u[0 ..< a]) & @[markSym] & toSyms(u[a ..< b]) &
                          @[markSym2] & toSyms(u[b .. ^1])
                  let want = isSet and cs[g - 1] == (st + a, st + b)
                  if member(capL.re, w) != want:
                    bad.add "capMark " & where & " " & $a & ".." & $b
    echo "  langs: ", att, " attempts, ", srch, " searches, ", caps,
         " captures, ", bad.len, " differ, ", lap()
    checkpoint bad[0 ..< min(bad.len, 30)].join("\n")
    check bad.len == 0
    check att > 1_500

  test "the concrete captures are std/re's":
    # `chosenCapsAt` above: the anchored attempt's groups against std/re's
    # `matchLen` with captures (PCRE_ANCHORED), the unanchored one's at the
    # start the search finds against `findBounds`' groups.
    var bad: seq[string]
    var n0 = 0
    for i, p in patterns:
      if not inPart(i): continue
      let pr = parsePcre(p)
      if pr.status != psOk or pr.groups == 0: continue
      let rx = re(p)
      let n = buildNfa(pr)
      for subj in words("ab\r\n", 4):
        for st in 0 .. subj.len:
          var m = newSeq[string](pr.groups)
          for i in 0 ..< m.len: m[i] = "?"
          let real = subj.matchLen(rx, m, st)
          let (e, cs) = chosenCapsAt(n, subj, st)
          inc n0
          let got = (if e < 0: -1 else: e - st)
          if got != real:
            bad.add escape(p) & " " & escape(subj) & " " & $st & " len"
            continue
          if real < 0: continue
          var hi = 0
          for g in 1 .. pr.groups:
            if cs[g - 1][0] >= 0: hi = g
          for g in 1 .. pr.groups:
            let want = (if g <= hi:
                          (if cs[g - 1][0] < 0: ""
                           else: subj[cs[g - 1][0] ..< cs[g - 1][1]])
                        else: "?")
            if m[g - 1] != want:
              bad.add escape(p) & " " & escape(subj) & " " & $st & " g" & $g
          # The unanchored attempt the search finds: findBounds' groups.
          var b = newSeq[tuple[first, last: int]](pr.groups)
          for i in 0 ..< b.len: b[i] = (first: -1, last: 0)
          let r = subj.findBounds(rx, b, st)
          if r.first < 0: continue
          let (e2, cs2) = chosenCapsAt(buildNfa(pr, pcreSearchEngine()), subj,
                                       r.first, st, false)
          if e2 != r.last + 1:
            bad.add escape(p) & " " & escape(subj) & " " & $st & " unanch len"
            continue
          for g in 1 .. pr.groups:
            let want = (if cs2[g - 1][0] < 0: (first: -1, last: 0)
                        else: (first: cs2[g - 1][0], last: cs2[g - 1][1] - 1))
            if b[g - 1] != want:
              bad.add escape(p) & " " & escape(subj) & " " & $st & " unanch g" &
                      $g
    checkpoint bad[0 ..< min(bad.len, 20)].join("\n")
    check bad.len == 0
    check n0 > 300
