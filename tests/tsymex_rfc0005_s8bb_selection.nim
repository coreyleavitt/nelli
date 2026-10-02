## RFC-0005 S8bb -- PCRE's match SELECTION (`pcre_select.nim`) against
## the concrete `std/re`, exhaustively over short subjects:
##   * the concrete priority run `chosenEnd` is PCRE's `matchLen` at every
##     start of every subject;
##   * each selection language (`lkMark`, `lkNone`, `lkEnds`) and search
##     language (`skNoOcc`, `skFirst`) holds exactly the words PCRE's
##     choice puts in it;
##   * the Z3 formulas of every entry point on a ground subject, for the
##     patterns the edge-split reading declined in S8ay, have the concrete
##     call's value as their ONLY solution.
## `-d:nelliRegexExhaustive` widens every subject length by one (minutes,
## not for CI).
import std/[unittest, strutils, re, times]
import z3
import nelli/smt/regex_parser
import nelli/smt/pcre_select

const widen = (when defined(nelliRegexExhaustive): 1 else: 0)

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

# ---- RFC-0005 S8bb item 3: PCRE's match selection ---------------------------

const selPatterns = ["", "a", "a|ab", "ab|a", "a*b", "a*", "a*?", "a+?b",
  "(ab)+", "(a|ab)(c|bcd)?", "(a|)*b", "(a*)*", "(a*)+b", "(a|b)*?b",
  "(a?)+?a", "(|a)+", "(a|ab)*", "(ab|a)*", "a{2,3}", "a{2,3}?",
  "(a|ab){1,2}b?", "^a|b", "a$|ab", "a\\Z|a", "a\\z|a", "a$\n?", "(a$|b)*",
  "^(a|^b)*", "\\Aa|b$", "a(^|b)", "(a\\n?)*$", "x*", "(?:a|b?)*",
  "(a?){2,3}b", "b*a|b", ".*a", ".*?a", "(a|b|ab)*$", "(a$)?a?", "\n|a\n",
  "(\n?$)+", "b+", ".", "[^a]", "^a", "a$", "a\\Z", "a\\z", "a.b", "\\s",
  "\\S+$"]

const markSym = 256
const markSym2 = 257

proc ends(r: RNode; w: seq[int]; i: int): seq[int] =
  ## Every end of a match of the selection regex `r` from `i` in `w`.
  case r.kind
  of rkEmpty: @[]
  of rkEps: @[i]
  of rkSet:
    if i < w.len and w[i] < 256 and char(w[i]) in r.bytes: @[i + 1] else: @[]
  of rkMark:
    if i < w.len and w[i] == markSym: @[i + 1] else: @[]
  of rkMark2:
    if i < w.len and w[i] == markSym2: @[i + 1] else: @[]
  of rkCat:
    var cur = @[i]
    for k in r.kids:
      var nx: seq[int]
      for c in cur:
        for e in ends(k, w, c):
          if e notin nx: nx.add e
      cur = nx
    cur
  of rkAlt:
    var res: seq[int]
    for k in r.kids:
      for e in ends(k, w, i):
        if e notin res: res.add e
    res
  of rkStar:
    var res = @[i]
    var frontier = @[i]
    while frontier.len > 0:
      var nx: seq[int]
      for c in frontier:
        for e in ends(r.kids[0], w, c):
          if e notin res:
            res.add e
            nx.add e
      frontier = nx
    res

proc member(r: RNode; w: seq[int]): bool = w.len in ends(r, w, 0)

proc toSyms(s: string): seq[int] =
  for c in s: result.add ord(c)

suite "S8bb (3): PCRE's match selection against the concrete std/re":

  test "the priority run is PCRE's matchLen at every start":
    var bad: seq[string]
    var checked = 0
    for p in selPatterns:
      let pr = parsePcre(p)
      check pr.status == psOk
      let rx = re(p)
      let n = buildNfa(pr.root, pr.groups)
      for s in words("ab\n", 5 + widen):
        for st in 0 .. s.len:
          let real = s.matchLen(rx, st)
          inc checked
          if chosenEnd(n, s[st .. ^1], st == 0) != real and bad.len < 10:
            bad.add escape(p) & " " & escape(s) & " start " & $st
    echo "  chosenEnd: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check checked > 80_000

  test "each selection language holds exactly PCRE's choices":
    var bad: seq[string]
    var checked = 0
    for p in selPatterns:
      let pr = parsePcre(p)
      let rx = re(p)
      let n = buildNfa(pr.root, pr.groups)
      for atStart in [true, false]:
        let none = selectionLang(n, p, lkNone, atStart)
        let mark = selectionLang(n, p, lkMark, atStart)
        let endsL = selectionLang(n, p, lkEnds, atStart, nonEmpty = true)
        check none.ok and mark.ok and endsL.ok
        if not (none.ok and mark.ok and endsL.ok): continue
        for u in words("ab\n", 5 + widen):
          # Away from the subject start: `u` follows a `b`.
          let real = (if atStart: u.matchLen(rx, 0)
                      else: ("b" & u).matchLen(rx, 1))
          inc checked
          let where = escape(p) & " " & escape(u) & " atStart " & $atStart
          if member(none.re, toSyms(u)) != (real == -1) and bad.len < 10:
            bad.add "lkNone " & where
          if member(endsL.re, toSyms(u)) != (u.len >= 1 and real == u.len) and
             bad.len < 10:
            bad.add "lkEnds " & where
          for k in 0 .. u.len:
            let w = toSyms(u[0 ..< k]) & @[markSym] & toSyms(u[k .. ^1])
            if member(mark.re, w) != (real == k) and bad.len < 10:
              bad.add "lkMark " & where & " k " & $k
    echo "  languages: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check checked > 30_000

  test "each search language holds exactly the leftmost match":
    var bad: seq[string]
    var checked = 0
    for p in selPatterns:
      let pr = parsePcre(p)
      let rx = re(p)
      let n = buildNfa(pr.root, pr.groups)
      for atStart in [true, false]:
        let noOcc = searchLang(n, p, skNoOcc, atStart)
        let first = searchLang(n, p, skFirst, atStart)
        check noOcc.ok and first.ok
        if not (noOcc.ok and first.ok): continue
        for u in words("ab\n", 5 + widen):
          # Away from the subject start: `u` follows a `b`.
          let f = (if atStart: u.find(rx, 0) else: ("b" & u).find(rx, 1))
          let real = (if atStart or f < 0: f else: f - 1)
          inc checked
          let where = escape(p) & " " & escape(u) & " atStart " & $atStart
          if member(noOcc.re, toSyms(u)) != (real == -1) and bad.len < 10:
            bad.add "skNoOcc " & where
          for q in 0 .. u.len:
            let w = toSyms(u[0 ..< q]) & @[markSym] & toSyms(u[q .. ^1])
            if member(first.re, w) != (real == q) and bad.len < 10:
              bad.add "skFirst " & where & " q " & $q
    echo "  search languages: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check checked > 30_000

  test "the Z3 formulas have the concrete value as their only solution":
    # Each formula is built on a ground subject; a solver must find the
    # concrete value and refute every other.
    let ctx = newContext()
    setCurrentContext(ctx)
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    var bad: seq[string]
    var checked, declined = 0
    for p in ["a|ab", "a*b", "(ab)+", "\\Aa|b$", "(a|)*b", "a(^|b)", "a$|ab",
              "(a|ab)(c|bcd)?", "^(a|^b)*", "a*?"]:
      let rx = re(p)
      for subj in words("ab\n", 2 + widen):
        var cases: seq[(string, int, int)]
        for st in -1 .. subj.len + 1:
          cases.add ("matchLen", st, subj.matchLen(rx, st))
          cases.add ("findBoundsLast", st, subj.findBounds(rx, st).last)
          cases.add ("findBoundsFirst", st, subj.findBounds(rx, st).first)
          cases.add ("find", st, subj.find(rx, st))
          cases.add ("contains", st, int(subj.contains(rx, st)))
          cases.add ("match", st, int(subj.match(rx, st)))
        cases.add ("endsWith", 0, int(subj.endsWith(rx)))
        cases.add ("startsWith", 0, int(subj.startsWith(rx)))
        for (name, st, real) in cases:
          let sp = RegexSpec(entry: name, flag: "re", pattern: p)
          let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj),
                                  mkInt(st), fresh)
          if r.outcome != roValue:
            inc declined
            continue
          inc checked
          let sol = newSolver(ctx)
          for d in r.defs: sol.add d
          if name in ["endsWith", "match", "startsWith", "contains"]:
            sol.add(if real == 1: not r.b else: r.b)
          else:
            sol.add r.i != mkInt(real)
          if $sol.check() != "zsUnsat" and bad.len < 10:
            bad.add escape(p) & " " & escape(subj) & " " & name & "(" & $st &
                    ") real " & $real
    echo "  Z3 formulas: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check declined == 0
    check checked > 1_000
