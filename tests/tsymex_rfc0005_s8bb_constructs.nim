## RFC-0005 S8bb item 5 -- the constructs S8ay left undecided (named
## groups, inline options, `\p{..}`, the start options and verbs, the
## newline conventions, `(*ACCEPT)`) and the captures overloads, against
## the concrete `std/re`, exhaustively over short subjects:
##   * the concrete priority run over the reader's tree is PCRE's
##     `matchLen` at every start of every subject;
##   * the tagged run `chosenCaps` is `findBounds`' groups, and each capture
##     language holds exactly the group's spans;
##   * under each newline convention and with `(*ACCEPT)`, every language
##     and search the walker reads;
##   * every entry point's Z3 formula under a convention is the concrete
##     call's ONLY solution (the captures overloads' written elements:
##     `tsymex_rfc0005_s8bb_capvalues.nim`).
## Split from `tsymex_rfc0005_s8bb_selection.nim` (item 3) to keep each
## suite inside the per-backend runtime budget.
## `-d:nelliRegexExhaustive` widens every subject length by one (minutes,
## not for CI).
import std/[unittest, strutils, re, times]
import z3
import nelli/smt/regex_parser
import nelli/smt/pcre_syntax
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

# ---- RFC-0005 S8bb item 5: the constructs S8ay left undecided -----------------
#
# Each pattern below was `psUnknown` (⊤) at S8ay. The reader now reads it;
# PCRE's match (`chosenEnd` over the reader's tree) must be the concrete
# `matchLen` at every start of every subject over {a, A, 0xE9, _, SP, LF}.

const readPatterns = [
  # named groups
  "(?<n>a)A", "(?P<n>a)|A", "(?'n'a)+", "(?<n1>a)(?<n2>A)?",
  # inline options
  "(?i)a", "a(?i)a", "(?i:a)a", "(?i)[a-b]", "(?i)[^a]", "(?i)\\x41",
  "(?i)[[:upper:]]", "(?i)[[:^lower:]]", "(a(?i)a|_)A", "(?i)a|_A", "(?-i)a",
  "(?i)(?-i)a", "(?i)\\Qa\\E", "(?s).", "(?s:.)\n", "(?x) a  A ", "(?U)a+",
  "(?U)a+?", "(?iU)a*", "(?J)(?<n>a)", "(?i)\\w", "(?i)\xE9", "(?i)[\xC9-\xFF]",
  "(?i-s:a.)", "(?x:a A)A", "((?i)a)a",
  # properties
  "\\pL", "\\p{Lu}+", "\\P{L}", "\\p{^Ll}", "[\\p{Lu}_]", "[^\\p{L}]",
  "\\p{Latin}", "\\p{Greek}", "\\p{Xwd}*", "\\p{Any}", "\\p{L&}", "\\pZ",
  "(?i)\\p{Lu}", "[\\p{Lu}-z]",
  # start options and verbs
  "(*UCP)\\w+", "(*UCP)\\W", "(*UCP)\\s", "(*UCP)[[:alpha:]]",
  "(*UCP)[[:^alpha:]]", "(*UCP)[[:punct:]]", "(*UCP)(?i)[[:lower:]]",
  "(*UCP)[\\w]", "(*UCP)[^\\s]", "(*UCP)[[:graph:]]", "(*UCP)\\d",
  "(*LF)a$", "(*NO_START_OPT)a|A", "(*NO_AUTO_POSSESS)a+A",
  "(*BSR_UNICODE)a", "a(*F)|A", "(*FAIL)", "(*MARK:x)a", "a(*:y)A",
  "(*UCP)(*LF)\\w"]

const stillUndecided = ["(?m)a", "(?X)a", "(*UTF8)a", "(*UTF)a",
  "(*COMMIT)a", "(*PRUNE)a", "(*SKIP)a", "(*THEN)a", "(*PRUNE:n)a",
  "(?<n>a)(?<n>A)", "\\p{Foo}", "(?i)*", "(*LIMIT_MATCH=9)a",
  "(*LIMIT_RECURSION=9)a", "a(*ACCEPT)?", "\\R"]

suite "S8bb (5): the constructs S8ay left undecided, against std/re":

  test "each is read, and PCRE's match is the concrete matchLen":
    var bad: seq[string]
    var checked = 0
    for p in readPatterns:
      let pr = parsePcre(p)
      checkpoint escape(p) & " " & $pr.status & " " & pr.reason
      check pr.status == psOk
      if pr.status != psOk: continue
      let rx = re(p)
      let n = buildNfa(pr.root, pr.groups)
      for s in words("aA\xE9_ \n", 3 + widen):
        for st in 0 .. s.len:
          let real = s.matchLen(rx, st)
          inc checked
          if chosenEnd(n, s[st .. ^1], st == 0) != real and bad.len < 10:
            bad.add escape(p) & " " & escape(s) & " start " & $st &
                    " real " & $real
    echo "  read constructs: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check checked > 50_000

  test "what stays undecided":
    for p in stillUndecided:
      checkpoint escape(p)
      check parsePcre(p).status == psUnknown

# ---- RFC-0005 S8bb item 5: the captures overloads ------------------------------
#
# The groups of PCRE's chosen match: the concrete tagged run `chosenCaps`,
# each group's capture languages, and the Z3 value of every element a
# captures overload writes, against `std/re`'s own writes.

const capPatterns = ["(a)|(b)", "(?:(a)|b)*", "((a)|b)+", "(a*)+", "(a*)*",
  "(a|ab)(c|bcd|)", "(a?)*?b", "(^a|b)(\n)?", "(a)(b)?$", "(?:(a)|(b))*",
  "b(a)?", "(a$|b)*", "((a)?)+", "(a)|b(\n)", "(?<x>a)(?i)(B)?",
  "(a|)+b", "^(a)|(b)", "()", "a", "(a(b)?)+"]

suite "S8bb (5): the captures of PCRE's chosen match, against std/re":

  test "the tagged run is std/re's groups at every start":
    var bad: seq[string]
    var checked = 0
    for p in capPatterns:
      let pr = parsePcre(p)
      check pr.status == psOk
      let rx = re(p)
      let n = buildNfa(pr.root, pr.groups)
      for s in words("ab\n", 4 + widen):
        for st in 0 .. s.len:
          inc checked
          let real = s.matchLen(rx, st)
          let (e, caps) = chosenCaps(n, s[st .. ^1], st == 0)
          var ok = e == real
          if ok and real >= 0:
            # A match at `st` is the leftmost from `st`: findBounds' groups.
            # (An unset group above the highest set one is not written:
            # starting every element at (-1, 0) makes that invisible.)
            var b = newSeq[tuple[first, last: int]](pr.groups)
            for x in b.mitems: x = (first: -1, last: 0)
            discard s.findBounds(rx, b, st)
            for g in 0 ..< pr.groups:
              let want =
                if caps[g][0] < 0: (first: -1, last: 0)
                else: (first: st + caps[g][0], last: st + caps[g][1] - 1)
              if b[g] != want: ok = false
          if not ok and bad.len < 10:
            bad.add escape(p) & " " & escape(s) & " start " & $st
    echo "  chosenCaps: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check checked > 10_000

  test "each capture language holds exactly the group's spans":
    var bad: seq[string]
    var checked = 0
    for p in capPatterns:
      let pr = parsePcre(p)
      let n = buildNfa(pr.root, pr.groups)
      for g in 1 .. pr.groups:
        for atStart in [true, false]:
          let setL = captureLang(n, p, g, atStart, marked = false)
          let capL = captureLang(n, p, g, atStart, marked = true)
          check setL.ok and capL.ok
          if not (setL.ok and capL.ok): continue
          for u in words("ab\n", 4 + widen):
            inc checked
            let (e, caps) = chosenCaps(n, u, atStart)
            let isSet = e >= 0 and caps[g - 1][0] >= 0
            let where = escape(p) & " g" & $g & " " & escape(u) &
                        " atStart " & $atStart
            if member(setL.re, toSyms(u)) != isSet and bad.len < 10:
              bad.add "set " & where
            for a in 0 .. u.len:
              for b in a .. u.len:
                let w = toSyms(u[0 ..< a]) & @[markSym] & toSyms(u[a ..< b]) &
                        @[markSym2] & toSyms(u[b .. ^1])
                let want = isSet and caps[g - 1] == (a, b)
                if member(capL.re, w) != want and bad.len < 10:
                  bad.add "cap " & where & " " & $a & ".." & $b
    echo "  capture languages: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check checked > 5_000

  # The Z3 value of each written element: `tsymex_rfc0005_s8bb_capvalues`
  # (split out for the per-backend runtime budget, RFC-0005 S8bb item 8).

# ---- RFC-0005 S8bb item 5: newline conventions and (*ACCEPT) -----------------
#
# The start options `(*CR)`, `(*CRLF)`, `(*ANYCRLF)`, `(*ANY)` change what
# `.` / `\N` exclude and where `$` / `\Z` hold (before a final newline
# SEQUENCE: CRLF is two bytes). `(*ACCEPT)` ends the match where it is
# reached, closing the groups it is in. Every model (the concrete run,
# each language, the search, the captures, the Z3 formulas) against
# `std/re` over {a, b, CR, LF, FF}. With a CRLF convention and no explicit
# CR or LF, whether PCRE tries a match at a CRLF's LF is its start-of-match
# optimiser's call wherever a match can start at an LF (`crlfSkipSeen`):
# the occurrence search declines there, and only there.

const nlPatterns = ["(*CR)a$", "(*CR).", "(*CR).+", "(*CR)a\\Z", "(*CR)\\N",
  "(*CR)[^a]", "(*CR)(?s).", "(*CR).*$", "(*CRLF)a$", "(*CRLF).", "(*CRLF)..",
  "(*CRLF).*$", "(*CRLF)\\N+", "(*CRLF)a\\r?$", "(*CRLF)$", "(*CRLF)(a|.)*?$",
  "(*CRLF)\\Z", "(*CRLF)(.)\\z", "(*ANYCRLF)a$", "(*ANYCRLF).",
  "(*ANYCRLF).*$", "(*ANYCRLF)a\\r?$", "(*ANYCRLF)\\Z", "(*ANYCRLF)(.?)$",
  "(*ANY)a$", "(*ANY).", "(*ANY).*\\Z", "(*ANY)\\v$", "(*LF)(*CR)a$",
  "(*CR)(*LF).$", "(*CRLF)\\n|.", "(*ANYCRLF)[\\r]?.", "(*CRLF)\\s\\S|\\Sb",
  "(*ANYCRLF)\\Sb|\\s\\S", "(*ANY)\\v\\z", "(*CRLF)[\\x09-\\x0b]\\z",
  "(*CRLF)\\Q\r\\E?.", "(*ANYCRLF)\\s?$"]

const acceptPatterns = ["(*ACCEPT)b", "a(*ACCEPT)b", "a(?:(*ACCEPT)|b)",
  "(?:a(*ACCEPT))+", "(a(*ACCEPT)b)|(c)", "(a|b(*ACCEPT))*\\z",
  "(?:(a)(*ACCEPT)|ab)b", "((a)(*ACCEPT))*b", "a+(*ACCEPT)b|ab",
  "(*CRLF)(.(*ACCEPT))+$"]

const nlAlpha = "ab\r\n\x0c"

suite "S8bb (5): newline conventions and (*ACCEPT), against std/re":

  test "each is read, and every model is std/re's":
    var bad: seq[string]
    var runs, langs, searches, capsChecked, seen = 0
    for p in @nlPatterns & @acceptPatterns:
      let pr = parsePcre(p)
      checkpoint escape(p) & " " & $pr.status & " " & pr.reason
      check pr.status == psOk
      if pr.status != psOk: continue
      let rx = re(p)
      let n = buildNfa(pr)
      for s in words(nlAlpha, 4):
        for st in 0 .. s.len:
          inc runs
          let real = s.matchLen(rx, st)
          let (e, caps) = chosenCaps(n, s[st .. ^1], st == 0)
          var ok = chosenEnd(n, s[st .. ^1], st == 0) == real and e == real
          if ok and real >= 0 and pr.groups > 0:
            inc capsChecked
            var b = newSeq[tuple[first, last: int]](pr.groups)
            for x in b.mitems: x = (first: -1, last: 0)
            discard s.findBounds(rx, b, st)
            for g in 0 ..< pr.groups:
              let want =
                if caps[g][0] < 0: (first: -1, last: 0)
                else: (first: st + caps[g][0], last: st + caps[g][1] - 1)
              if b[g] != want: ok = false
          if not ok and bad.len < 10:
            bad.add "run " & escape(p) & " " & escape(s) & " start " & $st
      for atStart in [true, false]:
        let none = selectionLang(n, p, lkNone, atStart)
        let mark = selectionLang(n, p, lkMark, atStart)
        let endsL = selectionLang(n, p, lkEnds, atStart, nonEmpty = true)
        let noOcc = searchLang(n, p, skNoOcc, atStart)
        let first = searchLang(n, p, skFirst, atStart)
        let search = not crlfSkipSeen(n)
        if not search and atStart: inc seen
        check none.ok and mark.ok and endsL.ok
        check noOcc.ok == search and first.ok == search
        if not (none.ok and mark.ok and endsL.ok): continue
        for u in words(nlAlpha, 3):
          # Away from the subject start: `u` follows a `b`.
          let real = (if atStart: u.matchLen(rx, 0)
                      else: ("b" & u).matchLen(rx, 1))
          let f = (if atStart: u.find(rx, 0) else: ("b" & u).find(rx, 1))
          let realF = (if atStart or f < 0: f else: f - 1)
          inc langs
          if search: inc searches
          let where = escape(p) & " " & escape(u) & " atStart " & $atStart
          if member(none.re, toSyms(u)) != (real == -1) and bad.len < 10:
            bad.add "lkNone " & where
          if member(endsL.re, toSyms(u)) != (u.len >= 1 and real == u.len) and
             bad.len < 10:
            bad.add "lkEnds " & where
          if search and member(noOcc.re, toSyms(u)) != (realF == -1) and
             bad.len < 10:
            bad.add "skNoOcc " & where
          for k in 0 .. u.len:
            let w = toSyms(u[0 ..< k]) & @[markSym] & toSyms(u[k .. ^1])
            if member(mark.re, w) != (real == k) and bad.len < 10:
              bad.add "lkMark " & where & " k " & $k
            if search and member(first.re, w) != (realF == k) and
               bad.len < 10:
              bad.add "skFirst " & where & " q " & $k
      for g in 1 .. pr.groups:
        for atStart in [true, false]:
          let setL = captureLang(n, p, g, atStart, marked = false)
          let capL = captureLang(n, p, g, atStart, marked = true)
          check setL.ok and capL.ok
          if not (setL.ok and capL.ok): continue
          for u in words(nlAlpha, 3):
            let (e, caps) = chosenCaps(n, u, atStart)
            let isSet = e >= 0 and caps[g - 1][0] >= 0
            let where = escape(p) & " g" & $g & " " & escape(u)
            if member(setL.re, toSyms(u)) != isSet and bad.len < 10:
              bad.add "set " & where
            for a in 0 .. u.len:
              for b in a .. u.len:
                let w = toSyms(u[0 ..< a]) & @[markSym] & toSyms(u[a ..< b]) &
                        @[markSym2] & toSyms(u[b .. ^1])
                if member(capL.re, w) != (isSet and caps[g - 1] == (a, b)) and
                   bad.len < 10:
                  bad.add "cap " & where & " " & $a & ".." & $b
    echo "  conventions and (*ACCEPT): ", runs, " runs, ", capsChecked,
         " capture runs, ", langs, " languages, ", searches, " searches (",
         seen, " patterns' searches declined), ", lap()
    checkpoint $bad
    check bad.len == 0
    check runs > 100_000
    check searches > 5_000

  test "the CRLF skip is PCRE's optimiser's call where a match starts at LF":
    # The bumpalong skips a CRLF's LF after a failed attempt at its CR, but
    # `[\x09-\x0b]`'s start bits pass over the CR: PCRE tries the LF.
    # Without start bits (an optional prefix before `.`) it does not.
    check "\r\n".find(re"(*CRLF)[\x09-\x0b]\z") == 1
    check "\r\n".find(re"(*CRLF)(?:[\x09-\x0b]\x00)?.") == -1
    check "\r\n".find(re"(*CRLF)(?:\n\x00)?.") == 1   # explicit LF: no skip
    for p in [r"(*CRLF)[\x09-\x0b]\z", r"(*CRLF)(?:[\x09-\x0b]\x00)?.",
              r"(*ANYCRLF)\s?$", r"(*ANY)\v\z"]:
      let n = buildNfa(parsePcre(p))
      checkpoint escape(p)
      check crlfSkipSeen(n)
      check not searchLang(n, p, skFirst, false).ok
    for p in [r"(*CRLF)(?:\n\x00)?.", "(*ANYCRLF).", "(*ANY)a$",
              "(*CRLF)\\Q\r\\E?."]:
      checkpoint escape(p)
      check not crlfSkipSeen(buildNfa(parsePcre(p)))

  test "the Z3 formulas route every entry through the automaton":
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    var bad: seq[string]
    var checked, declined, declinedSeen = 0
    for p in ["(*CR)a$", "(*CRLF).", "(*ANYCRLF)a\\r?$", "(*ANY).*\\Z",
              "a(?:(*ACCEPT)|b)", "(*CRLF)\\n|.", "(*CRLF)\\Q\r\\E?."]:
      let rx = re(p)
      let seen = crlfSkipSeen(buildNfa(parsePcre(p)))
      for subj in words("a\r\n", 2):
        let ctx = newContext()
        setCurrentContext(ctx)
        var cases: seq[(string, int, int)]
        # Each in-range start and -1 (and len + 1 for the empty subject).
        for st in -1 .. subj.len + 1:
          if st == subj.len + 1 and subj.len > 0: continue
          cases.add ("matchLen", st, subj.matchLen(rx, st))
          cases.add ("findBoundsLast", st, subj.findBounds(rx, st).last)
          cases.add ("find", st, subj.find(rx, st))
          cases.add ("match", st, int(subj.match(rx, st)))
        cases.add ("endsWith", 0, int(subj.endsWith(rx)))
        cases.add ("startsWith", 0, int(subj.startsWith(rx)))
        for (name, st, real) in cases:
          let sp = RegexSpec(entry: name, flag: "re", pattern: p)
          let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj),
                                  mkInt(st), fresh)
          if seen and name in ["find", "findBoundsLast"]:
            # The occurrence search declines (`crlfSkipSeen`).
            if r.outcome == roUnmodelled: inc declinedSeen
            else: inc declined
            continue
          if r.outcome != roValue:
            inc declined
            continue
          inc checked
          let sol = newSolver(ctx)
          let prm = newParams(ctx)
          prm.set("timeout", 10000)
          sol.setParams(prm)
          for d in r.defs: sol.add d
          if name in ["endsWith", "match", "startsWith"]:
            sol.add(if real == 1: not r.b else: r.b)
          else:
            sol.add r.i != mkInt(real)
          if $sol.check() != "zsUnsat" and bad.len < 10:
            bad.add escape(p) & " " & escape(subj) & " " & name & "(" & $st &
                    ") real " & $real
    echo "  convention Z3 formulas: ", checked, " cases (", declinedSeen,
         " searches declined), ", lap()
    checkpoint $bad
    check bad.len == 0
    check declined == 0
    check declinedSeen > 0
    check checked > 500
