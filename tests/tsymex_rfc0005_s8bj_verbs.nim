## RFC-0005 S8bj -- the concrete reference of the regex lowerings
## (`pcre_select.pcreExec` / `pcreReplace`: the agenda attempt and PCRE's
## bumpalong loop with its start-of-match optimiser) against the real
## `std/re`, on the backtracking verbs, the marks, the newline conventions'
## CRLF start skip, `(*NO_START_OPT)` and `(*LIMIT_..=0)`.
##
## For every pattern of a generated corpus and every subject over
## {a, b, CR, LF} up to length 3, at every start offset: `find`,
## `matchLen` and `findBounds`' `last` (and once per subject `replace`)
## must equal the reference's.
##
## The engine matters (see `pcre_engine`): under a JIT-enabled libpcre the
## unanchored entries of the patterns the walker declines there
## (`jitDeclined`) are not compared; the anchored ones (never the JIT's,
## std/re passes PCRE_ANCHORED) are.
import std/[unittest, strutils, re, times]
import pcre
import nelli/smt/[pcre_syntax, pcre_select]

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

proc jitEngine(): bool =
  var v: cint
  discard pcre.config(pcre.CONFIG_JIT, addr v)
  v == 1

type Tally = object
  patterns, calls, skippedJit, declined: int
  bad: seq[string]

proc check1(p: string; subjects: seq[string]; jit: bool; t: var Tally) =
  let pr = parsePcre(p)
  if pr.status != psOk: return
  let n = buildNfa(pr)
  if not n.ok:
    inc t.declined
    return
  if limitEffect(n)[0] == leUnknown:
    inc t.declined
    return
  let rx = re(p)
  inc t.patterns
  let unanch = not (jit and jitDeclined(n).len > 0)
  if not unanch: inc t.skippedJit
  for s in subjects:
    for st in 0 .. s.len:
      inc t.calls
      let (rc, a, b) = pcreExec(n, s, st, false)
      let (rcA, _, bA) = pcreExec(n, s, st, true)
      let wantLen = matchLen(s, rx, st)
      let gotLen = (if rcA == 1: bA - st else: rcA)
      if gotLen != wantLen:
        t.bad.add escape(p) & " matchLen(" & escape(s) & ", " & $st &
                  ") = " & $gotLen & ", re: " & $wantLen
      if not unanch: continue
      let wantFind = find(s, rx, st)
      let gotFind = (if rc == 1: a else: rc)
      if gotFind != wantFind:
        t.bad.add escape(p) & " find(" & escape(s) & ", " & $st & ") = " &
                  $gotFind & ", re: " & $wantFind
      let wantLast = findBounds(s, rx, st).last
      let gotLast = (if rc == 1: b - 1 else: 0)
      if gotLast != wantLast:
        t.bad.add escape(p) & " findBounds(" & escape(s) & ", " & $st &
                  ").last = " & $gotLast & ", re: " & $wantLast
    if unanch:
      let want = replace(s, rx, "-")
      let got = pcreReplace(n, s, "-")
      if got != want:
        t.bad.add escape(p) & " replace(" & escape(s) & ") = " & escape(got) &
                  ", re: " & escape(want)

const
  conventions = ["", "(*CRLF)", "(*ANYCRLF)", "(*ANY)", "(*CR)"]
  verbs = ["(*COMMIT)", "(*PRUNE)", "(*SKIP)", "(*THEN)", "(*MARK:A)",
           "(*SKIP:A)", "(*PRUNE:A)", "(*THEN:A)", "(*ACCEPT)", "(*F)"]
  items = ["a", "b", "a*", "a+", "a?", "x?", ".", "[ab]", "\\s", "\\r",
           "\\n", "(?:a|ab)", "(?:ab|a)", "(?:a|b)*", "b*", "$", "^", "\\z",
           "\\Z", "(?m)^", "(?m)$"]

proc corpus(): seq[string] =
  ## Two items and a verb (every placement), under each convention, with
  ## and without the start optimiser; sampled by a fixed stride.
  var all: seq[string]
  for cv in conventions:
    for nso in ["", "(*NO_START_OPT)"]:
      for v in verbs:
        for x in items:
          for y in items:
            all.add cv & nso & v & x & y
            all.add cv & nso & x & v & y
            all.add cv & nso & x & y & v
  var k = 0
  for p in all:
    inc k
    if k mod 199 == 0: result.add p

const thenCases = [
  # THEN caught by the innermost group with two or more alternatives whose
  # current branch holds it; frames outliving their group.
  "(?:a(*THEN)b|ab)", "(?:a(*THEN)b|a)c", "a(?:b(*THEN)c|bd)|abd",
  "(?:a(?:b(*THEN)x|c)|ab)", "(?:a(?:b(*THEN)x)|ab)", "(?:(?:a)(*THEN)b|ab)",
  "(?:a|b)(*THEN)c|.b", "(?:a(*THEN)|b)+c", "(?:a(*THEN)|b)*c|ab",
  "(?:(a)(*THEN)b|a)", "(?:a(*THEN)b|a|ab)", "(?:a(?:(*THEN)b|c)|ab)",
  "(a(*THEN)b|ab){2}", "(?:a(*THEN)b|a){2}", "(?:a(*THEN)b|a)?ab",
  "(?:a(*THEN)(?:b|c)|a.)", "a+(*THEN)b|aab", "(?:a+(*THEN)b|a)",
  "(?:a(*SKIP)b|a)|.", "a(*SKIP)b|.", "aa(*SKIP)b|a+", "(*MARK:A)a(*SKIP:A)b|.",
  "a(*MARK:A)a(*SKIP:A)b|.", "(?:a(*MARK:A)|b)a(*SKIP:A)b|.",
  "a(*SKIP:B)b|.", "(?:a(*SKIP:B)b|ab)", "(*SKIP:B)a|a", "a(*COMMIT)b|.",
  "(?:a(*COMMIT)b|a)", "(*COMMIT)a|b", "a(*PRUNE)b|.", "(?:a(*PRUNE)b|ab)",
  "(*LIMIT_MATCH=0)a", "(*LIMIT_RECURSION=0)a", "(*LIMIT_MATCH=0)(*COMMIT)",
  "(*LIMIT_MATCH=0)ab", "(*LIMIT_MATCH=0)a.*b", "(*LIMIT_RECURSION=0)^a",
  "(*LIMIT_MATCH=0)(?i)b", "(*LIMIT_MATCH=0)[ab]a", "(*LIMIT_MATCH=0)x?",
  "(*LIMIT_MATCH=10000000)a(*SKIP)b|.", "(*CRLF)\\s(*SKIP)b",
  "(*CRLF)(?:\\r|\\n)?(*COMMIT)a", "(*ANYCRLF)(*COMMIT)\\s", "(*ANY)$(*SKIP)",
  "(*CRLF)(?m)^a", "(*ANYCRLF)(?m)^", "(*CR)(?m)$\\r", "(*CRLF)(?m)$",
  "(*ANY)(?m)^.", "(*CRLF).\\n", "(*CRLF)(?s).\\n"]

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

suite "S8bj: the concrete reference against std/re":

  test "verbs, marks and the newline conventions (sampled corpus)":
    let jit = jitEngine()
    var t: Tally
    let subjects = words("ab\r\n", 3)
    for p in corpus(): check1(p, subjects, jit, t)
    echo "  engine jit=", jit, ": ", t.patterns, " patterns, ", t.calls,
         " calls, ", t.skippedJit, " unanchored-skipped, ", t.declined,
         " declined, ", t.bad.len, " differ, ", lap()
    checkpoint t.bad[0 ..< min(t.bad.len, 30)].join("\n")
    check t.bad.len == 0
    check t.patterns >= 600

  test "THEN's catcher, SKIP's landings, COMMIT, LIMIT=0, (?m)":
    let jit = jitEngine()
    var t: Tally
    let subjects = words("ab\r\n", 3)
    for cv in conventions:
      for p in thenCases: check1(cv & p, subjects, jit, t)
    echo "  engine jit=", jit, ": ", t.patterns, " patterns, ", t.calls,
         " calls, ", t.skippedJit, " unanchored-skipped, ", t.bad.len, " differ, ", lap()
    checkpoint t.bad[0 ..< min(t.bad.len, 30)].join("\n")
    check t.bad.len == 0
    check t.patterns >= 250
