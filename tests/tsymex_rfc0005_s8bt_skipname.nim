## RFC-0005 S8bt (item 4) -- mixed (*SKIP:NAME): a SKIP:NAME whose MARK only
## some paths pass, one with no MARK beside one with a MARK, and either
## beside a plain (*SKIP), against the real std/re (pcre_exec.c's
## `ignore_skip_arg`: a SKIP:NAME with no MARK re-runs the attempt ignoring
## every SKIP:NAME executed so far, found ones included; the count survives
## a SKIP's jump into the next attempt, and the re-run takes the CRLF start
## skip). S8bj declined these (`classifySkipNames`).
##
## The concrete reference (`pcreExec` / `pcreReplace`) on every subject
## over {a, b, CR, LF} up to length 3 at every start: `matchLen` on the
## interpreter, and the unanchored entries on the engine std/re runs them
## on (`pcre_engine.pcreSearchEngine`).
import std/[unittest, strutils, re, times]
import nelli/smt/[pcre_syntax, pcre_select, pcre_engine]
import ./s8bt_harness/jit_corpus

proc skipCorpus*(): seq[string] =
  ## Two alternatives of a head and a tail (three with a final `.`), under
  ## three conventions; then nested and repeated shapes.
  const heads = ["a", "(*MARK:A)a", "a(*MARK:A)", "(?:(*MARK:A)a|b)",
                 "(?:a|(*MARK:A)b)"]
  const tails = ["(*SKIP:A)b", "(*SKIP:B)b", "(*SKIP)b", "b"]
  for cv in ["", "(*CRLF)", "(*ANYCRLF)"]:
    for h1 in heads:
      for t1 in tails:
        for h2 in heads:
          for t2 in tails:
            let p = cv & h1 & t1 & "|" & h2 & t2
            if "SKIP:" notin p: continue
            result.add p
            if "(*SKIP)" in p or "SKIP:B" in p: result.add p & "|."
  for p in ["(*MARK:A)a(*SKIP:B)(?:b(*SKIP:A)a|.)",
            "a(*SKIP:B)(?:(*MARK:A)b(*SKIP:A)a|.)|b",
            "(?:(*MARK:A)a|a)(*SKIP:A)(?:b(*SKIP:B)|a)|.",
            "(?:a(*SKIP:B)|(*MARK:A)b)+(*SKIP:A)a|.",
            "(?:(*MARK:A)a(*SKIP:B)b|a(*SKIP:A))*b|.",
            "a+(*SKIP:B)b|(*MARK:A)a(*SKIP:A)a|a",
            "(*CRLF)\\s(*SKIP:B)a|(*MARK:A)\\s(*SKIP:A)b|\\s",
            "(*CRLF)[\\x09-\\x0b](*SKIP:B)a|[\\x09-\\x0b]",
            "(*ANYCRLF)(?:\\s(*SKIP:B)a|(*MARK:A).(*SKIP:A)b)|.",
            "(*CRLF)(*MARK:A)\\s(*SKIP:B)b(*SKIP:A)|(*SKIP)\\s",
            # The count a SKIP's jump keeps: the next attempt ignores its
            # first SKIP:NAME (std/re finds 3 in "abbc").
            "bc(*MARK:A)(*SKIP:A)x|a(*SKIP:B)y|ab(*SKIP)q|c",
            "b(*MARK:A)(*SKIP:A)x|a(*SKIP:B)y|a(*SKIP)q|b",
            "a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x|.",
            "(?:a(*SKIP:B)y|ab(*SKIP)q|b(*MARK:A)(*SKIP:A)x)+|c",
            "(*CRLF)\\s(*SKIP:B)y|\\sb(*MARK:A)(*SKIP:A)x|b"]:
    result.add p

type Tally = object
  patterns, calls, declined, unmodelled, unmodelledPats: int
  bad: seq[string]
  why: seq[string]

proc check1(p: string; subjects: seq[string]; t: var Tally) =
  let pr = parsePcre(p)
  doAssert pr.status == psOk, p
  let n = buildNfa(pr)
  let nu = buildNfa(pr, pcreSearchEngine())
  if not (n.ok and nu.ok):
    inc t.declined
    if t.why.len < 10: t.why.add escape(p) & ": " & n.why & nu.why
    return
  let rx = re(p)
  inc t.patterns
  let u0 = t.unmodelled
  defer:
    if t.unmodelled > u0: inc t.unmodelledPats
  for s in subjects:
    for st in 0 .. s.len:
      inc t.calls
      let (rcA, _, bA) = pcreExec(n, s, st, true)
      let gotLen = (if rcA == 1: bA - st else: rcA)
      let wantLen = matchLen(s, rx, st)
      if gotLen != wantLen:
        t.bad.add escape(p) & " matchLen(" & escape(s) & ", " & $st &
                  ") = " & $gotLen & ", re: " & $wantLen
      let (rc, a, b) = pcreExec(nu, s, st, false)
      if rc == pcreUnmodelled:
        inc t.unmodelled
        continue
      let got = (if rc == 1: (a, b - 1) elif rc == -1: (-1, 0) else: (rc, 0))
      let want = (find(s, rx, st), findBounds(s, rx, st).last)
      if got != want:
        t.bad.add escape(p) & " find/last(" & escape(s) & ", " & $st &
                  ") = " & $got & ", re: " & $want
    if pr.groups > 0:
      # The found attempt's groups (its count kept from the attempt
      # before: `pcreExecIgn`).
      for st in 0 .. s.len:
        var bs: array[3, tuple[first, last: int]]
        for i in 0 ..< bs.len: bs[i] = (first: -9, last: -9)
        let r = findBounds(s, rx, bs, st)
        let ((rc, a, _), ign) = pcreExecIgn(nu, s, st, false)
        if rc == pcreUnmodelled: continue
        var got = @[(-9, -9), (-9, -9), (-9, -9)]
        if rc == 1:
          let (_, cs) = chosenCapsAt(nu, s, a, st, false, ign)
          var hi = 0
          for i in 1 .. cs.len:
            if cs[i - 1][0] >= 0: hi = i
          for i in 1 .. min(hi, 3):
            got[i - 1] = (if cs[i - 1][0] < 0: (-1, 0)
                          else: (cs[i - 1][0], cs[i - 1][1] - 1))
        var want: seq[(int, int)]
        for x in bs: want.add (x.first, x.last)
        if r.first >= 0 and got != want:
          t.bad.add escape(p) & " captures(" & escape(s) & ", " & $st &
                    ") = " & $got & ", re: " & $want
    let wantR = replace(s, rx, "-")
    var unm = false
    let gotR = pcreReplace(nu, s, "-", unm)
    if not unm and gotR != wantR:
      t.bad.add escape(p) & " replace(" & escape(s) & ") = " & escape(gotR) &
                ", re: " & escape(wantR)

proc staleCorpus*(): seq[string] =
  ## The count a SKIP's jump keeps (`ignore_skip_arg`): three alternatives
  ## from a SKIP:NAME without its MARK, a SKIP, and SKIP:NAMEs with their
  ## MARK, in every order.
  const alts = ["bc(*MARK:A)(*SKIP:A)x", "a(*SKIP:B)y", "ab(*SKIP)q", "c",
                "b(*MARK:A)(*SKIP:A)x", "a(*SKIP)q", "b", "(*SKIP:B)a"]
  for a in alts:
    for b in alts:
      if b == a: continue
      for c in alts:
        if c == a or c == b: continue
        let p = a & "|" & b & "|" & c
        if "SKIP:B" in p and ("MARK" in p or "(*SKIP)" in p):
          result.add p
          # Every fourth with its alternatives as groups.
          if result.len mod 8 == 1:
            result.add "(" & a & ")|(" & b & ")|(" & c & ")"

# The patterns are split four ways between this file and its `_b` .. `_d`
# twins (which include this one with `s8btSkipPart = 1` .. `3`), so each
# runs under 60 s on the Windows legs; the stale-count family is `_e`'s.
when not declared(s8btSkipPart):
  const s8btSkipPart = 0

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

suite "S8bt: mixed (*SKIP:NAME), concretely (part " & $s8btSkipPart & ")":

  test "every shape, every subject, every start":
    var t: Tally
    if s8btSkipPart == 4:
      let subjects = words("abc", 4)
      for p in staleCorpus(): check1(p, subjects, t)
    else:
      let subjects = words("ab\r\n", 3)
      for i, p in skipCorpus():
        if i mod 4 == s8btSkipPart: check1(p, subjects, t)
    echo "  ", t.patterns, " patterns, ", t.calls, " calls, ", t.declined,
         " declined, ", t.unmodelled, " calls unmodelled (",
         t.unmodelledPats, " patterns), ", t.bad.len, " differ, ", lap()
    checkpoint t.why.join("\n")
    checkpoint t.bad[0 ..< min(t.bad.len, 30)].join("\n")
    check t.declined == 0
    check t.unmodelled == 0
    check t.bad.len == 0
    check t.patterns >= (if s8btSkipPart == 4: 150 else: 390)
