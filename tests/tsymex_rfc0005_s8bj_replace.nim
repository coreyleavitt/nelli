## RFC-0005 S8bj -- `replace(s, re, by)` for the patterns S8bb's run does
## not read (a verb, a `(?m)` anchor, UTF mode, an observable CRLF start
## skip), against the real `std/re`:
##   * the agenda's step table (`pcre_select.stepTable`), read by a direct
##     interpreter of its leaves and registers inside pcre_exec.c's loop,
##     is Nim's `replace` on every subject up to 4 bytes over a, b, CR, LF;
##   * the Z3 term (`regex_parser.replaceStepZ3`) has std/re's value as its
##     only value on every subject up to 3 bytes.
## Under a JIT-enabled libpcre the patterns the walker declines there
## (`jitDeclined`) are not compared.
import std/[unittest, strutils, re, times, tables]
import pcre
import z3
import nelli/smt/[pcre_syntax, pcre_select, regex_parser]

proc jitEngine(): bool =
  var v: cint
  discard pcre.config(pcre.CONFIG_JIT, addr v)
  v == 1

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

proc finalNl(n: Nfa; s: string; j: int): bool =
  let rest = s.len - j
  (rest == 1 and s[j] in nlBytes(n.nl)) or
    (nlPair(n.nl) and rest == 2 and s[j] == '\r' and s[j + 1] == '\n')

proc runRef(n: Nfa; t: StepTable; s: string; x, st0: int): (LeafKind, int) =
  ## The table's attempt at `x`: its outcome and position.
  var st = st0
  var regs: seq[int]
  for j in x .. s.len:
    let row = t.rows[st]
    let lf =
      if j == s.len: row.atEnd
      elif finalNl(n, s, j): row.nll[ord(s[j])]
      else: row.other[ord(s[j])]
    case lf.kind
    of lfNext:
      var nr: seq[int]
      for m in lf.regMap: nr.add(if m < 0: j else: regs[m])
      regs = nr
      st = lf.next
    of lfMatch, lfSkip:
      return (lf.kind, (if lf.reg < 0: j else: regs[lf.reg]))
    else:
      return (lf.kind, 0)
  raiseAssert "runRef: no leaf at the end"

proc execRef(n: Nfa; t: StepTable; s: string; start: int; ne: bool): (int, int) =
  ## pcre_exec.c's loop over the table's attempts.
  var x = start
  while true:
    while not created(n, s, x, start): inc x
    let pc = canonPc0(n, classAt(s, x))
    let elig = n.hasNeverSkip and x > start and x < s.len and
               s[x - 1] == '\r' and s[x] == '\n' and n.skipActive
    let (k, pos) = runRef(n, t, s, x, t.start[(pc, ne and x == start, elig)])
    var next: int
    case k
    of lfMatch: return (x, pos)
    of lfCommit: return (-1, 0)
    of lfSkip: next = (if pos > x: pos else: x + 1)
    else: next = x + 1
    if n.utf:
      while next < s.len and (ord(s[next]) and 0xC0) == 0x80: inc next
    if n.anchoredPat or next > s.len: return (-1, 0)
    x = next
    if x > start and s[x - 1] == '\r' and x < s.len and s[x] == '\n' and
       n.skipActive:
      inc x

proc replaceRef(n: Nfa; t: StepTable; s, by: string): string =
  var prev = 0
  var ne = false
  while prev < s.len:
    let (a, b) = execRef(n, t, s, prev, ne)
    ne = false
    if a < 0: break
    result.add s[prev ..< a]
    result.add by
    if a == b: ne = true
    prev = b
  result.add s[min(prev, s.len) .. ^1]

const repPatterns = [
  "a(*COMMIT)b|.", "(*COMMIT)a|b", "a+(*COMMIT)b|a", "a(*PRUNE)b|.",
  "a(*SKIP)b|.", "aa(*SKIP)b|a+", "a+(*SKIP)b|.|", "(*MARK:A)a(*SKIP:A)b|.",
  "a(*MARK:A)a(*SKIP:A)b|.", "a(*SKIP:B)b|.", "(?:a(*THEN)b|ab)",
  "(?:a(*THEN)b|a)b?", "(?:a(*THEN)|b)+c|a", "x?(*COMMIT)a|", "(*PRUNE)a?",
  "(?m)^", "(?m)$", "(?m)^a|b$", "(*CRLF)(?m)$", "(*CRLF)(?m)^",
  "(*ANYCRLF)(?m)^.?", "(*CR)(?m)$", "(*ANY)(?m)^\\s?",
  "(*CRLF)\\s?", "(*CRLF)a*", "(*ANYCRLF)\\s?$", "(*ANY)\\v?",
  "(*CRLF)[\\x09-\\x0b]\\z", "(*CRLF)\\s(*SKIP)b", "(*NO_START_OPT)a(*COMMIT)b|.",
  "(*CRLF)(*COMMIT)\\s|b", "(*LIMIT_MATCH=0)a"]

suite "S8bj: replace by the agenda's step table, against std/re":

  test "the table, read directly, is Nim's replace":
    let jit = jitEngine()
    var runs, skipped = 0
    var bad: seq[string]
    for p in repPatterns:
      let pr = parsePcre(p)
      check pr.status == psOk
      let n = buildNfa(pr)
      check n.ok
      if jit and jitDeclined(n).len > 0:
        inc skipped
        continue
      if limitEffect(n)[0] != leNone: continue   # the walker's own rule
      let t = stepTable(n)
      checkpoint escape(p) & " " & t.why
      check t.ok
      if not t.ok: continue
      let rx = re(p)
      for subj in words("ab\r\n", 4):
        inc runs
        let want = subj.replace(rx, "-")
        let got = replaceRef(n, t, subj, "-")
        if got != want and bad.len < 20:
          bad.add escape(p) & " " & escape(subj) & " got " & escape(got) &
                  " want " & escape(want)
    echo "  step-table replace runs: ", runs, " (", skipped, " JIT-declined)"
    checkpoint bad.join("\n")
    check bad.len == 0
    check runs > 5_000

  test "the Z3 term's only value is Nim's replace":
    let jit = jitEngine()
    var checked = 0
    var bad: seq[string]
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    for p in repPatterns:
      let pr = parsePcre(p)
      let n = buildNfa(pr)
      if (jit and jitDeclined(n).len > 0) or limitEffect(n)[0] != leNone:
        continue
      let t = stepTable(n)
      if not t.ok: continue
      let t0 = epochTime()
      let rx = re(p)
      let ctx = newContext()
      setCurrentContext(ctx)
      let sv = mkStringVar("s")
      let r = replaceStepZ3(sv, mkString("-"), n, t, fresh)
      for subj in words("ab\r\n", 3):
        inc checked
        let sol = newSolver(ctx)
        let prm = newParams(ctx)
        prm.set("timeout", 10000)
        sol.setParams(prm)
        sol.add sv == mkString(subj)
        sol.add r != mkString(subj.replace(rx, "-"))
        let res = $sol.check()
        if res != "zsUnsat" and bad.len < 20:
          bad.add escape(p) & " " & escape(subj) & " " & res
      if epochTime() - t0 > 1.0:
        echo "    ", escape(p), " ", formatFloat(epochTime() - t0, ffDecimal, 1)
    echo "  step-table replace Z3 values: ", checked, " cases"
    checkpoint bad.join("\n")
    check bad.len == 0
    check checked > 1_000
