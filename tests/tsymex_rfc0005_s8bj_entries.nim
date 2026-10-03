## RFC-0005 S8bj -- the Z3 formulas of every `std/re` entry point
## (`regex_parser.lowerRegexEntry`) for the verbs and the limit start options, against the real
## `std/re`: on every subject up to 2
## bytes over {a, b, CR, LF} (3 bytes over {a, 0xC3, 0xA9} in UTF mode,
## invalid UTF-8 included) at every start (-1 and one past the end too),
## std/re's value is the formula's only value.
##
## Under a JIT-enabled libpcre the unanchored entries of the patterns the
## walker declines there (`jitDeclined`) must decline (`roUnmodelled`).
import std/[unittest, strutils, re, times]
import pcre
import z3
import nelli/smt/[pcre_syntax, pcre_select, regex_parser]

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

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

const unanchoredEntries = ["find", "contains", "findBoundsFirst",
                           "findBoundsFirstCap", "findBoundsLast"]

type Tally = object
  checked, declinedJit: int
  bad: seq[string]

proc checkPattern(p, alpha: string; maxLen: int; t: var Tally) =
  var ctr = 0
  proc fresh(tag: string): string =
    inc ctr
    tag & "#" & $ctr
  let rx = re(p)
  let n = buildNfa(parsePcre(p))
  let jitOut = jitEngine() and jitDeclined(n).len > 0
  for subj in words(alpha, maxLen):
    let ctx = newContext()
    setCurrentContext(ctx)
    var cases: seq[(string, int, int)]
    for st in -1 .. subj.len + 1:
      cases.add ("matchLen", st, subj.matchLen(rx, st))
      cases.add ("match", st, int(subj.match(rx, st)))
      cases.add ("find", st, subj.find(rx, st))
      cases.add ("contains", st, int(subj.contains(rx, st)))
      cases.add ("findBoundsFirst", st, subj.findBounds(rx, st).first)
      cases.add ("findBoundsLast", st, subj.findBounds(rx, st).last)
      var m: array[0, tuple[first, last: int]]
      cases.add ("findBoundsFirstCap", st, subj.findBounds(rx, m, st).first)
    cases.add ("endsWith", 0, int(subj.endsWith(rx)))
    cases.add ("startsWith", 0, int(subj.startsWith(rx)))
    for (name, st, real) in cases:
      let sp = RegexSpec(entry: name, flag: "re", pattern: p)
      let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj), mkInt(st),
                              fresh)
      let where = escape(p) & " " & escape(subj) & " " & name & "(" & $st &
                  ") real " & $real
      if jitOut and name in unanchoredEntries:
        inc t.declinedJit
        if r.outcome != roUnmodelled: t.bad.add "not declined: " & where
        continue
      if r.outcome != roValue:
        t.bad.add $r.outcome & " " & r.msg & ": " & where
        continue
      inc t.checked
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
      if res != "zsUnsat": t.bad.add res & " " & where
    if t.bad.len > 20: return

suite "S8bj: the entry points' formulas against std/re":

  test "the verbs and the limit start options":
    var t: Tally
    for p in ["a(*COMMIT)b|.", "a(*SKIP)b|.", "(?:a(*THEN)b|ab)",
              "a(*MARK:A)a(*SKIP:A)b|.", "(*CRLF)\\s(*SKIP)b",
              "(*LIMIT_MATCH=0)a", "(*LIMIT_RECURSION=0)[ab]b"]:
      checkPattern(p, "ab\r\n", 2, t)
    echo "  verbs and limits: ", t.checked, " cases, ", t.declinedJit,
         " JIT-declined, ", lap()
    checkpoint t.bad.join("\n")
    check t.bad.len == 0
    check t.checked > 1_000
