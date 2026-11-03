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
##
## RFC-0005 S8cm: part 2 of 2 of this suite, with
## `tsymex_rfc0005_s8bb_selection`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 62 s).

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

suite "S8bb (3): PCRE's match selection against the concrete std/re":
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
