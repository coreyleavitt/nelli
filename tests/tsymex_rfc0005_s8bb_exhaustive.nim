## RFC-0005 S8bb -- the membership entry points against the concrete
## `std/re`, exhaustively over short subjects.
##
## Moved out of `tsymex_rfc0005_s8ay_remainder.nim` unchanged in coverage
## (S8ay's suite took 65-130 s against a 60 s per-backend target; RFC-0005
## S8bb item 8). PCRE's match selection is
## `tsymex_rfc0005_s8bb_selection.nim`. `-d:nelliRegexExhaustive` widens
## the subject length by one (minutes, not for CI).
import std/[unittest, strutils, re, times]
import z3
import nelli/smt/regex_parser

const widen = (when defined(nelliRegexExhaustive): 1 else: 0)

var t0 = epochTime()
proc lap(): string =
  let t = epochTime()
  result = formatFloat(t - t0, ffDecimal, 1) & " s"
  t0 = t

# ---- the membership entries, exhaustively (S8aw's "every link is true") -------
#
# `match` / `contains` (every `start` from -1 to len + 1) and `startsWith` /
# `endsWith`, for EVERY subject over {a, b, LF} up to length 4, against the
# concrete `std/re` call. Each formula is built on the ground subject and
# folded by Z3's rewriter; one it does not fold is checked by a solver.
# `endsWith` on a pattern whose PCRE choice is not fixed by the longest
# match (`a|ab`, `a*b`, `(ab)+`) declined in S8ay; RFC-0005 S8bb models
# PCRE's choice, so none declines now. `match` / `contains` / `startsWith`
# never decline on a pattern the reader accepts.

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

const exhPatterns = [("", false), ("a", false), ("b+", false), ("a|ab", false),
  ("a*b", false), (".", false), ("[^a]", false), ("^a", false),
  ("a$", false), ("a\\Z", false), ("a\\z", false), ("\\Aa|b$", false),
  ("(ab)+", false), ("a.b", false), ("\\s", false), ("\\S+$", false),
  ("a b", true), ("a # c\nb", true)]

suite "S8ay (1/2): every membership value is the concrete call's (exhaustive)":

  test "match / contains / startsWith / endsWith over {a, b, LF}, length <= 4":
    let ctx = newContext()
    setCurrentContext(ctx)
    proc fresh(tag: string): string = tag
    var bad: seq[string]
    var checked, folded = 0
    var declinedEnds: seq[string]
    for (p, ext) in exhPatterns:
      let rx = (if ext: rex(p) else: re(p))
      for subj in words("ab\n", 4 + widen):
        var cases: seq[(string, int, bool)]
        for st in -1 .. subj.len + 1:
          cases.add ("match", st, subj.match(rx, st))
          cases.add ("contains", st, subj.contains(rx, st))
        cases.add ("startsWith", 0, subj.startsWith(rx))
        cases.add ("endsWith", 0, subj.endsWith(rx))
        for (name, st, real) in cases:
          let sp = RegexSpec(entry: name, flag: (if ext: "rex" else: "re"),
                             pattern: p)
          let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj),
                                  mkInt(st), fresh)
          if r.outcome == roUnmodelled and name == "endsWith":
            if p notin declinedEnds: declinedEnds.add p
            continue
          if r.outcome != roValue or r.defs.len > 0:
            if bad.len < 10: bad.add "not lowered: " & escape(p) & " " & name
            continue
          inc checked
          let f = $wrap[Z3Bool](ctx, ctx.checkErr Z3_simplify(ctx.raw, r.b.raw))
          var got: bool
          if f == "true" or f == "false":
            inc folded
            got = f == "true"
          else:
            let sol = newSolver(ctx)
            sol.add r.b
            got = $sol.check() == "zsSat"
          if got != real and bad.len < 10:
            bad.add (if ext: "rex " else: "re ") & escape(p) & " " &
                    escape(subj) & " " & name & "(" & $st & ") real " & $real
    echo "  membership: ", checked, " cases, ", lap()
    checkpoint $checked & " cases, " & $folded & " folded; endsWith " &
               "declined on " & $declinedEnds & "; " & $bad
    check bad.len == 0
    check checked > 10_000
    check declinedEnds.len == 0   # RFC-0005 S8bb

  test "the enumeration catches the pre-S8ay lowering (full-string membership)":
    # `match` and `contains` were both `matches(s, R)` before S8ay. Over
    # the same words the enumeration must tell that apart from the real
    # calls, or it could not have caught the bug it guards.
    let ctx = newContext()
    setCurrentContext(ctx)
    var caught = 0
    for p in ["a", "b+", "a.b"]:
      let rx = re(p)
      let full = rxToZ3(parsePcre(p).root)
      for subj in words("ab\n", 3):
        let f = $wrap[Z3Bool](ctx, ctx.checkErr Z3_simplify(ctx.raw,
          matches(mkString(subj), full).raw))
        if (f == "true") != subj.contains(rx) or
           (f == "true") != subj.match(rx):
          inc caught
    checkpoint $caught
    check caught > 0

