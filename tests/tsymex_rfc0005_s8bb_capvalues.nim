## RFC-0005 S8bb item 5 -- the captures overloads' written elements against
## the concrete `std/re`: for every call that reports a match (`match`,
## `matchLen`, `find`, `contains`, `findBounds` and its bounds overload),
## every start (a bad offset too), a short and a full `matches` array, the
## Z3 value of each group element `regex_parser.lowerRegexEntry` builds is
## the concrete call's ONLY solution.
## Split from `tsymex_rfc0005_s8bb_constructs.nim` (RFC-0005 S8bb item 8) to
## keep each suite inside the per-backend runtime budget.
## `-d:nelliRegexExhaustive` widens every subject length by one (minutes,
## not for CI).
import std/[unittest, strutils, re, times]
import z3
import nelli/smt/regex_parser
import nelli/smt/pcre_syntax

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

suite "S8bb (5): the captures overloads' writes, against std/re":

  test "the Z3 value of each written element is std/re's":
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    var bad: seq[string]
    var checked, declined = 0
    for p in ["(a)|(b)", "((a)|b)+", "(^a|b)(\n)?"]:
      let pr = parsePcre(p)
      let rx = re(p)
      # LF matters only to the pattern that reads it.
      for subj in words((if '\n' in p: "ab\n" else: "ab"), 2 + widen):
        # A context per subject, and a timeout per query: a query Z3 leaves
        # undecided fails the check instead of hanging the suite.
        let ctx = newContext()
        setCurrentContext(ctx)
        for st in [-1, 0, 1, subj.len + 1]:
          if st == 1 and subj.len == 0: continue
          # A bad offset writes nothing: one array length covers it.
          if st notin 0 .. subj.len and subj.len > 1: continue
          # A short array (1) at the first start only.
          for m in (if st == 0: @[1, pr.groups] else: @[pr.groups]):
            # `matchLen` shares `match`'s lowering, `contains` `find`'s: at the
            # first start only.
            for call in (if st == 0: @["match", "matchLen", "find", "contains",
                                       "findBounds"]
                         else: @["match", "find", "findBounds"]):
              var arr = newSeq[string](m)
              for i in 0 ..< m: arr[i] = "o" & $i
              var bnd = newSeq[tuple[first, last: int]](m)
              for i in 0 ..< m: bnd[i] = (first: 7 + i, last: 9 + i)
              case call
              of "match": discard subj.match(rx, arr, st)
              of "matchLen": discard subj.matchLen(rx, arr, st)
              of "find": discard subj.find(rx, arr, st)
              of "contains": discard subj.contains(rx, arr, st)
              else:
                discard subj.findBounds(rx, arr, st)
                discard subj.findBounds(rx, bnd, st)
              for g in 1 .. min(m, pr.groups):
                var kinds = @["capture"]
                if call == "findBounds": kinds.add ["captureFirst", "captureLast"]
                for k in kinds:
                  let sp = RegexSpec(entry: k & "|" & call & "|" & $g,
                                     flag: "re", pattern: p)
                  let oldS = "o" & $(g - 1)
                  let oldI = (if k == "captureFirst": 7 + g - 1 else: 9 + g - 1)
                  let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj),
                                          mkInt(st), fresh, mkInt(m),
                                          mkString(oldS), mkInt(oldI))
                  if r.outcome != roValue:
                    inc declined
                    continue
                  inc checked
                  let sol = newSolver(ctx)
                  let prm = newParams(ctx)
                  prm.set("timeout", 10000)
                  sol.setParams(prm)
                  for d in r.defs: sol.add d
                  case k
                  of "capture": sol.add r.s != mkString(arr[g - 1])
                  of "captureFirst": sol.add r.i != mkInt(bnd[g - 1].first)
                  else: sol.add r.i != mkInt(bnd[g - 1].last)
                  if $sol.check() != "zsUnsat" and bad.len < 10:
                    bad.add escape(p) & " " & escape(subj) & " " & k & " " &
                            call & "(" & $st & ") m " & $m & " g " & $g
    echo "  capture Z3 values: ", checked, " cases, ", lap()
    checkpoint $bad
    check bad.len == 0
    check declined == 0
    check checked > 600
