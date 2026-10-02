## RFC-0005 S8bb item 5 -- the check behind the
## `tsymex_rfc0005_s8bb_capvalues*` suites (one pattern per suite, RFC-0005
## S8bb item 8: one suite over all three ran 93 s on the Windows leg). For
## every call that reports a match (`match`, `matchLen`, `find`, `contains`,
## `findBounds` and its bounds overload), every start (a bad offset too), a
## short and a full `matches` array, the Z3 value of each group element
## `regex_parser.lowerRegexEntry` builds must be the concrete `std/re`
## call's ONLY solution. Not a test itself (no `t` prefix).
## `-d:nelliRegexExhaustive` widens every subject length by one (minutes,
## not for CI).
import std/[strutils, re]
import z3
import nelli/smt/regex_parser
import nelli/smt/pcre_syntax

const widen = (when defined(nelliRegexExhaustive): 1 else: 0)

proc words(alpha: string; maxLen: int): seq[string] =
  result = @[""]
  var frontier = @[""]
  for _ in 1 .. maxLen:
    var next: seq[string]
    for w in frontier:
      for c in alpha: next.add w & c
    result.add next
    frontier = next

proc capValues*(p: string): tuple[checked, declined: int; bad: seq[string]] =
  ## Each query that is not `unsat` (a wrong value, or undecided within its
  ## 10 s timeout) is listed in `bad` (the first ten).
  var ctr = 0
  proc fresh(tag: string): string =
    inc ctr
    tag & "#" & $ctr
  let pr = parsePcre(p)
  let rx = re(p)
  # LF matters only to the pattern that reads it.
  for subj in words((if '\n' in p: "ab\n" else: "ab"), 2 + widen):
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
              # A context per query (and fresh names from 1), and a
              # timeout per query: a query Z3 leaves undecided fails the
              # check instead of hanging the suite. RFC-0005 S8bb: in a
              # context shared by a subject's queries, Z3 4.13.4 left
              # `(a)|(b)` "ab" captureFirst findBounds(0) m 2 g 1
              # unknown at 10 s (Linux and the Windows leg); alone it is
              # unsat in about a second.
              let ctx = newContext()
              setCurrentContext(ctx)
              ctr = 0
              let oldS = "o" & $(g - 1)
              let oldI = (if k == "captureFirst": 7 + g - 1 else: 9 + g - 1)
              let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj),
                                      mkInt(st), fresh, mkInt(m),
                                      mkString(oldS), mkInt(oldI))
              if r.outcome != roValue:
                inc result.declined
                continue
              inc result.checked
              let sol = newSolver(ctx)
              let prm = newParams(ctx)
              prm.set("timeout", 10000)
              sol.setParams(prm)
              for d in r.defs: sol.add d
              case k
              of "capture": sol.add r.s != mkString(arr[g - 1])
              of "captureFirst": sol.add r.i != mkInt(bnd[g - 1].first)
              else: sol.add r.i != mkInt(bnd[g - 1].last)
              if $sol.check() != "zsUnsat" and result.bad.len < 10:
                result.bad.add escape(p) & " " & escape(subj) & " " & k & " " &
                        call & "(" & $st & ") m " & $m & " g " & $g
