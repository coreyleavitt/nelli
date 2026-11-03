## RFC-0005 (soundness channels) slice S8ay -- S8aw's remainder.
##
## Nim's `std/re` entry points each ask PCRE a different question, and the
## walker answered all of them with one: full-string membership of the
## S6a reading of the pattern (`matches(s, R)`), with the `start` argument
## dropped. Wrong verdicts at 04e3a97 (each pinned below, RED first):
##   * `contains(s, R)` is "R occurs somewhere": `"abc".contains(re"b")`
##     was false to the walker -- a false sxSat for `not contains`;
##   * `match(s, R, start)` is "R matches a PREFIX of `s[start..]`" (PCRE's
##     ANCHORED), and true for an out-of-range `start` (`matchLen` returns
##     PCRE_ERROR_BADOFFSET, which is not -1): `"abc".match(re"")` and
##     `"abc".match(re"b", 1)` were false to the walker (false sxSat), and
##     S6b's "match contradiction" pin (`s.len >= 1 and s.match(re"")` is
##     sxUnsat) was itself a false sxUnsat;
##   * `contains(s, R, start)` dropped `start` (a false sxUnsat);
##   * the S6a reading was not PCRE's: `.` matched `\n`, `\D \W \S \n \t`
##     were literal letters, `^ $` literal bytes;
##   * `rex"..."` (extended: whitespace and `#` comments ignored) was read
##     as `re"..."`;
##   * a pattern PCRE rejects (`re"a**"`) never raised the `RegexError` Nim
##     raises at run time -- a handler target was a false sxUnsat;
##   * `matchLen`, `findBounds`, `findAll`, `replacef` and `=~` crashed the
##     compile ("node has no type"); the captures overloads
##     (`match(s, R, matches)`) dropped the `matches` write -- a false
##     sxUnsat for any claim on a capture.
## Item 5: `replace(s, re, by)` over a receiver of unknown length is exact
## past S8aw's 16-byte unroll.
## Item 6: a query only step 1c refutes no longer pays step 1's
## full-theory search first (S8aw's join walk: 10,000,930 units at
## 8b2508f, about 20 s on Z3 5.1; pinned by units, this file's .nim.cfg).
##
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_rfc0005_s8ay_remainder`, `tsymex_rfc0005_s8ay_remainder_b`,
## `tsymex_rfc0005_s8ay_remainder_c`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 94 s).

import std/[unittest, strutils, re]
import z3
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/regex_parser
import nelli/smt/runtime

when not defined(symexQueryStats):
  {.error: "tsymex_rfc0005_s8ay_remainder needs -d:symexQueryStats (its .nim.cfg)".}

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors)
  r

# ---- item 5: exact regex replace past 16 bytes --------------------------------

# Each receiver is longer than the 16-byte unroll S8aw had, so each value
# here is the recursive function (`regexReplaceRec`). The queries are ones
# both Z3 builds decide in seconds; S8ay's measurements list the shapes they
# leave undecided (an unbounded length comparison, a `contains` over the
# result), which are `beSolverUndef`, never a claim.

proc pastUnroll(s: string) =
  if s.len > 20 and s.replace(re"a", "") == "b":
    symexTarget("ay_past_unroll")

proc pastUnrollPair(s: string) =
  if s.len > 20 and s.replace(re"aa", "x") == "xa":
    symexTarget("ay_past_unroll_pair")

proc pastUnrollRun(s: string) =
  if s.len > 20 and s.replace(re"f+", "x") == "x":
    symexTarget("ay_past_unroll_run")

suite "S8ay (5): regex replace is exact past 16 bytes":

  test "a deletion over a 21+ byte receiver: sxSat, untainted":
    let r = verdict(pastUnroll, "ay_past_unroll")
    check r.status == sxSat
    check not hasKind(r.errors, seZ3StringIncomplete)
    if r.status == sxSat:
      check r.witness[0].len > 20
      check r.witness[0].replace(re"a", "") == "b"

  test "a two-byte literal: an impossible result is sxUnsat":
    check verdict(pastUnrollPair, "ay_past_unroll_pair").status == sxUnsat

  test "a greedy run over a 21+ byte receiver: sxSat":
    let r = verdict(pastUnrollRun, "ay_past_unroll_run")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len > 20
      check r.witness[0].replace(re"f+", "x") == "x"

# ---- items 2 and 4: differential against the concrete std/re -----------------
#
# The reader and the entry formulas against Nim's own `re` / `rex` (PCRE
# 8.45 as linked by the toolchain): every pattern PCRE rejects must be read
# as rejected with Nim's exact `RegexError.msg` (caret offset included),
# every pattern PCRE accepts must not be, and each entry point's Z3 value on
# a concrete subject must be the concrete call's value. A wider sweep of
# the same harness (630 patterns x both modes for the reader; 13932
# pattern/subject/entry/start cases for the formulas) agreed everywhere
# when S8ay landed; this is a sample of it sized to the suite's budget.

const diffPatterns = [
  # rejected by PCRE
  "(", "a)", "[a", "a**", "a{3,2}", "a{65536}", "[z-a]", "\\1", "\\c",
  "(?#x", "a?*", "\\x{100}", "[a-\\d]", "[[:foo:]]", "(a)\\2", "\\A*",
  "[a\\", "a)(", "(?=", "x{2,65536}", "[\\x7a-a]", "\\", "a{,65536}",
  # accepted
  "", ".", "a.b", "\\d+\\D*", "\\s\\S", "[^a-c]+", "a|ab", "(ab|cd)e",
  "^ab$", "x$|^y", "a\\z", "\\Aa", "[[:upper:]]", "a{65535}", "a{,3}",
  "\\1(a)", "(?:)*", "[]-a]", "\\Qa*\\E", "\\cA", "\\x4", "{", "a{1,2"]

const diffRex = ["a b", "a # c\nb", "a +", "a{2 }", "(? :a)", "\\ ", "[ ]"]

suite "S8ay (2/4): the reader against the concrete std/re":

  test "rejection and acceptance agree, with Nim's exact message":
    var cases: seq[(string, bool)]
    for p in diffPatterns:
      cases.add (p, false)
      cases.add (p, true)
    for p in diffRex:
      cases.add (p, true)
      cases.add (p, false)
    var checked = 0
    for (pat, ext) in cases:
      var real = ""
      var accepted = true
      try:
        discard (if ext: rex(pat) else: re(pat))
      except RegexError as e:
        accepted = false
        real = e.msg
      let pr = parsePcre(pat, ext)
      if pr.status == psUnknown: continue
      checkpoint (if ext: "rex " else: "re ") & escape(pat) & " real=" &
        escape(real) & " ours=" & $pr.status & " " & escape(pr.errMsg)
      inc checked
      if accepted: check pr.status in {psOk, psUnmodelled}
      else:
        check pr.status == psRejected
        check pr.errMsg == real
    check checked >= 50

const semPatterns = ["", "a", "ab", "a|ab", "a*", "a+?", ".", "\\D", "[^a]",
                     "^a", "a$", "a\\Z", "x$|^y", "a b", "ba+", "b\\s*$"]
const semSubjects = ["", "a", "ab", "ba\n", "xaba", "a b"]
const semEntries = [("match", 1), ("match", 9), ("contains", 0),
                    ("contains", 1), ("startsWith", 0), ("endsWith", 0),
                    ("find", 0), ("find", 9), ("matchLen", 0),
                    ("findBoundsLast", 1)]

suite "S8ay (1/2): the entry formulas against the concrete std/re":

  test "each entry point's value is the concrete call's":
    let ctx = newContext()
    setCurrentContext(ctx)
    var ctr = 0
    proc fresh(tag: string): string =
      inc ctr
      tag & "#" & $ctr
    var decided = 0
    for p in semPatterns:
      let rx = re(p)
      for subj in semSubjects:
        for (name, st) in semEntries:
          let real: int = case name
            of "match": int(subj.match(rx, st))
            of "contains": int(subj.contains(rx, st))
            of "startsWith": int(subj.startsWith(rx))
            of "endsWith": int(subj.endsWith(rx))
            of "find": subj.find(rx, st)
            of "matchLen": subj.matchLen(rx, st)
            else: subj.findBounds(rx, st).last
          let sp = RegexSpec(entry: name, flag: "re", pattern: p)
          let r = lowerRegexEntry(sp, parseSpec(sp), mkString(subj),
                                  mkInt(st), fresh)
          if r.outcome != roValue: continue
          let sol = newSolver(ctx)
          for d in r.defs: sol.add d
          checkpoint escape(p) & " " & escape(subj) & " " & name & "(" &
                     $st & ") real " & $real
          check $sol.check() == "zsSat"
          let m = sol.model
          let got =
            if name in ["match", "contains", "startsWith", "endsWith"]:
              int(m.evalBool(r.b))
            else: int(m.evalInt(r.i))
          check got == real
          inc decided
    check decided >= 700

# ---- the membership entries, exhaustively ------------------------------------
#
# RFC-0005 S8bb: moved to `tsymex_rfc0005_s8bb_exhaustive.nim` (this
# suite's runtime; the coverage is unchanged there).

# ---- item 6: step 1c's refutation without the full budget first ------------
#
# S8aw's join walk (a first index past the last) is refuted only by step
# 1c's facts. Until S8ay `checkCapped` ran step 1's full-theory search to
# half the default `seqQueryRLimit` first: 10,000,930 units, about 20 s on
# Z3 5.1, for a refutation the facts find in a few thousand. The
# facts-first check (`factsFirstRLimit`) answers it before step 1. Pinned
# at the DEFAULT budget by the units the walk spends (`rlimitDelta`, this
# file's `-d:symexQueryStats`), which no verdict shows.

proc joinFoundExceedsLast(s, t: string) =
  if t in s and s.find(t, 0) >= 0 and s.rfind(t) < s.find(t, 0):
    symexTarget("ay_join")

proc joinFromI(s, t: string; i: int) =
  if i >= 0 and i <= s.len:
    let r = s.find(t, i)
    if r >= 0 and s.rfind(t) < r:
      symexTarget("ay_join_i")

proc unitsSpent(): int =
  ## The Z3 units every query since the last reset spent.
  for q in symexQueryStats: result += q.rlimitDelta

suite "S8ay (6): step 1c decides before the full-theory search":

  test "the join walk is sxUnsat at the default budget, within factsFirstRLimit":
    symexQueryStats = @[]
    let r = symexFind(joinFoundExceedsLast, tLabel("ay_join"))
    let units = unitsSpent()
    checkpoint $r.status & " " & show(r.errors) & " units=" & $units
    check r.status == sxUnsat
    check units < int(factsFirstRLimit)

  test "from a symbolic start too":
    symexQueryStats = @[]
    let r = symexFind(joinFromI, tLabel("ay_join_i"))
    let units = unitsSpent()
    checkpoint $r.status & " " & show(r.errors) & " units=" & $units
    check r.status == sxUnsat
    check units < int(factsFirstRLimit)

suite "S8ay: walker version floor":
  test "symexWalkerVersion >= 198":
    check parseInt(symexWalkerVersion) >= 198
