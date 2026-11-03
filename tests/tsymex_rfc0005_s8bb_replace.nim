## RFC-0005 (soundness channels) slice S8bb, item 6 -- `replace(s, re, by)`
## for an alternation, an anchor and a pattern that can match empty.
##
## At ae08bfd each of these declined (sxUnknown, `seZ3StringIncomplete`):
## S8aw / S8ay lowered only a fixed-length sequence of byte sets and one
## byte set under a greedy `+`. Each pin below is a verdict `std/re`
## decides concretely (probed against Nim 2.2.10's `std/re`, PCRE 8.45):
## Nim's loop takes PCRE's chosen match at the leftmost position, and
## after an empty match retries at the same position with
## NOTEMPTY_ATSTART.
##
## RFC-0005 S8cm: part 1 of 4 of this suite, with
## `tsymex_rfc0005_s8bb_replace_b`, `tsymex_rfc0005_s8bb_replace_d`,
## `tsymex_rfc0005_s8bb_replace_c`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 90 s).

import std/[unittest, strutils, re, times, sequtils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/pcre_syntax
import nelli/smt/pcre_select
import nelli/smt/regex_parser
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let t0 = epochTime()
  let r = symexFind(sut, tLabel(label))
  echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t0,
                                                     ffDecimal, 1), " s"
  checkpoint $r.status & " " & show(r.errors) & " witness=" &
             (if r.status in {sxSat, sxRaised}: $r.witness else: "-")
  r

proc emptyEverywhere(s: string) =
  if s == "ab" and s.replace(re"x*", "-") != "-a-b-":
    symexTarget("bb_rep_empty")

proc emptyAfterMatch(s: string) =
  # The empty match at the end of "aa" is a match of its own.
  if s == "aab" and s.replace(re"a*", "-") != "--b-":
    symexTarget("bb_rep_empty_after")

proc alternation(s: string) =
  if s == "ab" and s.replace(re"a|ab", "-") != "-b":
    symexTarget("bb_rep_alt")

proc lazyStar(s: string) =
  # `a*?` takes the empty match first; NOTEMPTY_ATSTART then takes one `a`.
  if s == "baaa" and s.replace(re"a*?", "-") != "-b------":
    symexTarget("bb_rep_lazy")

proc emptyAlternative(s: string) =
  if s == "aaa" and s.replace(re"a|", "-") != "---":
    symexTarget("bb_rep_empty_alt")

proc acceptAlt(s: string) =
  if s == "ab" and s.replace(re"a(*ACCEPT)b|b", "-") != "--":
    symexTarget("bb_rep_accept")

suite "S8bb (6): replace takes PCRE's chosen match, Nim's empty-match retry":

  test "a pattern that can match empty":
    check verdict(emptyEverywhere, "bb_rep_empty").status == sxUnsat
    check verdict(emptyAfterMatch, "bb_rep_empty_after").status == sxUnsat
    check verdict(lazyStar, "bb_rep_lazy").status == sxUnsat
    check verdict(emptyAlternative, "bb_rep_empty_alt").status == sxUnsat

  test "an alternation takes its first alternative that matches":
    check verdict(alternation, "bb_rep_alt").status == sxUnsat
    check verdict(acceptAlt, "bb_rep_accept").status == sxUnsat
