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
## RFC-0005 S8cm: part 2 of 4 of this suite, with
## `tsymex_rfc0005_s8bb_replace`, `tsymex_rfc0005_s8bb_replace_d`,
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

proc dollar(s: string) =
  # `$` holds before the final newline and at the end.
  if s == "a\n" and s.replace(re"$", "-") != "a-\n-":
    symexTarget("bb_rep_dollar")

proc caret(s: string) =
  if s == "aa" and s.replace(re"^a", "-") != "-a":
    symexTarget("bb_rep_caret")

proc caretOrA(s: string) =
  # NOTEMPTY_ATSTART refuses `^` at 0 on the retry; `a` matches at 1.
  if s == "ba" and s.replace(re"^|a", "-") != "-b-":
    symexTarget("bb_rep_caret_or")

proc crlfDollar(s: string) =
  if s == "xa\r\n" and s.replace(re"(*CRLF)a$", "-") != "x-\r\n":
    symexTarget("bb_rep_crlf_dollar")

suite "S8bb (6): replace takes PCRE's chosen match, Nim's empty-match retry":
  test "anchors, under the newline convention":
    check verdict(dollar, "bb_rep_dollar").status == sxUnsat
    check verdict(caret, "bb_rep_caret").status == sxUnsat
    check verdict(caretOrA, "bb_rep_caret_or").status == sxUnsat
    check verdict(crlfDollar, "bb_rep_crlf_dollar").status == sxUnsat
