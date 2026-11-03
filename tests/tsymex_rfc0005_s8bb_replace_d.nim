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
## RFC-0005 S8cm: part 3 of 4 of this suite, with
## `tsymex_rfc0005_s8bb_replace`, `tsymex_rfc0005_s8bb_replace_b`,
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

const seqBudget = SymexSettings(budget: ResourceBudget(
  seqQueryRLimit: 100_000_000'u))

template verdict(sut: untyped; label: string): SymexResult =
  let t0 = epochTime()
  let r = symexFind(sut, tLabel(label))
  echo "  ", label, ": ", r.status, " ", formatFloat(epochTime() - t0,
                                                     ffDecimal, 1), " s"
  checkpoint $r.status & " " & show(r.errors) & " witness=" &
             (if r.status in {sxSat, sxRaised}: $r.witness else: "-")
  r

proc symbolicAlt(s: string) =
  # PCRE takes `a` before `ab`: "ab" gives "xb" (the longest match would
  # give "x"), so this is reached, by "ab" alone (replay-confirmed).
  # (`s.len == 2 and ... == "x"`, unsat, is undecided under the walker's
  # budget: `beSolverUndef`, RFC-0005 S8bb's measurements.)
  if s.len == 2 and s[0] == 'a' and s.replace(re"a|ab", "x") == "xb":
    symexTarget("bb_rep_sym_alt")

proc symbolicEmpty(s: string) =
  # `x*` on one byte: "x" gives "-", any other byte c gives "-c-"; never
  # "--".
  if s.len == 1 and s.replace(re"x*", "-") == "--":
    symexTarget("bb_rep_sym_empty")

proc symbolicEmptyHit(s: string) =
  # `$` matches empty at the end only: "q-" comes from "q" alone
  # (replay-confirmed).
  if s.len == 1 and s.replace(re"$", "-") == "q-":
    symexTarget("bb_rep_sym_empty_hit")

suite "S8bb (6): replace takes PCRE's chosen match, Nim's empty-match retry":
  test "a symbolic receiver":
    let alt = verdict(symbolicAlt, "bb_rep_sym_alt")
    check alt.status == sxSat
    if alt.status == sxSat:
      check alt.witness[0] == "ab"
    check verdict(symbolicEmpty, "bb_rep_sym_empty").status == sxUnsat
    # RFC-0005 batch 7: since S8bp solves this label query in a context
    # of its own, its cost is the query text's alone. Z3 5.1 decides it
    # in 198,718 units; Z3 4.13.4 needs 18,801,883 (12,755,004 in the
    # walk's context at batch 6), and step 1 has half of
    # `seqQueryRLimit`'s 20M, so on 4.13.4 the default walk declines.
    # Under the defaults the pin is sxSat or that decline, never sxUnsat;
    # under an explicit 100M sequence budget it is Nim's witness on both
    # Z3s.
    let hit = verdict(symbolicEmptyHit, "bb_rep_sym_empty_hit")
    check hit.status in {sxSat, sxUnknown}
    if hit.status == sxSat:
      check hit.witness[0] == "q"
    else:
      check hit.errors.anyIt(it.kind == beSolverUndef)
    let wide = symexFind(symbolicEmptyHit, tLabel("bb_rep_sym_empty_hit"),
                         seqBudget)
    check wide.status == sxSat
    if wide.status == sxSat:
      check wide.witness[0] == "q"
      check "q".replace(re"$", "-") == "q-"
