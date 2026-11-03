## RFC-0005 S8bt (item 7) -- unbounded `replace(s, re, by)` queries past
## S8bj's two lemma shapes, as walker verdicts.
##
## S8bj stated facts of a recursively defined `replace` value only for
## S8aw's shapes (a sequence of byte sets, or one set under `+`), with the
## length relation only for a numeral `len(by)` and the image only for a
## one-set pattern and a literal `by` (its per-byte form for at most 16
## plain ASCII bytes). S8bt states them for every pattern the walker
## lowers (`pcre_select.replaceFacts`, `regex_parser.replaceLemmas`):
##   * the lengths, `len(r) = len(s) - c + k*len(by)`, for any `by` (the
##     product a fresh Int with its linear consequences);
##   * the bytes every attempt matches whatever follows (`sure`): such a
##     byte of the subject is always inside a match, so it is in `r` only
##     when it is in `by` -- for a literal or a symbolic `by`, any byte.
## Each pin's verdict is `std/re`'s on every receiver; the facts themselves
## are checked against `std/re` in `tsymex_rfc0005_s8bt_replace_facts`.
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8bt_replace_lemmas_b`. Split so that each part compiles and
## runs in under 60 s on the Windows legs (the whole file took 64 s).

import std/[unittest, strutils, re, times]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

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

# ---- a symbolic `len(by)` ----------------------------------------------------

proc lenByNonEmpty(s, by: string) =
  # Each match removes one byte and adds len(by) >= 1.
  if by.len >= 1 and s.replace(re"a", by).len < s.len:
    symexTarget("bt_len_by_nonempty")

proc lenByEmpty(s, by: string) =
  if by.len == 0 and s.replace(re"[0-9]+", by).len > s.len:
    symexTarget("bt_len_by_empty")

proc lenBySat(s, by: string) =
  if by.len == 2 and s.len == 2 and s.replace(re"a", by).len == 4:
    symexTarget("bt_len_by_sat")

# ---- patterns past S8aw's shapes -------------------------------------------------

proc altSets(s: string) =
  # `[0-9]|x`: every digit and every `x` is matched.
  if s.replace(re"[0-9]|x", "").contains("x"):
    symexTarget("bt_alt_sets")

proc altPlusBounded(s: string) =
  if s.len <= 16 and s.replace(re"(?:ab|a)+", "-").contains("a"):
    symexTarget("bt_alt_plus_bounded")

proc altPlus(s: string) =
  # An `a` always starts a match of `(?:ab|a)+`.
  if s.replace(re"(?:ab|a)+", "-").contains("a"):
    symexTarget("bt_alt_plus")

proc altLen(s: string) =
  if s.replace(re"ab|cd", "").len > s.len:
    symexTarget("bt_alt_len")

proc verbLen(s: string) =
  # The agenda's step table (a verb): every match is one or two bytes.
  if s.replace(re"a(*COMMIT)b|a", "").len > s.len:
    symexTarget("bt_verb_len")

proc emptyMatches(s: string) =
  # `a*?` matches empty everywhere: at most 2*len(s) + 1 copies of `by`.
  if s.replace(re"a*?", "-").len > 3 * s.len + 1:
    symexTarget("bt_empty_matches")

proc altSetsSat(s: string) =
  if s.len == 3 and s.replace(re"[0-9]|x", "") == "y":
    symexTarget("bt_alt_sets_sat")

# ---- a symbolic `by` ----------------------------------------------------------

proc byNoQ(s, by: string) =
  if not by.contains("q") and s.replace(re"q+", by).contains("q"):
    symexTarget("bt_by_no_q")

proc byAlt(s, by: string) =
  if not by.contains("a") and s.replace(re"a|bc", by).contains("a"):
    symexTarget("bt_by_alt")

proc byNoQSat(s, by: string) =
  if not by.contains("q") and s.len >= 2 and s.replace(re"q+", by) == "zz":
    symexTarget("bt_by_no_q_sat")

suite "S8bt (7): a symbolic len(by)":

  test "len(by) >= 1 never shrinks a one-byte replace: sxUnsat":
    check verdict(lenByNonEmpty, "bt_len_by_nonempty").status == sxUnsat

  test "an empty by never grows: sxUnsat":
    check verdict(lenByEmpty, "bt_len_by_empty").status == sxUnsat

  test "the reachable lengths stay reachable: sxSat, std/re's witness":
    let r = verdict(lenBySat, "bt_len_by_sat")
    check r.status == sxSat
    if r.status == sxSat:
      let (s, by) = (r.witness[0], r.witness[1])
      check by.len == 2 and s.len == 2 and s.replace(re"a", by).len == 4

suite "S8bt (7): patterns past S8aw's shapes":

  test "[0-9]|x leaves no x: sxUnsat":
    check verdict(altSets, "bt_alt_sets").status == sxUnsat

  test "(?:ab|a)+ leaves no a up to its safe length: sxUnsat":
    # RFC-0005 S8cf: past it `replace` can stop at a limit and keep the rest
    # (`a` * 100000 on the JIT's stack, -27): an unbounded `s` is not refuted.
    check verdict(altPlus, "bt_alt_plus").status == sxUnknown
    check verdict(altPlusBounded, "bt_alt_plus_bounded").status == sxUnsat

  test "ab|cd never grows: sxUnsat":
    check verdict(altLen, "bt_alt_len").status == sxUnsat

  test "a(*COMMIT)b|a never grows: sxUnsat":
    check verdict(verbLen, "bt_verb_len").status == sxUnsat

  test "empty matches: at most 2*len+1 copies of by: sxUnsat":
    check verdict(emptyMatches, "bt_empty_matches").status == sxUnsat

  test "the reachable values stay reachable: sxSat, std/re's witness":
    let r = verdict(altSetsSat, "bt_alt_sets_sat")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len == 3 and
            r.witness[0].replace(re"[0-9]|x", "") == "y"

suite "S8bt (7): a symbolic by":

  test "q+ with a by holding no q leaves no q: sxUnsat":
    check verdict(byNoQ, "bt_by_no_q").status == sxUnsat

  test "a|bc with a by holding no a leaves no a: sxUnsat":
    check verdict(byAlt, "bt_by_alt").status == sxUnsat

  test "reachable: sxSat, std/re's witness":
    let r = verdict(byNoQSat, "bt_by_no_q_sat")
    check r.status == sxSat
    if r.status == sxSat:
      let (s, by) = (r.witness[0], r.witness[1])
      check "q" notin by and s.len >= 2 and s.replace(re"q+", by) == "zz"
