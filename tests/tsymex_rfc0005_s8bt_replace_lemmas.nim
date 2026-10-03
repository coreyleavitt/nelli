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

# ---- containment past 16 bytes, non-ASCII and escaped bytes ---------------------

proc manyBytes(s: string) =
  if s.replace(re"[a-z]", "").contains("m"):
    symexTarget("bt_many_bytes")

proc nonAscii(s: string) =
  if s.replace(re"\xe9+", "-").contains("\xe9"):
    symexTarget("bt_non_ascii")

proc controlBytes(s: string) =
  if s.replace(re"[\x00-\x08]", "").contains("\x01"):
    symexTarget("bt_control_bytes")

proc spaceNl(s: string) =
  if s.replace(re"\s", "").contains("\n"):
    symexTarget("bt_space_nl")

proc manyBytesSat(s: string) =
  if s.len > 18 and s.replace(re"[a-z]", "") == "M":
    symexTarget("bt_many_bytes_sat")

# ---- no match, no change -----------------------------------------------------

proc identity(s: string) =
  # With no `a` in s nothing is replaced.
  if not s.contains("a") and s.replace(re"a", "x") != s:
    symexTarget("bt_identity")

proc identityAlt(s, by: string) =
  # `ab|cd` matches only at an `a` or a `c`.
  if not s.contains("a") and not s.contains("c") and
     s.replace(re"ab|cd", by) != s:
    symexTarget("bt_identity_alt")

proc identitySat(s: string) =
  if s.len >= 2 and s.replace(re"a", "x") != s and not s.contains("x"):
    symexTarget("bt_identity_sat")

# ---- no fact where none holds ----------------------------------------------------

proc anchoredSat(s: string) =
  # `^a` matches only at 0: "aa" keeps its second `a`.
  if s.replace(re"^a", "").contains("a"):
    symexTarget("bt_anchored_sat")

proc commitKeeps(s: string) =
  if s.replace(re"a(*COMMIT)b|a", "").contains("a"):
    symexTarget("bt_commit_keeps")

proc pairSat(s: string) =
  # An `a` not followed by `b` stays.
  if s.replace(re"ab", "").contains("a"):
    symexTarget("bt_pair_sat")

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

  test "(?:ab|a)+ leaves no a: sxUnsat":
    check verdict(altPlus, "bt_alt_plus").status == sxUnsat

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

suite "S8bt (7): containment past 16 bytes and non-ASCII":

  test "[a-z] (26 bytes) leaves no m: sxUnsat":
    check verdict(manyBytes, "bt_many_bytes").status == sxUnsat

  test "\\xe9+ leaves no \\xe9: sxUnsat":
    check verdict(nonAscii, "bt_non_ascii").status == sxUnsat

  test "[\\x00-\\x08] leaves no \\x01: sxUnsat":
    check verdict(controlBytes, "bt_control_bytes").status == sxUnsat

  test "\\s leaves no LF: sxUnsat":
    check verdict(spaceNl, "bt_space_nl").status == sxUnsat

  test "reachable: sxSat, std/re's witness":
    let r = verdict(manyBytesSat, "bt_many_bytes_sat")
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].len > 18 and r.witness[0].replace(re"[a-z]", "") == "M"

suite "S8bt (7): no match leaves the receiver":

  test "no a, no change: sxUnsat":
    check verdict(identity, "bt_identity").status == sxUnsat

  test "no a or c, no change for ab|cd and any by: sxUnsat":
    check verdict(identityAlt, "bt_identity_alt").status == sxUnsat

  test "reachable: sxSat, std/re's witness":
    let r = verdict(identitySat, "bt_identity_sat")
    check r.status == sxSat
    if r.status == sxSat:
      let w = r.witness[0]
      check w.len >= 2 and w.replace(re"a", "x") != w and "x" notin w

suite "S8bt (7): no fact where none holds":

  test "a(*COMMIT)b|a keeps an a: never sxUnsat":
    # "ac": the attempt at 0 backtracks into COMMIT, the search ends. No
    # fact may refute it; finding the model is Z3's (sxSat with std/re's
    # witness locally, undecided under Z3 4.13.4 on the Windows leg).
    let r = verdict(commitKeeps, "bt_commit_keeps")
    check r.status in {sxSat, sxUnknown}
    if r.status == sxSat:
      check r.witness[0].replace(re"a(*COMMIT)b|a", "").contains("a")

  test "^a and ab keep some a: sxSat, std/re's witness":
    let a = verdict(anchoredSat, "bt_anchored_sat")
    check a.status == sxSat
    if a.status == sxSat:
      check a.witness[0].replace(re"^a", "").contains("a")
    let b = verdict(pairSat, "bt_pair_sat")
    check b.status == sxSat
    if b.status == sxSat:
      check b.witness[0].replace(re"ab", "").contains("a")

suite "S8bt (7): walker version":

  test "the walker version is at least 224":
    check parseInt(symexWalkerVersion) >= 224
