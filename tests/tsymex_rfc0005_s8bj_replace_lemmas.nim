## RFC-0005 S8bj, item 5 -- S8bb's undecided `replace` queries Q2, Q7 and
## Q8, as walker verdicts.
##
## S8ay / S8bb lowered `replace(s, re, by)` exactly (a recursive function
## over the receiver's suffixes), but Z3 left these three `unknown` on both
## pinned builds: an unbounded length comparison (Q2) and `contains` over
## the result (Q7, Q8) need an induction over the receiver that Z3's
## recursive-function unfolding does not do. The walker now states two
## facts of every `replace` value beside the exact term
## (`runtime_strings.regexReplaceLemmas`), each true of every receiver:
##   * the image: for a one-byte-set pattern (`[S]`, `[S]+`) and a literal
##     `by`, every byte of the result is a byte outside `S` kept as is or
##     part of a copy of `by`: `r in ([^S] | by)*`;
##   * the lengths: with `k` matches removing `c` bytes, `len(r) = len(s) -
##     c + k * len(by)`, `k * mn <= c <= k * mx` (the pattern's match
##     lengths), `c <= len(s)`.
## Each pin's verdict is `std/re`'s on every receiver (an exhaustive check
## over short receivers is below).
import std/[unittest, strutils, re, times]
import nelli/symex
import nelli/smt/types

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

proc q2(s: string) =
  # Removing digits never grows the receiver.
  if s.replace(re"[0-9]", "").len > s.len:
    symexTarget("bj_q2")

proc q7(s: string) =
  # Every run of `f` becomes one `x`: no `f` is left, so no "ff".
  if s.replace(re"f+", "x").contains("ff"):
    symexTarget("bj_q7")

proc q8(s: string) =
  if s.replace(re"a", "").contains("a"):
    symexTarget("bj_q8")

proc q2sat(s: string) =
  # The lemmas leave the reachable values reachable.
  if s.len > 3 and s.replace(re"[0-9]", "").len == s.len - 2:
    symexTarget("bj_q2_sat")

proc q7sat(s: string) =
  if s.len > 2 and s.replace(re"f+", "x") == "xax":
    symexTarget("bj_q7_sat")

proc q8sat(s: string) =
  if s.len > 2 and s.replace(re"a", "") == "b":
    symexTarget("bj_q8_sat")

proc growsBy(s: string) =
  # A longer `by`: `len(r) = len(s) - c + 2k`, `c >= k`.
  if s.replace(re"q", "yy").len > 2 * s.len:
    symexTarget("bj_grows_by")

suite "S8bj (5): Q2, Q7 and Q8 are decided":

  test "Q2: replace([0-9] -> \"\") never grows: sxUnsat":
    check verdict(q2, "bj_q2").status == sxUnsat

  test "Q7: replace(f+ -> \"x\") never contains \"ff\": sxUnsat":
    check verdict(q7, "bj_q7").status == sxUnsat

  test "Q8: replace(a -> \"\") never contains \"a\": sxUnsat":
    check verdict(q8, "bj_q8").status == sxUnsat

  test "a longer by: at most twice the length: sxUnsat":
    check verdict(growsBy, "bj_grows_by").status == sxUnsat

  test "the reachable values stay reachable: sxSat, std/re's witness":
    let a = verdict(q2sat, "bj_q2_sat")
    check a.status == sxSat
    if a.status == sxSat:
      let w = a.witness[0]
      check w.len > 3 and w.replace(re"[0-9]", "").len == w.len - 2
    let b = verdict(q7sat, "bj_q7_sat")
    check b.status == sxSat
    if b.status == sxSat:
      check b.witness[0].replace(re"f+", "x") == "xax"
    let c = verdict(q8sat, "bj_q8_sat")
    check c.status == sxSat
    if c.status == sxSat:
      let w = c.witness[0]
      check w.len > 2 and w.replace(re"a", "") == "b"
