## RFC-0005 (soundness channels) slice S8bb, item 5 -- the constructs S8ay
## left undecided (named groups, inline options, `\p{..}`, the `(*...)`
## verbs) and the captures overloads.
##
## At ae08bfd every one of these calls declined (sxUnknown): the pattern
## reader stopped at the construct, and a call with a `matches` array was
## not lowered at all (the write into the array was not modelled). Each pin
## below is a verdict `std/re` decides concretely (the expected values were
## probed against Nim 2.2.10's `std/re`, PCRE 8.45).
##
## RFC-0005 S8cm: part 4 of 4 of this suite, with
## `tsymex_rfc0005_s8bb_captures`, `tsymex_rfc0005_s8bb_captures_b`,
## `tsymex_rfc0005_s8bb_captures_c`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 92 s).

import std/[unittest, strutils, re]
import nelli/symex
import nelli/smt/types

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint $r.status & " " & show(r.errors) & " witness=" &
             (if r.status in {sxSat, sxRaised}: $r.witness else: "-")
  r

proc capSeq(s: string) =
  # (`newSeq[string](2)` aborts the compile in `symexFind`: a different
  # mechanism, reported under RFC-0005 S8bb's "As landed".)
  var m = @["p", "q"]
  if s == "ab" and s.match(re"(a)(b)", m):
    if m[0] != "a" or m[1] != "b":
      symexTarget("bb_cap_seq")

proc capSeqShort(s: string; drop: bool) =
  # The seq's length depends on `drop`: the write needs every set group to
  # fit, so a one-element `matches` is left alone.
  var m = @["p", "q"]
  if drop: discard m.pop()
  if s == "ab" and s.match(re"(a)(b)", m):
    if m[0] != (if drop: "p" else: "a"):
      symexTarget("bb_cap_seq_short")

type Holder = object
  ms: array[2, string]

proc capField(s: string) =
  var h = Holder(ms: ["p", "q"])
  if s == "ab" and s.match(re"(a)(b)", h.ms):
    if h.ms[0] != "a" or h.ms[1] != "b":
      symexTarget("bb_cap_field")

suite "S8bb (5): the captures overloads write `matches` as std/re does":
  test "a seq or a field as the matches array":
    check verdict(capSeq, "bb_cap_seq").status == sxUnsat
    check verdict(capSeqShort, "bb_cap_seq_short").status == sxUnsat
    check verdict(capField, "bb_cap_field").status == sxUnsat
