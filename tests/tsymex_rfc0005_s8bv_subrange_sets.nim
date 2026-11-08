## RFC-0005 (soundness channels) slice S8bv -- S8bq's remainder, item 2 (subrange fields and sets).
##
## Item 2 was replaced; see the RFC's "As landed (S8bv)". Nim has no set
## conversion between two base domains -- every one is a type mismatch, and a
## literal is typed as its target, converting (and range-checking) each
## ELEMENT. The precision gap the probes found instead is an enum SUBRANGE
## (`range[a1..a2]`), which was unclassified: as a parameter, a local, a field
## and a set's base type it is the enum narrowed to its bounds, and Nim's range
## checks (assignment, conversion, argument, set element) raise `RangeDefect`.
## Split so each file stays under 60 s on Windows.
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc hasMsg(errs: seq[SymexErrorInfo]; k: SymexErrorKind; sub: string): bool =
  for e in errs:
    if e.kind == k and sub in e.msg: return true
  false

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

from ./s8cu_helpers import nativeHits

type
  E4 = enum e0, e1, e2, e3
  SE = range[e1..e2]
  SubHolder = object
    f: SE
    n: int

proc takeSE(s: set[SE]): int = card(s)

proc subField(h: SubHolder) =
  if ord(h.f) == 0: symexTarget("bv_sub_field_out")
  if h.f == e2 and h.n == 4: symexTarget("bv_sub_field")

proc subSetParam(s: set[SE]) =
  if card(s) == 3: symexTarget("bv_sub_set_out")
  if e2 in s and e1 notin s: symexTarget("bv_sub_set")

proc subSetOps(s, t: set[SE]) =
  if e1 in s + t and e1 notin s and e1 notin t: symexTarget("bv_sub_set_union")
  if s - t == {e1} and s <= t: symexTarget("bv_sub_set_diff")
  if s * t == {e1, e2} and card(s) == 2: symexTarget("bv_sub_set_inter")

proc subSetIter(s: set[SE]) =
  var k = 0
  for x in s: k = k * 10 + ord(x)
  if k == 12: symexTarget("bv_sub_set_iter")
  if k == 21: symexTarget("bv_sub_set_iter_rev")

proc subSetElem(e: E4) =
  # A literal is typed as its target: each element converts to `SE`.
  try:
    if takeSE({e1, e}) == 2: symexTarget("bv_sub_set_elem")
  except RangeDefect:
    if e == e3: symexTarget("bv_sub_set_elem_raise")
    if e == e2: symexTarget("bv_sub_set_elem_bad")

proc subSetIncl(e: E4) =
  var s: set[SE]
  try:
    s.incl e
  except RangeDefect:
    if e == e0: symexTarget("bv_sub_set_incl_raise")
  if e2 in s and e != e2: symexTarget("bv_sub_set_incl_bad")

suite "S8bv: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 250

suite "S8bv (2): enum subranges":
  test "a subrange field":
    check verdict(subField, "bv_sub_field_out").status == sxUnsat
    let r = verdict(subField, "bv_sub_field")
    check r.status == sxSat
    check r.errors.len == 0
    check "bv_sub_field" in nativeHits(subField(SubHolder(f: e2, n: 4)))
  test "a set over a subrange":
    check verdict(subSetParam, "bv_sub_set_out").status == sxUnsat
    let r = verdict(subSetParam, "bv_sub_set")
    check r.status == sxSat
    check r.errors.len == 0
    check $r.witness == "({e2},)"
    check "bv_sub_set" in nativeHits(subSetParam({e2}))
  test "set operators over a subrange":
    check verdict(subSetOps, "bv_sub_set_union").status == sxUnsat
    check verdict(subSetOps, "bv_sub_set_diff").status == sxUnsat
    check verdict(subSetOps, "bv_sub_set_inter").status == sxSat
    check "bv_sub_set_inter" in nativeHits(subSetOps({e1, e2}, {e1, e2}))
  test "iterating a set over a subrange":
    check verdict(subSetIter, "bv_sub_set_iter").status == sxSat
    check verdict(subSetIter, "bv_sub_set_iter_rev").status == sxUnsat
    check "bv_sub_set_iter" in nativeHits(subSetIter({e1, e2}))
  test "a literal's element converts to the subrange":
    check verdict(subSetElem, "bv_sub_set_elem").status == sxSat
    check verdict(subSetElem, "bv_sub_set_elem_raise").status == sxSat
    check verdict(subSetElem, "bv_sub_set_elem_bad").status == sxUnsat
    check "bv_sub_set_elem_raise" in nativeHits(subSetElem(e3))
  test "incl range-checks a subrange element":
    check verdict(subSetIncl, "bv_sub_set_incl_raise").status == sxSat
    check verdict(subSetIncl, "bv_sub_set_incl_bad").status == sxUnsat
    check "bv_sub_set_incl_raise" in nativeHits(subSetIncl(e0))
