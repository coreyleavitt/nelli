## RFC-0005 (soundness channels) slice S8bq -- S8bi's remainder: the one
## soundness item and the four precision items S8bi reported and did not fix.
##
## Item 1: a `newSeq` / `newSeqOfCap` / `newSeqUninit` length above 2^20
## was modelled as an allocation that succeeds. A real run raises
## `OutOfMemDefect`, or not, depending on the host. The path is declined,
## scoped to it, exactly as S8bc declines `newSeq`'s (`iekSeqNewZero`).
##
## Item 3: a `Regex` value built outside a regex call (`let r = re"(ab"`)
## was `feUnsupportedExprKind` (`nnkCallStrLit`), and the call form
## (`re("(ab")`, `re(p)`) aborted the compile ("node has no type"). It is
## a constructor call: a pattern PCRE rejects raises `RegexError`.
##
## Item 2: a builtin `set[T]` (a parameter, a local, a field, a result) was
## unclassified, so every set-typed value declined. It is one bit-vector
## with a bit per value of `T`: membership, `incl`, `excl`, `+`, `-`, `*`,
## `<=`, `<`, `==`, `card` and literals are exact.
##
## Item 5: `k in {..}` over a literal with a non-constant element declined.
## The key is evaluated first and not checked; every element is evaluated,
## in order, converted (range-checked) to the base type.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8bq_remainder`, `tsymex_rfc0005_s8bq_remainder_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 71 s).
import std/[unittest, strutils, re]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

# ---- item 2: builtin set values ----------------------------------------------

type E4 = enum e0, e1, e2, e3
type Holder = object
  cs: set[char]
  n: int

proc bsCardBound(s: set[char]) =
  if card(s) == 3 and s <= {'a', 'b'}:
    symexTarget("bq_bs_card_bound")

proc bsLen(s: set[char]) =
  if s.len == 2 and 'a' in s:
    symexTarget("bq_bs_len")

proc bsConstLit() =
  let ls = {'a'..'c', 'x'}
  if card(ls) != 4 or 'b' notin ls or 'd' in ls:
    symexTarget("bq_bs_const_lit")

proc bsEnum(es: set[E4]; e: E4) =
  var u = es
  u.incl e
  if u == {e0..e3} and card(es) == 3:
    symexTarget("bq_bs_enum")

proc bsEnumNo(es: set[E4]) =
  if card(es) > 4:
    symexTarget("bq_bs_enum_no")

proc bsBool(x: bool) =
  var b: set[bool]
  b.incl x
  if card(b) == 2 or x notin b:
    symexTarget("bq_bs_bool")

proc bsInt8(s: set[int8]) =
  if -128'i8 in s and 127'i8 in s and card(s) == 2:
    symexTarget("bq_bs_int8")

proc bsUInt8(s: set[uint8]; k: uint8) =
  if k in s and k > 250'u8 and card(s) == 1:
    symexTarget("bq_bs_uint8")

proc bsRangeIncl(x: int) =
  var rs: set[range[0..9]]
  try:
    rs.incl x
  except RangeDefect:
    if x == 20: symexTarget("bq_bs_range_incl")

proc bsRangeIn(x: int) =
  var rs: set[range[0..9]] = {3}
  try:
    if x in rs: discard
  except RangeDefect:
    if x == -1: symexTarget("bq_bs_range_in")

proc bsRangeInOk(x: int) =
  var rs: set[range[0..9]] = {3}
  try:
    if x in rs and x != 3: symexTarget("bq_bs_range_in_ok")
  except RangeDefect: discard

proc bsField(h: Holder; c: char) =
  var g = h
  g.cs.incl c
  if c notin g.cs:
    symexTarget("bq_bs_field")

proc bsFieldSat(h: Holder) =
  if 'k' in h.cs and h.n == 2:
    symexTarget("bq_bs_field_sat")

proc bsMerge(c: char) =
  var u: set[char]
  if c == 'a': u.incl 'a'
  else: u.incl 'b'
  if card(u) == 2 or ('a' in u) != (c == 'a'):
    symexTarget("bq_bs_merge")

proc mkSet(c: char): set[char] = {c, 'z'}

proc bsReturn(c: char) =
  let r = mkSet(c)
  if c notin r or 'z' notin r:
    symexTarget("bq_bs_return")

proc bsArrayElem(i: int; c: char) =
  var a: array[2, set[char]]
  a[1].incl c
  if i >= 0 and i <= 1 and c in a[i] and i == 0:
    symexTarget("bq_bs_array_elem")

proc bsIter(s: set[char]) =
  var k = 0
  for c in s: inc k
  if k == 2: symexTarget("bq_bs_iter")

suite "S8bq (2): builtin set values":
  test "card counts the members":
    check verdict(bsCardBound, "bq_bs_card_bound").status == sxUnsat
    check verdict(bsLen, "bq_bs_len").status == sxSat
  test "a literal of constants as a value":
    check verdict(bsConstLit, "bq_bs_const_lit").status == sxUnsat
  test "an enum set":
    check verdict(bsEnum, "bq_bs_enum").status == sxSat
    check verdict(bsEnumNo, "bq_bs_enum_no").status == sxUnsat
  test "a bool set":
    check verdict(bsBool, "bq_bs_bool").status == sxUnsat
  test "int8 and uint8 sets":
    check verdict(bsInt8, "bq_bs_int8").status == sxSat
    let r = verdict(bsUInt8, "bq_bs_uint8")
    check r.status == sxSat
    check r.errors.len == 0
  test "incl range-checks its element":
    check verdict(bsRangeIncl, "bq_bs_range_incl").status == sxSat
  test "membership in a set value range-checks the key":
    check verdict(bsRangeIn, "bq_bs_range_in").status == sxSat
    check verdict(bsRangeInOk, "bq_bs_range_in_ok").status == sxUnsat
  test "a set field":
    check verdict(bsField, "bq_bs_field").status == sxUnsat
    let r = verdict(bsFieldSat, "bq_bs_field_sat")
    check r.status == sxSat
    check r.errors.len == 0
  test "paths merge a set":
    check verdict(bsMerge, "bq_bs_merge").status == sxUnsat
  test "a set returned by a call":
    check verdict(bsReturn, "bq_bs_return").status == sxUnsat
  test "a set array element":
    check verdict(bsArrayElem, "bq_bs_array_elem").status == sxUnsat
  test "iterating a set is modelled (RFC-0005 S8bv)":
    let r = verdict(bsIter, "bq_bs_iter")
    check r.status == sxSat
    check r.errors.len == 0
