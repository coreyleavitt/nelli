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
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8bq_remainder`, `tsymex_rfc0005_s8bq_remainder_b`. Split so
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

# ---- item 2: builtin set values ----------------------------------------------

type E4 = enum e0, e1, e2, e3

# ---- item 5: set literals with non-constant elements -------------------------

proc nlMember(c, d: char) =
  if c in {d, 'x'} and c != 'x' and c != d:
    symexTarget("bq_nl_member")

proc nlRange(c, lo, hi: char) =
  if c in {lo..hi} and (c < lo or c > hi):
    symexTarget("bq_nl_range")

proc nlRangeSat(c, lo, hi: char) =
  if c in {lo..hi} and c == 'm' and hi == 'n':
    symexTarget("bq_nl_range_sat")

proc nlElemCheck(y, b: int) =
  # Every element is converted, also after a match.
  try:
    discard y in {3, b}
  except RangeDefect:
    if y == 3 and b == 70000: symexTarget("bq_nl_elem_check")

proc nlKeyUnchecked(x, a: int) =
  try:
    if x in {a, 3}: discard
  except RangeDefect:
    if a >= 0 and a <= 65535: symexTarget("bq_nl_key_unchecked")

proc nlValue(c, lo, hi: char) =
  let l = {c, lo..hi}
  if c notin l or (lo <= hi and lo notin l) or card(l) == 0:
    symexTarget("bq_nl_value")

proc nlValueEmpty(lo, hi: char) =
  let r = {lo..hi}
  if card(r) == 3 and hi == 'e':
    symexTarget("bq_nl_value_empty")

proc nlWhile(s: string; a, b: char) =
  var i = 0
  while i < s.len and s[i] in {a, b}:
    inc i
  if s.len == 2 and i == 2 and s[0] != s[1]:
    symexTarget("bq_nl_while")

# ---- item 4: newSeqUninit taints a read of an unwritten element ------------

proc unNoRead(n: int) =
  if n < 0: return
  let xs = newSeqUninit[int](n)
  if xs.len == 5: symexTarget("bq_un_no_read")

proc unWrittenRead(k: int) =
  var xs = newSeqUninit[int](3)
  xs[0] = k
  if xs[0] == 7: symexTarget("bq_un_written_read")

proc unUnwrittenRead() =
  var xs = newSeqUninit[int](3)
  xs[0] = 1
  if xs[1] == 42: symexTarget("bq_un_unwritten_read")

proc unSymIndexDead(i: int) =
  var xs = newSeqUninit[int](3)
  xs[0] = 1
  xs[1] = 2
  if i >= 0 and i <= 1:
    if xs[i] == 5: symexTarget("bq_un_sym_index_dead")

proc unSymIndexLive(i: int) =
  var xs = newSeqUninit[int](3)
  xs[0] = 1
  xs[1] = 2
  if i >= 0 and i <= 2:
    if xs[i] == 5: symexTarget("bq_un_sym_index_live")

proc unMerge(c: bool) =
  var xs = newSeqUninit[int](2)
  if c: xs[0] = 1
  else: xs[0] = 2
  if xs[0] == 3: symexTarget("bq_un_merge")

proc unMergeOneArm(c: bool) =
  var xs = newSeqUninit[int](2)
  if c: xs[0] = 1
  if not c and xs[0] == 3: symexTarget("bq_un_merge_one_arm")

proc unDelMoves() =
  # `del` moves the last (unwritten) element into the deleted slot.
  var xs = newSeqUninit[int](3)
  xs[0] = 1
  xs[1] = 2
  xs.del(0)
  if xs[0] == 9: symexTarget("bq_un_del_moves")

proc unDelWritten() =
  var xs = newSeqUninit[int](2)
  xs[0] = 1
  xs[1] = 2
  xs.del(0)
  if xs[0] == 9: symexTarget("bq_un_del_written")

proc unAdd(k: int) =
  var xs = newSeqUninit[int](1)
  xs.add k
  if xs[1] == 4: symexTarget("bq_un_add")

proc unPop() =
  var xs = newSeqUninit[int](2)
  xs[1] = 5
  let v = xs.pop()
  if v == 6: symexTarget("bq_un_pop")

proc unPopUnwritten() =
  var xs = newSeqUninit[int](2)
  xs[0] = 5
  let v = xs.pop()
  if v == 6: symexTarget("bq_un_pop_unwritten")

proc mkUninit(k: int): seq[int] =
  result = newSeqUninit[int](2)
  result[0] = k

proc unReturnWritten(k: int) =
  let ys = mkUninit(k)
  if ys[0] == 4: symexTarget("bq_un_return_written")

proc unReturnUnwritten(k: int) =
  let ys = mkUninit(k)
  if ys[1] == 4: symexTarget("bq_un_return_unwritten")

type UnHolder = object
  s: seq[int]

proc unField(k: int) =
  var h: UnHolder
  h.s = newSeqUninit[int](2)
  h.s[0] = k
  if h.s[0] == 3: symexTarget("bq_un_field")

proc unAugUnwritten() =
  # `xs[i] += v` reads the element.
  var xs = newSeqUninit[int](2)
  xs[0] += 1
  if xs[0] == 8: symexTarget("bq_un_aug_unwritten")

proc unAugWritten(k: int) =
  var xs = newSeqUninit[int](2)
  xs[0] = k
  xs[0] += 1
  if xs[0] == 8: symexTarget("bq_un_aug_written")

proc unLoopFill(k: int) =
  var xs = newSeqUninit[int](3)
  for i in 0 ..< 3: xs[i] = k
  if xs[2] != k: symexTarget("bq_un_loop_fill")

suite "S8bq (5): set literals with non-constant elements":
  test "membership in a literal of variables":
    check verdict(nlMember, "bq_nl_member").status == sxUnsat
  test "membership in a range with variable bounds":
    check verdict(nlRange, "bq_nl_range").status == sxUnsat
    check verdict(nlRangeSat, "bq_nl_range_sat").status == sxSat
  test "every element is converted, after a match too":
    check verdict(nlElemCheck, "bq_nl_elem_check").status == sxSat
  test "the key is not range-checked":
    check verdict(nlKeyUnchecked, "bq_nl_key_unchecked").status == sxUnsat
  test "a literal with variable elements as a value":
    check verdict(nlValue, "bq_nl_value").status == sxUnsat
    check verdict(nlValueEmpty, "bq_nl_value_empty").status == sxSat
  test "in a while guard":
    check verdict(nlWhile, "bq_nl_while").status == sxSat

suite "S8bq (4): newSeqUninit taints only a read of an unwritten element":
  test "no element read: clean":
    let r = verdict(unNoRead, "bq_un_no_read")
    check r.status == sxSat
    # (item 1's decline of a length above 2^20 is on its own path)
    check not r.errors.hasKind(feUnsupportedOpHavoc)
  test "a written element reads exactly":
    let r = verdict(unWrittenRead, "bq_un_written_read")
    check r.status == sxSat
    check r.errors.len == 0
  test "an unwritten element's read is tainted":
    let r = verdict(unUnwrittenRead, "bq_un_unwritten_read")
    check r.status == sxUnknown
    check r.errors.hasMsg(feUnsupportedOpHavoc,
      "newSeqUninit element read before it is written")
  test "a symbolic index confined to written elements":
    check verdict(unSymIndexDead, "bq_un_sym_index_dead").status == sxUnsat
  test "a symbolic index that may reach an unwritten element":
    check verdict(unSymIndexLive, "bq_un_sym_index_live").status == sxUnknown
  test "written on both arms of a merge":
    check verdict(unMerge, "bq_un_merge").status == sxUnsat
  test "written on one arm of a merge, read on the other":
    check verdict(unMergeOneArm, "bq_un_merge_one_arm").status == sxUnknown
  test "del moves an unwritten element into a written slot":
    check verdict(unDelMoves, "bq_un_del_moves").status == sxUnknown
  test "del of fully written elements":
    check verdict(unDelWritten, "bq_un_del_written").status == sxUnsat
  test "an added element is written":
    let r = verdict(unAdd, "bq_un_add")
    check r.status == sxSat
    check r.errors.len == 0
  test "pop of a written element":
    check verdict(unPop, "bq_un_pop").status == sxUnsat
  test "pop of an unwritten element":
    check verdict(unPopUnwritten, "bq_un_pop_unwritten").status == sxUnknown
  test "a seq returned by a call keeps its unwritten elements":
    let r = verdict(unReturnWritten, "bq_un_return_written")
    check r.status == sxSat
    check r.errors.len == 0
    check verdict(unReturnUnwritten, "bq_un_return_unwritten").status == sxUnknown
  test "a loop writes every element":
    check verdict(unLoopFill, "bq_un_loop_fill").status == sxUnsat
  test "an element assignment's index check is not a read":
    let r = verdict(unField, "bq_un_field")
    check r.status == sxSat
    check r.errors.len == 0
  test "an augmented assignment reads the element":
    check verdict(unAugUnwritten, "bq_un_aug_unwritten").status == sxUnknown
    let r = verdict(unAugWritten, "bq_un_aug_written")
    check r.status == sxSat
    check r.errors.len == 0
