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

# ---- item 1: a huge length is not an allocation that succeeds ---------------

proc hugeNewSeq(n: int) =
  if n < 0: return
  let xs = newSeq[int](n)
  if n > 2_000_000 and xs.len == n:
    symexTarget("bq_huge_newseq")

proc hugeNewSeqEdge(n: int) =
  if n < 0: return
  # 2^20 itself is modelled; the control.
  let xs = newSeq[int](n)
  if n == 1_048_576 and xs.len == n:
    symexTarget("bq_huge_newseq_edge")

proc hugeNewSeqLit() =
  let xs = newSeq[int](3_000_000)
  if xs.len == 3_000_000:
    symexTarget("bq_huge_newseq_lit")

proc hugeNewSeqStmt(n: int) =
  if n < 0: return
  var xs: seq[int]
  newSeq(xs, n)
  if n > 1_048_576 and xs.len > 0:
    symexTarget("bq_huge_newseq_stmt")

proc hugeOfCap(n: int) =
  if n < 0: return
  var xs = newSeqOfCap[int](n)
  xs.add 1
  if n > 1_048_576 and xs.len == 1:
    symexTarget("bq_huge_ofcap")

proc hugeUninit(n: int) =
  if n < 0: return
  let xs = newSeqUninit[int](n)
  if n > 1_048_576 and xs.len == n:
    symexTarget("bq_huge_uninit")

proc hugeBoundedDead(n: int) =
  # The guard's decline sits on an arm no execution takes here.
  if n < 0 or n > 50: return
  let xs = newSeqUninit[int](n)
  if xs.len > 50: symexTarget("bq_huge_bounded_dead")

proc hugeNegStill(n: int) =
  # The negative length still raises, unaffected by the decline.
  try:
    discard newSeq[int](n)
  except RangeDefect:
    if n == -3: symexTarget("bq_huge_neg_still")

proc hugeOtherPath(n, k: int) =
  if n < 0: return
  # The decline is scoped to the huge path: a target on a path that never
  # allocates more than 2^20 stays decided.
  if k == 1:
    discard newSeq[int](n)
  elif k == 2 and n == 7:
    symexTarget("bq_huge_other_path")

# ---- item 3: a Regex value is a constructor call ----------------------------

proc reLetRejected(s: string) =
  try:
    let r = re"(ab"
    if s.match(r): discard
  except RegexError:
    symexTarget("bq_re_let_rejected")

proc reLetRejectedAfter(s: string) =
  # Nothing after the constructor runs.
  try:
    let r = re"(ab"
    symexTarget("bq_re_let_rejected_after")
    discard s.match(r)
  except RegexError: discard

proc reCallRejected(s: string) =
  try:
    let r = re("(ab")
    discard s.match(r)
  except ValueError:
    symexTarget("bq_re_call_rejected")

proc reRexRejected() =
  try:
    discard rex"a)"
  except RegexError:
    symexTarget("bq_re_rex_rejected")

proc reLetValid(s: string) =
  let r = re"ab"
  if s.len == 2 and s.match(r):
    symexTarget("bq_re_let_valid")

proc reLetValidNo(s: string) =
  let r = re"ab"
  if s.len == 2 and s.match(r) and s[0] != 'a':
    symexTarget("bq_re_let_valid_no")

proc reValidNotNil() =
  let r = re"ab"
  if r == nil:
    symexTarget("bq_re_valid_not_nil")

proc reValidRaises() =
  try:
    discard re"a+b"
  except RegexError:
    symexTarget("bq_re_valid_raises")

proc reValueVar(s, p: string) =
  try:
    let r = re(p)
    if s.match(r): symexTarget("bq_re_value_var")
  except RegexError: discard

# ---- item 2: builtin set values ----------------------------------------------

type E4 = enum e0, e1, e2, e3
const tinySeqBudget = SymexSettings(budget: ResourceBudget(seqQueryRLimit: 1'u))
type Holder = object
  cs: set[char]
  n: int

proc bsParamMember(s: set[char]; c: char) =
  if c in s and c == 'q' and card(s) == 1:
    symexTarget("bq_bs_param_member")

proc bsInclMember(s: set[char]; c: char) =
  var u = s
  u.incl c
  if c notin u:
    symexTarget("bq_bs_incl_member")

proc bsExclMember(s: set[char]; c: char) =
  var u = s
  excl(u, c)
  if c in u:
    symexTarget("bq_bs_excl_member")

proc bsInclOther(s: set[E4]; e: E4) =
  # `incl` adds exactly one member. (Over `set[char]` the count query is a
  # 256-bit pigeonhole: bounded by `seqQueryRLimit`, see `bsCardBounded`.)
  var u = s
  u.incl e
  if card(u) > card(s) + 1 or (e in s and u != s):
    symexTarget("bq_bs_incl_other")

proc bsCardBounded(s: set[char]) =
  if card(s) == 3:
    symexTarget("bq_bs_card_bounded")

proc bsUnion(s, t: set[char]; c: char) =
  if c in s + t and c notin s and c notin t:
    symexTarget("bq_bs_union")

proc bsDiff(s, t: set[char]; c: char) =
  if c in s - t and c in t:
    symexTarget("bq_bs_diff")

proc bsInter(s, t: set[char]; c: char) =
  if c in s * t and c notin s:
    symexTarget("bq_bs_inter")

proc bsInterSat(s, t: set[char]) =
  if 'z' in s * t and card(s) == 1 and card(t) == 2:
    symexTarget("bq_bs_inter_sat")

proc bsSubset(s, t: set[char]; c: char) =
  if s <= t and c in s and c notin t:
    symexTarget("bq_bs_subset")

proc bsProper(s, t: set[char]) =
  if s < t and s == t:
    symexTarget("bq_bs_proper")

proc bsProperSat(s, t: set[char]) =
  if s < t and card(s) == 2 and t >= s and t != s:
    symexTarget("bq_bs_proper_sat")

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


suite "S8bq: walker version":
  test "the walker version floor":
    check parseInt(symexWalkerVersion) >= 220

suite "S8bq (1): a length above 2^20 is declined, not modelled as allocated":
  test "newSeq above 2^20 declines, scoped":
    let r = verdict(hugeNewSeq, "bq_huge_newseq")
    check r.status == sxUnknown
    check r.errors.hasMsg(feUnsupportedOp,
      "`newSeq` with a length above 1048576 is not modelled")
  test "control: a length of exactly 2^20 is modelled":
    check verdict(hugeNewSeqEdge, "bq_huge_newseq_edge").status == sxSat
  test "a literal length above 2^20 declines":
    let r = verdict(hugeNewSeqLit, "bq_huge_newseq_lit")
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedOp)
  test "the statement newSeq(s, n) above 2^20 declines":
    check verdict(hugeNewSeqStmt, "bq_huge_newseq_stmt").status == sxUnknown
  test "newSeqOfCap above 2^20 declines":
    let r = verdict(hugeOfCap, "bq_huge_ofcap")
    check r.status == sxUnknown
    check r.errors.hasMsg(feUnsupportedOp,
      "`newSeqOfCap` with a length above 1048576 is not modelled")
  test "newSeqUninit above 2^20 declines":
    let r = verdict(hugeUninit, "bq_huge_uninit")
    check r.status == sxUnknown
    check r.errors.hasMsg(feUnsupportedOp,
      "`newSeqUninit` with a length above 1048576 is not modelled")
  test "a bounded length never reaches the decline (the arm is dropped)":
    check verdict(hugeBoundedDead, "bq_huge_bounded_dead").status == sxUnsat
  test "a negative length still raises RangeDefect":
    check verdict(hugeNegStill, "bq_huge_neg_still").status == sxSat
  test "the decline is scoped to its path":
    check verdict(hugeOtherPath, "bq_huge_other_path").status == sxSat

suite "S8bq (3): a Regex value is a constructor call":
  test "a rejected literal bound by let raises RegexError":
    let r = verdict(reLetRejected, "bq_re_let_rejected")
    check r.status == sxSat
    check r.errors.len == 0
  test "nothing after a rejected constructor runs":
    check verdict(reLetRejectedAfter, "bq_re_let_rejected_after").status == sxUnsat
  test "the call form re(\"(ab\") raises":
    check verdict(reCallRejected, "bq_re_call_rejected").status == sxSat
  test "rex with a rejected pattern raises":
    check verdict(reRexRejected, "bq_re_rex_rejected").status == sxSat
  test "a valid literal bound by let is the literal at a regex call":
    let r = verdict(reLetValid, "bq_re_let_valid")
    check r.status == sxSat
    check r.errors.len == 0
    check verdict(reLetValidNo, "bq_re_let_valid_no").status == sxUnsat
  test "a valid Regex is not nil":
    check verdict(reValidNotNil, "bq_re_valid_not_nil").status == sxUnsat
  test "a valid pattern does not raise":
    check verdict(reValidRaises, "bq_re_valid_raises").status == sxUnsat
  test "a pattern that is not a literal declines, classified":
    let r = verdict(reValueVar, "bq_re_value_var")
    check r.status == sxUnknown
    check r.errors.hasKind(seUnsupportedRegex)

suite "S8bq (2): builtin set values":
  test "a set[char] parameter's members":
    let r = verdict(bsParamMember, "bq_bs_param_member")
    check r.status == sxSat
    check r.errors.len == 0
    check $r.witness == "({'q'}, 'q')"
  test "incl adds the element":
    check verdict(bsInclMember, "bq_bs_incl_member").status == sxUnsat
  test "excl removes the element":
    check verdict(bsExclMember, "bq_bs_excl_member").status == sxUnsat
  test "incl adds exactly one member":
    check verdict(bsInclOther, "bq_bs_incl_other").status == sxUnsat
  test "+ is the union":
    check verdict(bsUnion, "bq_bs_union").status == sxUnsat
  test "- is the difference":
    check verdict(bsDiff, "bq_bs_diff").status == sxUnsat
  test "* is the intersection":
    check verdict(bsInter, "bq_bs_inter").status == sxUnsat
    check verdict(bsInterSat, "bq_bs_inter_sat").status == sxSat
  test "<= is the subset":
    check verdict(bsSubset, "bq_bs_subset").status == sxUnsat
  test "< is a proper subset; >= and != too":
    check verdict(bsProper, "bq_bs_proper").status == sxUnsat
    check verdict(bsProperSat, "bq_bs_proper_sat").status == sxSat
  test "a query counting a set's members runs under seqQueryRLimit":
    let r = symexFind(bsCardBounded, tLabel("bq_bs_card_bounded"),
                      tinySeqBudget)
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasMsg(beSolverUndef, "counts a builtin set's members")
    check verdict(bsCardBounded, "bq_bs_card_bounded").status == sxSat
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
