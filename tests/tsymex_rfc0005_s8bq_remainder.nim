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
