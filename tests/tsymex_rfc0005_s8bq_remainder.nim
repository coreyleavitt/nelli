## RFC-0005 (soundness channels) slice S8bq -- S8bi's remainder: the one
## soundness item and the four precision items S8bi reported and did not fix.
##
## Item 1: a `newSeq` / `newSeqOfCap` / `newSeqUninit` length above 2^20
## was modelled as an allocation that succeeds. A real run raises
## `OutOfMemDefect`, or not, depending on the host. The path is declined,
## scoped to it, exactly as S8bc declines `newSeq`'s (`iekSeqNewZero`).
import std/[unittest, strutils]
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
