## RFC-0005 (soundness channels) slice S8bi -- S8bb's remainder, part A:
## the soundness and crash items S8bb reported and did not fix.
##
## Item 1: every node that can raise counts as a raise site in
## `rhsHasInlineDefectFork`. A call through a closure, a `map`/`filter`
## over a closure, a borrowed arithmetic operator and a regex call were
## carriers only (their operands could raise, they could not), so in a
## `while` guard -- where `parseAtomicOperand` hoists nothing and the
## predicate is the only protection -- D1c's flat fast path lowered them
## whether or not the short circuit reached them: `b >= 0 and f(b)` forked
## `f`'s raise for `b < 0`, a false `sxSat`.
##
## Item 2: each raise carries only the facts of what was evaluated before
## it. A closure call's exit facts (its body did not raise) were appended
## to every raise of the expression, also those evaluated before the call:
## in `while ord(s[i]) + f(x) > 0` the `IndexDefect` was forked only with
## `x <= 5`, a false `sxUnsat`. And an operand left inline (`s[i]`) was
## evaluated after a later operand's hoisted `let`s.
##
## Item 3: `newSeq[T](n)`, `newSeq(s, n)`, `newSeqOfCap[T](n)` and
## `newSeqUninit[T](n)` aborted the compile ("node has no type").
##
## Item 4: `k in {..}` / `k notin {..}` over a set literal was
## `feUnsupportedExprKind` (nnkCurly).
##
## Item 5: every recursive Z3 definition carries a decreasing fuel bound
## (Z3 unfolds one without spending `rlimit`); a source scan pins it.
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8bi_remainder`, `tsymex_rfc0005_s8bi_remainder_c`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 76 s).

import std/[unittest, strutils, re, sequtils, os, tables]
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

proc onlyLengthDecline(errs: seq[SymexErrorInfo]): bool =
  ## RFC-0005 batch 5. Every error is S8bc's length decline
  ## (`parseNewSeqLen`): a length above 2^20 is not modelled, scoped.
  if errs.len == 0: return false
  for e in errs:
    if e.kind != feUnsupportedOp or "length above 1048576" notin e.msg:
      return false
  true

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

# ---- item 1: raise sites behind a while guard's short circuit ---------------

type M = distinct int
proc `==`(a, b: M): bool {.borrow.}

# ---- item 3: newSeq and friends ---------------------------------------------

proc nsLen(n: int) =
  let xs = newSeq[int](n)
  if xs.len == 3 and xs[1] == 0 and xs[2] == 0:
    symexTarget("bi_ns_len")

proc nsNonZero(n: int) =
  if n < 0: return
  let xs = newSeq[int](n)
  if xs.len > 2 and xs[2] != 0:
    symexTarget("bi_ns_nonzero")

proc nsNeg(n: int) =
  try:
    discard newSeq[int](n)
  except RangeDefect:
    if n == -4: symexTarget("bi_ns_neg")

proc nsNonNegRaise(n: int) =
  try:
    discard newSeq[int](n)
  except RangeDefect:
    if n >= 0: symexTarget("bi_ns_nonneg_raise")

proc nsIndex(n, i: int) =
  let xs = newSeq[int](n)
  try:
    discard xs[i]
  except IndexDefect:
    if n == 2 and i == 2: symexTarget("bi_ns_index")

proc nsStr(n: int) =
  var xs = newSeq[string](n)
  if n == 2:
    xs[1] = "q"
    if xs[0] == "" and xs[1] == "q": symexTarget("bi_ns_str")

proc nsVar(n: int) =
  var xs: seq[int]
  newSeq(xs, n)
  if xs.len == 4 and xs[3] == 0: symexTarget("bi_ns_var")

proc nsVarNeg(n: int) =
  var xs = @[1]
  try:
    newSeq(xs, n)
  except RangeDefect:
    if xs.len == 1 and n < 0: symexTarget("bi_ns_var_neg")

proc nsOfCap(n: int) =
  var xs = newSeqOfCap[int](n)
  xs.add 7
  if n == 50 and xs.len == 1 and xs[0] == 7: symexTarget("bi_ns_ofcap")

proc nsOfCapLen(n: int) =
  if n < 0: return
  let xs = newSeqOfCap[int](n)
  if xs.len != 0: symexTarget("bi_ns_ofcap_len")

proc nsOfCapNeg(n: int) =
  try:
    discard newSeqOfCap[int](n)
  except RangeDefect:
    symexTarget("bi_ns_ofcap_neg")

proc nsUninit(n: int) =
  let xs = newSeqUninit[int](n)
  if xs.len == 5: symexTarget("bi_ns_uninit")

proc nsTuple(n: int) =
  let xs = newSeq[(int, int)](n)
  if xs.len == 1: symexTarget("bi_ns_tuple")

# RFC-0005 batch 5: the unified lowering (S8bc's leaf split) backs a tuple
# element, and a length above 2^20 declines on its own path (S8bc's
# `parseNewSeqLen`). The bounded forms below are the S8bi pins with that
# path excluded, which stay decided.

proc nsTupleZero(n: int) =
  let xs = newSeq[(int, int)](n)
  if xs.len == 2 and xs[1][0] == 0 and xs[1][1] == 0:
    symexTarget("bi_ns_tuple_zero")

proc nsTupleNonZero(n: int) =
  if n < 0 or n > 1000: return
  let xs = newSeq[(int, int)](n)
  if xs.len > 1 and xs[1][1] != 0: symexTarget("bi_ns_tuple_nonzero")

proc nsNonZeroB(n: int) =
  if n < 0 or n > 1000: return
  let xs = newSeq[int](n)
  if xs.len > 2 and xs[2] != 0:
    symexTarget("bi_ns_nonzero_b")

proc nsNonNegRaiseB(n: int) =
  if n > 1000: return
  try:
    discard newSeq[int](n)
  except RangeDefect:
    if n >= 0: symexTarget("bi_ns_nonneg_raise_b")

proc nsOfCapLenB(n: int) =
  if n < 0 or n > 1000: return
  let xs = newSeqOfCap[int](n)
  if xs.len != 0: symexTarget("bi_ns_ofcap_len_b")

suite "S8bi (3): newSeq, newSeqOfCap, newSeqUninit":
  test "newSeq has length n and zero elements":
    let r = verdict(nsLen, "bi_ns_len")
    check r.status == sxSat
    check onlyLengthDecline(r.errors)   # batch 5: the n > 2^20 path only
  test "a newSeq element is never nonzero":
    let r = verdict(nsNonZero, "bi_ns_nonzero")
    check r.status == sxUnknown   # batch 5: the n > 2^20 path declines
    check onlyLengthDecline(r.errors)
    check verdict(nsNonZeroB, "bi_ns_nonzero_b").status == sxUnsat
  test "a negative length raises RangeDefect":
    check verdict(nsNeg, "bi_ns_neg").status == sxSat
  test "a non-negative length does not raise":
    let r = verdict(nsNonNegRaise, "bi_ns_nonneg_raise")
    check r.status == sxUnknown   # batch 5: the n > 2^20 path declines
    check onlyLengthDecline(r.errors)
    check verdict(nsNonNegRaiseB, "bi_ns_nonneg_raise_b").status == sxUnsat
  test "index n of a newSeq of length n raises IndexDefect":
    check verdict(nsIndex, "bi_ns_index").status == sxSat
  test "newSeq[string] elements are empty":
    check verdict(nsStr, "bi_ns_str").status == sxSat
  test "the statement newSeq(s, n)":
    check verdict(nsVar, "bi_ns_var").status == sxSat
  test "newSeq(s, n) raises before assigning":
    check verdict(nsVarNeg, "bi_ns_var_neg").status == sxSat
  test "newSeqOfCap is empty":
    check verdict(nsOfCap, "bi_ns_ofcap").status == sxSat
    let r = verdict(nsOfCapLen, "bi_ns_ofcap_len")
    check r.status == sxUnknown   # batch 5: the n > 2^20 path declines
    check onlyLengthDecline(r.errors)
    check verdict(nsOfCapLenB, "bi_ns_ofcap_len_b").status == sxUnsat
  test "newSeqOfCap range-checks its capacity":
    check verdict(nsOfCapNeg, "bi_ns_ofcap_neg").status == sxSat
  test "newSeqUninit has length n (RFC-0005 S8bq: no element read, no taint)":
    # S8bi tainted the whole path at the call (`feUnsupportedOpHavoc`);
    # S8bq taints only a read of an unwritten element, and this reads none.
    let r = verdict(nsUninit, "bi_ns_uninit")
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOpHavoc)
  test "a tuple element is backed (batch 5: S8bc's leaf split)":
    # S8bi pinned this as an unbacked-element decline; the unified lowering
    # builds one constant array per leaf (S8bc). Native: a newSeq of tuples
    # holds `(0, 0)` at every index.
    check newSeq[(int, int)](2) == @[(0, 0), (0, 0)]
    let r = verdict(nsTuple, "bi_ns_tuple")
    check r.status == sxSat
    check not r.errors.hasKind(seNestedSeqUnsupported)
    check verdict(nsTupleZero, "bi_ns_tuple_zero").status == sxSat
    check verdict(nsTupleNonZero, "bi_ns_tuple_nonzero").status == sxUnsat
