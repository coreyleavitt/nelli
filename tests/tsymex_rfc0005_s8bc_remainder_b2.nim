## RFC-0005 (soundness channels) slice S8bc -- S8at's "Different mechanisms,
## reported and not fixed here" remainder, part b: array-element insert, newSeq, mgetOrPut and inc / dec / += on an element
## (items 4, 5, 7).
## RFC-0005 S8bl (item 5): split out of `tsymex_rfc0005_s8bc_remainder`,
## whose compile alone took 77 s on the Windows leg (budget: 60 s a file).
##
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8bc_remainder_b`, `tsymex_rfc0005_s8bc_remainder_b3`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 74 s).

import std/[unittest, strutils, sequtils, tables, sets, hashes]
import nelli
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template reproduces(call: untyped; label: string): bool =
  block:
    symexCaptureBegin()
    call
    let hits = symexCaptureEnd()
    label in hits

# ---- (5) newSeq ---------------------------------------------------------------
#
# RFC-0005 S8bc: `newSeq[T](n)` / `newSeq(s, n)` is `n` zero elements; a
# negative `n` raises `RangeDefect` (the `Natural` parameter); a length above
# 2^20 declines, scoped to its path. The stdlib body was walked and declined
# (an unsupported `when`, the payload cast).

proc nsLen(n: int) =
  if n < 0 or n > 50: return
  let s = newSeq[int](n)
  if s.len == 3 and s[2] == 0 and s[0] == 0: symexTarget("ns_len")
  if s.len == 3 and s[1] != 0: symexTarget("ns_zero_dead")
  if s.len != n and n >= 0: symexTarget("ns_len_dead")

proc nsRange(n: int) =
  try:
    let s = newSeq[int](n)
    if s.len < 0: symexTarget("ns_range_dead")
  except RangeDefect:
    if n < 0: symexTarget("ns_range")
    if n >= 0: symexTarget("ns_range_dead2")

proc nsHuge(n: int) =
  if n == 7: symexTarget("ns_small")
  if n < 0: return
  let s = newSeq[bool](n)
  if s.len == 2_000_000: symexTarget("ns_huge")

proc nsVar(n: int) =
  if n < 1 or n > 9: return
  var s: seq[string]
  newSeq(s, n)
  s[n - 1] = "x"
  if s.len == 4 and s[3] == "x" and s[0] == "": symexTarget("ns_var")
  if s.len == 4 and s[2] != "": symexTarget("ns_var_dead")

proc nsWrite(i: int) =
  var s = newSeq[int8]()
  s.add 3
  var t = newSeq[int8](3)
  t[i] = 5
  if t[0] == 5 and s[0] == 3 and t[1] == 0 and t.len == 3: symexTarget("ns_write")

proc itBound(n: int) =
  # `initTable`'s own size guard (S8at), behind a bound: its decline arm is
  # infeasible here, so it is dropped, not walked into a taint.
  if n < 0 or n > 9: return
  var t = initTable[int, int](n)
  t[1] = 2
  if t.len != 1: symexTarget("it_bound_dead")

suite "S8bc (5): newSeq":
  test "a scoped decline on an infeasible arm does not taint":
    let d = symexFind(itBound, tLabel("it_bound_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let n = symexFind(nsLen, tLabel("ns_len_dead"))
    checkpoint $n.status & " " & show(n.errors)
    check n.status == sxUnsat


  test "newSeq[T](n) is n zero elements":
    let r = symexFind(nsLen, tLabel("ns_len"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 3
      check reproduces(nsLen(r.witness[0]), "ns_len")
    let d = symexFind(nsLen, tLabel("ns_zero_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat
    let d2 = symexFind(nsLen, tLabel("ns_len_dead"))
    checkpoint $d2.status & " " & show(d2.errors)
    check d2.status == sxUnsat

  test "a negative length raises RangeDefect":
    let r = symexFind(nsRange, tLabel("ns_range"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(nsRange(r.witness[0]), "ns_range")
    # A length above 2^20 is the declined path, so this dead label is
    # sxUnknown, not sxUnsat: the decline must never be a false sxUnsat.
    let d = symexFind(nsRange, tLabel("ns_range_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnknown
    check d.errors.hasKind(feUnsupportedOp)
    check not d.errors.hasKind(weInternalWalkerFault)
    let d2 = symexFind(nsRange, tLabel("ns_range_dead2"))
    checkpoint $d2.status & " " & show(d2.errors)
    check d2.status in {sxUnsat, sxUnknown}
    check not d2.errors.hasKind(weInternalWalkerFault)

  test "a length above the bound declines, scoped":
    # The label before the call is found; the one past the 2^20 bound is
    # an honest sxUnknown, never a false sxUnsat.
    let r = symexFind(nsHuge, tLabel("ns_small"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let h = symexFind(nsHuge, tLabel("ns_huge"))
    checkpoint $h.status & " " & show(h.errors)
    check h.status == sxUnknown
    check h.errors.hasKind(feUnsupportedOp)

  test "newSeq(s, n) on a seq[string]":
    let r = symexFind(nsVar, tLabel("ns_var"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 4
      check reproduces(nsVar(r.witness[0]), "ns_var")
    let d = symexFind(nsVar, tLabel("ns_var_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "newSeq[int8]() and a write into newSeq[int8](3)":
    let r = symexFind(nsWrite, tLabel("ns_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 0
      check reproduces(nsWrite(r.witness[0]), "ns_write")
