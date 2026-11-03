## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 2 of 6 of this suite, with
## `tsymex_rfc0005_s8ar_remainder`, `tsymex_rfc0005_s8ar_remainder_c`,
## `tsymex_rfc0005_s8ar_remainder_d`, `tsymex_rfc0005_s8ar_remainder_e`,
## `tsymex_rfc0005_s8ar_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 120 s).

import std/[unittest, strutils, sequtils, tables, sets]
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

proc iMid(v: int, i: int) =
  if i < 0 or i > 3: return
  var s = @[10, 20, 30]
  s.insert(v, i)
  # `v` neither 10 nor 20: `i == 1` is then the only way in (RFC-0005 S8bp:
  # `v = 10, i = 0` and `v = 20, i = 2` satisfy the rest too, and Z3 4.13.4
  # returned the first once every search ran in a context of its own).
  if v != 10 and v != 20 and s.len == 4 and s[1] == v and s[2] == 20 and
     s[0] == 10 and s[3] == 30:
    symexTarget("i_mid")
  if s.len != 4: symexTarget("i_len_dead")
  if i == 1 and s[2] != 20: symexTarget("i_shift_dead")

proc iEnd(v: int) =
  var s = @[1, 2]
  s.insert(v, s.len)
  if s[2] == v and s[0] == 1 and s[1] == 2: symexTarget("i_end")
  if s[2] != v: symexTarget("i_end_dead")

proc iDefault(v: int) =
  var s = @[5]
  s.insert(v)
  if s[0] == v and s[1] == 5: symexTarget("i_front")

proc iRange(i: int) =
  var s = @[1, 2, 3]
  try:
    s.insert(9, i)
  except RangeDefect:
    if s.len == 3: symexTarget("i_range")
    if s.len != 3: symexTarget("i_range_dead")
  except IndexDefect:
    if s.len == 4 and s[3] == 0: symexTarget("i_index_grown")
    if s.len != 4 or s[3] != 0: symexTarget("i_index_dead")

proc iStr(a: string, i: int) =
  var s = @["x", "y"]
  s.insert(a, i)
  if s[0] == "x" and s[1] == "q" and s[2] == "y": symexTarget("i_str")

type
  IHolder = object
    s: seq[int]
  IRefHolder = ref object
    s: seq[int]

proc iDot(v: int) =
  var o = IHolder(s: @[1, 2])
  o.s.insert(v, 1)
  if o.s.len == 3 and o.s[1] == v and o.s[2] == 2: symexTarget("i_dot")
  if o.s.len != 3: symexTarget("i_dot_dead")

proc iRef(p: IRefHolder, v: int) =
  if p == nil: return
  let n0 = p.s.len
  p.s.insert(v, 0)
  if p.s.len == n0 + 1 and p.s[0] == v and n0 == 1 and p.s[1] == 7:
    symexTarget("i_ref")
  if p.s.len != n0 + 1: symexTarget("i_ref_dead")

proc iRefIdx(p: IRefHolder) =
  if p == nil: return
  try:
    p.s.insert(4, 3)
  except IndexDefect:
    if p.s.len == 3 and p.s[2] == 0: symexTarget("i_ref_grown")

suite "S8ar (3): insert on a plain seq and on dotted fields":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "insert in the middle shifts the tail":
    let r = run(iMid, "i_mid", sxSat)
    if r.status == sxSat:
      check r.witness[1] == 1
      check reproduces(iMid(r.witness[0], r.witness[1]), "i_mid")
    discard run(iMid, "i_len_dead", sxUnsat)
    discard run(iMid, "i_shift_dead", sxUnsat)

  test "insert at len appends; the argument reads the seq at the call":
    discard run(iEnd, "i_end", sxSat)
    discard run(iEnd, "i_end_dead", sxUnsat)

  test "the default index is 0":
    discard run(iDefault, "i_front", sxSat)

  test "a negative index raises RangeDefect before any change":
    let r = run(iRange, "i_range", sxSat)
    if r.status == sxSat:
      check r.witness[0] < 0
      check reproduces(iRange(r.witness[0]), "i_range")
    discard run(iRange, "i_range_dead", sxUnsat)

  test "an index past len raises IndexDefect after the seq has grown":
    let r = run(iRange, "i_index_grown", sxSat)
    if r.status == sxSat:
      check r.witness[0] > 3
      check reproduces(iRange(r.witness[0]), "i_index_grown")
    discard run(iRange, "i_index_dead", sxUnsat)

  test "a seq[string]":
    let r = run(iStr, "i_str", sxSat)
    if r.status == sxSat:
      check r.witness[0] == "q" and r.witness[1] == 1

  test "a value-object field":
    discard run(iDot, "i_dot", sxSat)
    discard run(iDot, "i_dot_dead", sxUnsat)

  test "a ref-object field":
    let r = run(iRef, "i_ref", sxSat)
    if r.status == sxSat:
      check reproduces(iRef(r.witness[0], r.witness[1]), "i_ref")
    discard run(iRef, "i_ref_dead", sxUnsat)

  test "a ref-object field's IndexDefect sees the grown field":
    let r = run(iRefIdx, "i_ref_grown", sxSat)
    if r.status == sxSat:
      check reproduces(iRefIdx(r.witness[0]), "i_ref_grown")
