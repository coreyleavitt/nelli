## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 4 of 8 of this suite, with
## `tsymex_rfc0005_s8ar_remainder`, `tsymex_rfc0005_s8ar_remainder_b`,
## `tsymex_rfc0005_s8ar_remainder_c`, `tsymex_rfc0005_s8ar_remainder_g`,
## `tsymex_rfc0005_s8ar_remainder_e`, `tsymex_rfc0005_s8ar_remainder_h`,
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

type
  Meters = distinct int
  Pt = object
    x, y: int
  FHolder = ref object
    pt: Pt
    tp: (int, bool)
    arr: array[3, int]
    m: Meters
    nm: tuple[a: int, s: string]
    nested: (Pt, int)
  PtRef = ref Pt

proc fWrite(p: FHolder, v: int) =
  if p == nil: return
  p.pt = Pt(x: v, y: 2)
  p.tp = (v, true)
  p.m = Meters(v)
  if p.pt.x == 5 and p.pt.y == 2 and p.tp[1]: symexTarget("f_write")
  if p.pt.y != 2: symexTarget("f_write_dead")
  if p.tp[0] != v: symexTarget("f_write_tup_dead")
  if int(p.m) != v: symexTarget("f_write_dist_dead")

proc fAlias(a, b: FHolder) =
  if a == nil or b == nil: return
  a.pt = Pt(x: 1, y: 1)
  b.pt = Pt(x: 2, y: 2)
  if a.pt.x == 2: symexTarget("f_alias")
  if a.pt.x == 1 and b.pt.x == 1: symexTarget("f_alias_dead")

proc fZero() =
  let q = FHolder()
  if int(q.m) == 0 and q.pt.x == 0 and q.arr[1] == 0 and not q.tp[1] and
     q.nm.s.len == 0 and q.nested[0].y == 0:
    symexTarget("f_zero")
  if int(q.m) != 0: symexTarget("f_zero_dist_dead")
  if q.pt.y != 0: symexTarget("f_zero_pt_dead")
  if q.arr[2] != 0: symexTarget("f_zero_arr_dead")

proc fNewZero() =
  var q: FHolder
  new(q)
  if int(q.m) != 0: symexTarget("f_new_dist_dead")
  if int(q.m) == 0: symexTarget("f_new_dist")

proc fWhole(p: PtRef) =
  if p == nil: return
  p.x = 4
  if p[].x != 4: symexTarget("f_whole_read_dead")
  p[] = Pt(x: 2, y: 3)
  if p.y == 3 and p[].x == 2: symexTarget("f_whole_write")
  if p.y != 3: symexTarget("f_whole_write_dead")

proc fWholeIn(p: PtRef) =
  if p != nil and p[].x == 6 and p.y == 7: symexTarget("f_whole_in")


suite "S8ar (5, 6): tuple, object, array and distinct fields of a heap cell":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "writes of whole tree values":
    let r = run(fWrite, "f_write", sxSat)
    if r.status == sxSat:
      check reproduces(fWrite(r.witness[0], r.witness[1]), "f_write")
    discard run(fWrite, "f_write_dead", sxUnsat)
    discard run(fWrite, "f_write_tup_dead", sxUnsat)
    discard run(fWrite, "f_write_dist_dead", sxUnsat)

  test "two refs to one cell share its tree value":
    let r = run(fAlias, "f_alias", sxSat)
    if r.status == sxSat:
      check reproduces(fAlias(r.witness[0], r.witness[1]), "f_alias")
    discard run(fAlias, "f_alias_dead", sxUnsat)

  test "a constructed object zeroes every tree field; a distinct's zero is its base's":
    discard run(fZero, "f_zero", sxSat)
    discard run(fZero, "f_zero_dist_dead", sxUnsat)
    discard run(fZero, "f_zero_pt_dead", sxUnsat)
    discard run(fZero, "f_zero_arr_dead", sxUnsat)

  test "new(T) zeroes a distinct field":
    discard run(fNewZero, "f_new_dist", sxSat)
    discard run(fNewZero, "f_new_dist_dead", sxUnsat)

  test "p[] of an object reads and writes the field heaps":
    discard run(fWhole, "f_whole_read_dead", sxUnsat)
    discard run(fWhole, "f_whole_write", sxSat)
    discard run(fWhole, "f_whole_write_dead", sxUnsat)
    let r = run(fWholeIn, "f_whole_in", sxSat)
    if r.status == sxSat: check reproduces(fWholeIn(r.witness[0]), "f_whole_in")
