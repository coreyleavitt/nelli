## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
##
## RFC-0005 S8cm: part 3 of 6 of this suite, with
## `tsymex_rfc0005_s8ar_remainder`, `tsymex_rfc0005_s8ar_remainder_b`,
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

type
  DNode = ref object
    a, b, c: int
    next: DNode
    kids: seq[DNode]

proc dMany(p: DNode) =
  if p == nil: return
  if p.a + p.b + p.c + p.a + p.b + p.c + p.a + p.b + p.c + p.a == 13 and
     p.b == 1 and p.c == 2:
    symexTarget("d_many")

proc dChain(p: DNode) =
  if p != nil and p.next != nil and p.next.next != nil and p.next.next.a == 3:
    symexTarget("d_chain")

proc dKid(p: DNode) =
  if p != nil and p.kids.len == 1 and p.kids[0] != nil and p.kids[0].a == 5:
    symexTarget("d_kid")

proc budget(n: int): SymexSettings =
  result = defaultSymexSettings()
  result.budget.maxHeapDepth = n

suite "S8ar (8): the heap-depth budget counts heap steps, not field reads":
  test "ten field reads of one parameter fit the default budget of 8":
    let r = symexFind(dMany, tLabel("d_many"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(heDepthExhausted)
    if r.status == sxSat:
      check reproduces(dMany(r.witness[0]), "d_many")

  test "a field three steps from the root needs a budget above 3":
    let r3 = symexFind(dChain, tLabel("d_chain"), budget(3))
    checkpoint $r3.status & " " & show(r3.errors)
    check r3.status == sxUnknown
    check r3.errors.hasKind(heDepthExhausted)
    let r4 = symexFind(dChain, tLabel("d_chain"), budget(4))
    checkpoint $r4.status & " " & show(r4.errors)
    check r4.status == sxSat
    if r4.status == sxSat:
      check reproduces(dChain(r4.witness[0]), "d_chain")

  test "a ref read out of a seq field is one step further from the root":
    let r2 = symexFind(dKid, tLabel("d_kid"), budget(2))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxUnknown
    check r2.errors.hasKind(heDepthExhausted)
    let r3 = symexFind(dKid, tLabel("d_kid"), budget(3))
    checkpoint $r3.status & " " & show(r3.errors)
    check r3.status == sxSat

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

proc fPt(p: FHolder) =
  if p != nil and p.pt.x == 3 and p.pt.y == p.pt.x + 1: symexTarget("f_pt")

proc fTup(p: FHolder) =
  if p != nil and p.tp[0] == 5 and p.tp[1]: symexTarget("f_tup")

proc fArr(p: FHolder) =
  if p != nil and p.arr[2] == 9 and p.arr[0] == -1: symexTarget("f_arr")

proc fDist(p: FHolder) =
  if p != nil and int(p.m) == 7: symexTarget("f_dist")

proc fNested(p: FHolder) =
  if p != nil and p.nested[0].y == 2 and p.nested[1] == 4: symexTarget("f_nested")

proc fNamed(p: FHolder) =
  if p != nil and p.nm.a == 1 and p.nm.s.len == 1 and p.nm.s[0] == '\xff':
    symexTarget("f_named")

suite "S8ar (5, 6): tuple, object, array and distinct fields of a heap cell":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "an object field":
    let r = run(fPt, "f_pt", sxSat)
    if r.status == sxSat: check reproduces(fPt(r.witness[0]), "f_pt")

  test "an anonymous tuple field":
    let r = run(fTup, "f_tup", sxSat)
    if r.status == sxSat: check reproduces(fTup(r.witness[0]), "f_tup")

  test "an array field":
    let r = run(fArr, "f_arr", sxSat)
    if r.status == sxSat: check reproduces(fArr(r.witness[0]), "f_arr")

  test "a distinct field":
    let r = run(fDist, "f_dist", sxSat)
    if r.status == sxSat: check reproduces(fDist(r.witness[0]), "f_dist")

  test "a tuple of an object and an int":
    let r = run(fNested, "f_nested", sxSat)
    if r.status == sxSat: check reproduces(fNested(r.witness[0]), "f_nested")

  test "a named tuple with a string part (its bytes are facts of the read)":
    let r = run(fNamed, "f_named", sxSat)
    if r.status == sxSat: check reproduces(fNamed(r.witness[0]), "f_named")
