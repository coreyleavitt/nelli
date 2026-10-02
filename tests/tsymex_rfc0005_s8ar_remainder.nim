## RFC-0005 (soundness channels) slice S8ar -- S8ap's "Different mechanisms,
## reported and not fixed here" remainder.
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
  TNode = ref object
    kids: seq[TNode]
    v: int

  NObj = object
    kids: seq[NRef]
    v: int
  NRef = ref NObj
  VRec = object
    kids: seq[VRec]
    v: int

proc rKids(p: TNode) =
  if p != nil and p.kids.len == 2 and p.kids[1] != nil and p.kids[1].v == 3:
    symexTarget("r_kids")

proc rInd(p: NRef) =
  if p != nil and p.kids.len == 1 and p.kids[0] != nil and p.kids[0].v == 4:
    symexTarget("r_ind")

proc rVRec(p: VRec) =
  if p.v == 2: symexTarget("vrec_v")
  if p.kids.len == 1: symexTarget("vrec_kids")

suite "S8ar (1): a seq of the object's own ref type":
  test "classifies and is walked":
    let r = symexFind(rKids, tLabel("r_kids"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      check reproduces(rKids(r.witness[0]), "r_kids")

  test "a sym-indirection ref (NRef = ref NObj) through a seq field":
    let r = symexFind(rInd, tLabel("r_ind"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      check reproduces(rInd(r.witness[0]), "r_ind")

  test "a value object recurring through a seq declines scoped at the field":
    let r = symexFind(rVRec, tLabel("vrec_v"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let r2 = symexFind(rVRec, tLabel("vrec_kids"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxUnknown
    check not r2.errors.hasKind(weInternalWalkerFault)
    check r2.errors.anyIt("recursive value object" in it.msg or "seq[" in it.msg)

proc sAdd(v: string) =
  var s: seq[string]
  s.add v
  if s.len == 1 and s[0] == "q": symexTarget("s_add")
  if s.len != 1: symexTarget("s_add_dead")

proc sAddCmp(a, b: string) =
  var s = @[a]
  s.add b
  if s[0] == s[1] and a.len == 2: symexTarget("s_eq")

proc sParam(s: seq[string]) =
  if s.len == 2 and s[1] == "zz": symexTarget("s_param")

suite "S8ar (2): a plain seq[string] is modelled, never a walker fault":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "add then read":
    let r = run(sAdd, "s_add", sxSat)
    if r.status == sxSat: check r.witness[0] == "q"
    discard run(sAdd, "s_add_dead", sxUnsat)

  test "element equality after add":
    let r = run(sAddCmp, "s_eq", sxSat)
    if r.status == sxSat: check r.witness[0] == r.witness[1]

  test "a seq[string] param renders":
    let r = run(sParam, "s_param", sxSat)
    if r.status == sxSat:
      check r.witness[0].len == 2 and r.witness[0][1] == "zz"
      check reproduces(sParam(r.witness[0]), "s_param")

proc iMid(v: int, i: int) =
  if i < 0 or i > 3: return
  var s = @[10, 20, 30]
  s.insert(v, i)
  if s.len == 4 and s[1] == v and s[2] == 20 and s[0] == 10 and s[3] == 30:
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
