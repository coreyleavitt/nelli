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

type
  TabHolder = ref object
    ti: Table[int, int]
    ts: Table[string, string]
    tf: Table[string, float]
    tb: Table[bool, int8]
  BadTab = ref object
    tq: Table[string, seq[int]]
    n: int
  OddHolder = ref object
    hs: HashSet[string]
    bad: Table[string, (int, int)]   ## RFC-0005 S8at: was `seq[int]`, now backed
    n: int

proc tIntKey(t: Table[int, int]) =
  if t.hasKey(3) and t[3] == 7 and t.len == 1: symexTarget("t_intkey")

proc tStrVal(t: Table[string, string]) =
  if "a" in t and t["a"] == "xy": symexTarget("t_strval")

proc tFloatVal(t: Table[string, float]) =
  if "a" in t and t["a"] > 1.5: symexTarget("t_floatval")

proc tLocal(v: string) =
  var t: Table[int8, string]
  t[-1] = v
  t[4] = "z"
  if t[-1] == "q" and t.len == 2: symexTarget("t_local")
  if t.len != 2: symexTarget("t_local_len_dead")
  t.del(-1)
  if -1'i8 in t: symexTarget("t_local_del_dead")
  if t.len == 1 and t[4] == "z": symexTarget("t_local_del")

proc tHeap(p: TabHolder) =
  if p == nil: return
  if 2 in p.ti and p.ti[2] == -5 and "k" in p.ts and p.ts["k"] == "v" and
     "f" in p.tf and p.tf["f"] == 0.5 and true in p.tb and p.tb[true] == -3:
    symexTarget("t_heap")

proc tHeapWrite(p: TabHolder, v: int) =
  if p == nil: return
  p.ti[v] = 1
  if p.ti[v] != 1: symexTarget("t_heap_write_dead")
  if p.ti.len == 0: symexTarget("t_heap_write_len_dead")

proc tBad(p: BadTab) =
  if p != nil and p.tq.len == 1: symexTarget("t_bad")

proc tOdd(p: OddHolder) =
  if p != nil and p.n == 9: symexTarget("t_odd")

suite "S8ar (5, 9): every backed Table key and value type, rendered":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "an int key":
    let r = run(tIntKey, "t_intkey", sxSat)
    if r.status == sxSat: check reproduces(tIntKey(r.witness[0]), "t_intkey")

  test "a string value":
    let r = run(tStrVal, "t_strval", sxSat)
    if r.status == sxSat: check reproduces(tStrVal(r.witness[0]), "t_strval")

  test "a float value":
    let r = run(tFloatVal, "t_floatval", sxSat)
    if r.status == sxSat: check reproduces(tFloatVal(r.witness[0]), "t_floatval")

  test "a local Table[int8, string]: set, del, len":
    let r = run(tLocal, "t_local", sxSat)
    if r.status == sxSat: check reproduces(tLocal(r.witness[0]), "t_local")
    discard run(tLocal, "t_local_len_dead", sxUnsat)
    discard run(tLocal, "t_local_del_dead", sxUnsat)
    discard run(tLocal, "t_local_del", sxSat)

  test "Table fields of a ref render every backed value type":
    let r = run(tHeap, "t_heap", sxSat)
    if r.status == sxSat: check reproduces(tHeap(r.witness[0]), "t_heap")

  test "a write to an int-keyed Table field":
    discard run(tHeapWrite, "t_heap_write_dead", sxUnsat)
    discard run(tHeapWrite, "t_heap_write_len_dead", sxUnsat)

  test "a Table whose value is a container is modelled (RFC-0005 S8at)":
    # Pinned a scoped decline until RFC-0005 S8at held a container value
    # leaf-split (`tvTree`); it is now exact and renders.
    let r = run(tBad, "t_bad", sxSat)
    check r.errors.len == 0
    if r.status == sxSat: check reproduces(tBad(r.witness[0]), "t_bad")

suite "S8ar (7): a container a ref pointee holds no longer demotes the parameter":
  test "a HashSet[string] and an unbacked Table field beside an int field":
    let r = symexFind(tOdd, tLabel("t_odd"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedWitnessType)
    if r.status == sxSat: check reproduces(tOdd(r.witness[0]), "t_odd")

type
  Sub = object
    x: int
  Inner = object
    s: seq[int]
    a: int
    t: Table[string, int]
    sub: Sub
  Outer = ref object
    inner: Inner

proc dAdd(p: Outer, v: int) =
  if p == nil: return
  let n = p.inner.s.len
  p.inner.s.add v
  if p.inner.s.len != n + 1: symexTarget("d_add_len_dead")
  if p.inner.s[n] != v: symexTarget("d_add_elem_dead")
  if v == 5 and p.inner.a == 3 and n == 2: symexTarget("d_add")

proc dAsg(p: Outer, v: int) =
  if p == nil or v < -100 or v > 100: return
  p.inner.a = v
  p.inner.a += 1
  p.inner.sub.x = v * 2
  if p.inner.a != v + 1: symexTarget("d_asg_dead")
  if p.inner.sub.x != v * 2: symexTarget("d_sub_dead")
  if p.inner.a == 8: symexTarget("d_asg")

proc dIdx(p: Outer) =
  if p == nil or p.inner.s.len == 0: return
  p.inner.s[0] = 9
  if p.inner.s[0] != 9: symexTarget("d_idx_dead")
  symexTarget("d_idx")

proc dIdxRaise(p: Outer) =
  if p == nil: return
  p.inner.s[0] = 9

proc dTab(p: Outer) =
  if p == nil: return
  p.inner.t["k"] = 4
  if p.inner.t["k"] != 4: symexTarget("d_tab_dead")
  symexTarget("d_tab")

proc dAlias(p: Outer) =
  if p == nil: return
  let q = p
  let n = q.inner.s.len
  p.inner.s.insert(7, 0)
  if q.inner.s.len != n + 1 or q.inner.s[0] != 7: symexTarget("d_alias_dead")

suite "S8ar (4): a value chain rooted at a ref object's field":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(feUnsupportedStmtKind)
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "p.inner.s.add v":
    discard run(dAdd, "d_add_len_dead", sxUnsat)
    discard run(dAdd, "d_add_elem_dead", sxUnsat)
    let r = run(dAdd, "d_add", sxSat)
    if r.status == sxSat:
      check reproduces(dAdd(r.witness[0], r.witness[1]), "d_add")

  test "p.inner.a = v, p.inner.a += 1, p.inner.sub.x = v":
    discard run(dAsg, "d_asg_dead", sxUnsat)
    discard run(dAsg, "d_sub_dead", sxUnsat)
    let r = run(dAsg, "d_asg", sxSat)
    if r.status == sxSat:
      check reproduces(dAsg(r.witness[0], r.witness[1]), "d_asg")

  test "p.inner.s[0] = v forks its IndexDefect":
    discard run(dIdx, "d_idx_dead", sxUnsat)
    let r = run(dIdx, "d_idx", sxSat)
    if r.status == sxSat: check reproduces(dIdx(r.witness[0]), "d_idx")
    let ex = symexFind(dIdxRaise, tRaisedExn("IndexDefect"))
    checkpoint $ex.status & " " & show(ex.errors)
    check ex.status == sxRaised
    if ex.status == sxRaised:
      check ex.raisedWitness[0] != nil and ex.raisedWitness[0].inner.s.len == 0

  test "p.inner.t[k] = v":
    discard run(dTab, "d_tab_dead", sxUnsat)
    discard run(dTab, "d_tab", sxSat)

  test "an alias sees the write":
    discard run(dAlias, "d_alias_dead", sxUnsat)

type
  WKind = enum wkA, wkB
  WVar = ref object
    case kind: WKind
    of wkA: xs: seq[int]
    of wkB: hs: HashSet[int8]
  WHolder = ref object
    tp: (seq[int], int)
    a2: array[2, seq[int]]
    tt: Table[int, int]
    hs: HashSet[int8]
  ByValVar = object
    case kind: WKind
    of wkA: a: int
    of wkB: b: bool
  DSeq = distinct seq[int]
  DeclHolder = ref object
    bv: ByValVar
    n: int
  DeclHolder2 = ref object
    ds: DSeq
    n: int

proc wfTree(p: WHolder) =
  if p == nil: return
  if p.tp[0].len < 0 or p.tp[0].len > 1024: symexTarget("wf_tp_dead")
  if p.a2[1].len < 0: symexTarget("wf_a2_dead")
  if p.tt.len == 0 and 3 in p.tt: symexTarget("wf_tt_dead")
  if p.hs.len > 256: symexTarget("wf_hs_dead")
  if p.tp[0].len == 2 and p.a2[1].len == 1 and 3 in p.tt and p.hs.len == 256:
    symexTarget("wf_tree")

proc wfArm(p: WVar) =
  if p == nil: return
  if p.kind == wkA and p.xs.len < 0: symexTarget("wf_arm_dead")
  if p.kind == wkB and p.hs.len > 256: symexTarget("wf_arm_set_dead")
  if p.kind == wkA and p.xs.len == 3: symexTarget("wf_arm")

proc wfWritten(p: WHolder, v: int) =
  if p == nil: return
  p.tp = (@[v], 1)
  if p.tp[0].len != 1: symexTarget("wf_written_dead")

proc declBV(p: DeclHolder) =
  if p != nil and p.n == 1: symexTarget("decl_bv")

proc declBVRead(p: DeclHolder) =
  if p != nil and p.bv.kind == wkB: symexTarget("decl_bv_read")

proc declDS(p: DeclHolder2) =
  if p != nil and p.n == 1: symexTarget("decl_ds")

proc declDSRead(p: DeclHolder2) =
  if p == nil: return
  let d = p.ds
  if p.n == 2: symexTarget("decl_ds_read")

proc declDSWrite(p: DeclHolder2) =
  if p == nil: return
  p.ds = DSeq(@[1])
  if p.n == 2: symexTarget("decl_ds_write")

type
  DeclHolder3 = ref object
    tc: (int, ByValVar)
    n: int

proc declTC(p: DeclHolder3) =
  if p != nil and p.n == 1: symexTarget("decl_tc")

proc declTCRead(p: DeclHolder3) =
  if p == nil: return
  let t = p.tc
  if p.n == 2: symexTarget("decl_tc_read")

proc declU8(t: Table[uint8, int]) =
  if 7'u8 in t and t[7'u8] == 3: symexTarget("decl_u8")

proc declChar(t: Table[char, string]) =
  if 'k' in t and t['k'] == "v": symexTarget("decl_char")

suite "S8ar (10): every read of a cell asserts its well-formedness":
  template run(fn: typed, lbl: string, want: SymexStatusKind): untyped =
    block:
      let r = symexFind(fn, tLabel(lbl))
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == want
      check not r.errors.hasKind(weInternalWalkerFault)
      r

  test "tree parts: a nested seq, an array of seqs, a cell-keyed Table, a HashSet":
    discard run(wfTree, "wf_tp_dead", sxUnsat)
    discard run(wfTree, "wf_a2_dead", sxUnsat)
    discard run(wfTree, "wf_tt_dead", sxUnsat)
    discard run(wfTree, "wf_hs_dead", sxUnsat)
    let r = run(wfTree, "wf_tree", sxSat)
    if r.status == sxSat: check reproduces(wfTree(r.witness[0]), "wf_tree")

  test "a ref variant's arm cells":
    discard run(wfArm, "wf_arm_dead", sxUnsat)
    discard run(wfArm, "wf_arm_set_dead", sxUnsat)
    let r = run(wfArm, "wf_arm", sxSat)
    if r.status == sxSat: check reproduces(wfArm(r.witness[0]), "wf_arm")

  test "a written cell is the value the program built":
    discard run(wfWritten, "wf_written_dead", sxUnsat)

suite "S8ar: the declines that remained (closed by RFC-0005 S8at)":
  test "a by-value case object field: the field, not the parameter":
    let r = symexFind(declBV, tLabel("decl_bv"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declBV(r.witness[0]), "decl_bv")
    # A scoped decline (`heUnsupportedPointeeRead`) until RFC-0005 S8at made
    # a by-value case object a tree-valued heap cell; the read is exact.
    let r2 = symexFind(declBVRead, tLabel("decl_bv_read"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    check r2.errors.len == 0
    if r2.status == sxSat:
      check reproduces(declBVRead(r2.witness[0]), "decl_bv_read")

  test "a distinct over a composite base: the field, not the parameter":
    let r = symexFind(declDS, tLabel("decl_ds"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declDS(r.witness[0]), "decl_ds")
    # A scoped decline (`heUnsupportedPointeeRead`) until RFC-0005 S8at held
    # a distinct over a composite base as its base's leaves; the read and the
    # store are exact.
    let r2 = symexFind(declDSRead, tLabel("decl_ds_read"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    # Only `geDistinctBijectivitySkipped`, a `sevHint`, remains.
    check not r2.errors.anyIt(it.severity == sevError)
    if r2.status == sxSat:
      check reproduces(declDSRead(r2.witness[0]), "decl_ds_read")
    let r3 = symexFind(declDSWrite, tLabel("decl_ds_write"))
    checkpoint $r3.status & " " & show(r3.errors)
    check r3.status == sxSat
    check not r3.errors.anyIt(it.severity == sevError)   # an ill-sorted store before S8ar
    if r3.status == sxSat:
      check reproduces(declDSWrite(r3.witness[0]), "decl_ds_write")

  test "a tuple holding a by-value case object: the field, not the parameter":
    let r = symexFind(declTC, tLabel("decl_tc"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declTC(r.witness[0]), "decl_tc")
    # The read was a havoc (`heUnsupportedPointeeRead`, replay-gated) until
    # RFC-0005 S8at made the case object a heap cell part; it is exact.
    let r2 = symexFind(declTCRead, tLabel("decl_tc_read"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    check r2.errors.len == 0
    if r2.status == sxSat:
      check reproduces(declTCRead(r2.witness[0]), "decl_tc_read")

  test "uint8- and char-keyed Table parameters render (S8am's isChar tells them apart)":
    let r = symexFind(declU8, tLabel("decl_u8"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(declU8(r.witness[0]), "decl_u8")
    let r2 = symexFind(declChar, tLabel("decl_char"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat: check reproduces(declChar(r2.witness[0]), "decl_char")

suite "S8ar: walker version floor":
  test "walker version floor >= 191":
    check parseInt(symexWalkerVersion) >= 191
