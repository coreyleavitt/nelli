## RFC-0005 (soundness channels) slice S8at -- S8ar's "Different mechanisms,
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

template replays(call: untyped; label: string) =
  ## The witness is typed (the parameter was not demoted) and replays.
  when compiles(call):
    check reproduces(call, label)
  else:
    checkpoint "the witness of `" & astToStr(call) & "` is not typed"
    check false

# ---- (2) `initTable[K, V]()` / `initHashSet[T]()` inside a SUT -------------

proc itPut(k, v: int) =
  var t = initTable[int, int]()
  t[k] = v
  if t[k] == 3 and t.len == 1: symexTarget("it_put")
  if t.len != 1: symexTarget("it_put_dead")

proc itEmpty(k: int) =
  let t = initTable[string, int]()
  if t.hasKey("a"): symexTarget("it_empty_dead")
  if t.len == 0 and k == 4: symexTarget("it_empty")

proc itSized(k: int) =
  var t = initTable[int, int](8)
  t[k] = 1
  if t.len == 1 and k == 9: symexTarget("it_sized")

proc itSymSize(n, k: int) =
  var t = initTable[int, int](n)
  t[k] = 1
  if t.len == 1 and k == 2: symexTarget("it_symsize")

proc itNeg(n: int) =
  try:
    let t = initTable[int, int](n)
    if t.len == 0: symexTarget("it_neg_ok")
  except RangeDefect:
    symexTarget("it_neg_raised")

proc itHuge(n: int) =
  if n > 2_000_000:
    let t = initTable[int, int](n)
    if t.len == 0: symexTarget("it_huge")

proc hsPut(k: int) =
  var s = initHashSet[int]()
  s.incl k
  if k in s and s.len == 1 and k == 5: symexTarget("hs_put")
  if s.len != 1: symexTarget("hs_put_dead")

proc mkOne[T](): T = T(1)

proc retOnlyGeneric(k: int) =
  let x = mkOne[int]()
  if x == 1 and k == 6: symexTarget("ret_only")
  if x != 1: symexTarget("ret_only_dead")

proc mkSeqOf[T](): seq[T] = newSeq[T]()

proc retOnlyNewSeq(k: int) =
  let s = mkSeqOf[int]()
  if s.len == 0 and k == 6: symexTarget("ret_newseq")

suite "S8at (2): initTable / initHashSet in a SUT":
  test "initTable[int, int]() then a store":
    let r = symexFind(itPut, tLabel("it_put"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(itPut(r.witness[0], r.witness[1]), "it_put")
    let d = symexFind(itPut, tLabel("it_put_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an initTable is empty":
    let r = symexFind(itEmpty, tLabel("it_empty"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(itEmpty, tLabel("it_empty_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a literal initial size":
    let r = symexFind(itSized, tLabel("it_sized"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(itSized(r.witness[0]), "it_sized")

  test "a symbolic initial size: a negative one raises RangeDefect":
    let r = symexFind(itNeg, tLabel("it_neg_raised"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] < 0
      check reproduces(itNeg(r.witness[0]), "it_neg_raised")
    let r2 = symexFind(itNeg, tLabel("it_neg_ok"))
    checkpoint $r2.status & " " & show(r2.errors)
    check r2.status == sxSat
    if r2.status == sxSat:
      check reproduces(itNeg(r2.witness[0]), "it_neg_ok")

  test "a symbolic initial size: a small one is modelled":
    let r = symexFind(itSymSize, tLabel("it_symsize"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(itSymSize(r.witness[0], r.witness[1]), "it_symsize")

  test "initHashSet[int]() then an incl":
    let r = symexFind(hsPut, tLabel("hs_put"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(hsPut(r.witness[0]), "hs_put")
    let d = symexFind(hsPut, tLabel("hs_put_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a generic bound only by its return type":
    let r = symexFind(retOnlyGeneric, tLabel("ret_only"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0] == 6
      check reproduces(retOnlyGeneric(r.witness[0]), "ret_only")
    let d = symexFind(retOnlyGeneric, tLabel("ret_only_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "newSeq through such a generic compiles, and is modelled":
    # S8at pinned `sxSat` or `sxUnknown`: `newSeq` had no model, its stdlib
    # body walked until the call-depth budget ran out. RFC-0005 S8bc
    # (item 5) models it (`iekSeqNewZero`).
    let r = symexFind(retOnlyNewSeq, tLabel("ret_newseq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)
    if r.status == sxSat:
      check reproduces(retOnlyNewSeq(r.witness[0]), "ret_newseq")

  test "an initial size above the modelled bound declines, scoped":
    let r = symexFind(itHuge, tLabel("it_huge"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.anyIt(it.kind == feUnsupportedOp and
                         "initial size above" in it.msg)
    check not r.errors.hasKind(weInternalWalkerFault)

# ---- (4) a by-value case object as a heap cell value -----------------------

type
  WK = enum wkA, wkB, wkC
  BV = object
    case kind: WK
    of wkA: a: int
    of wkB, wkC: b: bool
  BVH = ref object
    n: int
    bv: BV
  BVT = ref object
    t: (int, BV)

proc bvRead(p: BVH) =
  if p != nil and p.bv.kind == wkB and p.bv.b and p.n == 2:
    symexTarget("bv_read")

proc bvWrongArm(p: BVH) =
  if p != nil and p.bv.kind == wkA:
    if p.bv.b: symexTarget("bv_wrong")

proc bvNew(n: int) =
  let h = BVH(n: n)
  if h.bv.kind == wkA and h.bv.a == 0 and n == 3: symexTarget("bv_new")
  if h.bv.kind != wkA: symexTarget("bv_new_dead")
  if h.bv.a != 0: symexTarget("bv_new_dead2")

proc bvStore(p: BVH, x: int) =
  if p != nil:
    p.bv = BV(kind: wkA, a: x)
    if p.bv.a == 7: symexTarget("bv_store")
    if p.bv.kind != wkA: symexTarget("bv_store_dead")
    if p.bv.a != x: symexTarget("bv_store_dead2")

proc bvSameBranch(p: BVH) =
  # `of wkB, wkC:` is one branch: moving between its tags keeps `b`.
  if p != nil and p.bv.kind == wkC and p.bv.b:
    p.bv.kind = wkB
    if p.bv.b: symexTarget("bv_same_branch")
    if not p.bv.b: symexTarget("bv_same_branch_dead")

proc bvTuple(p: BVT) =
  if p != nil and p.t[0] == 4 and p.t[1].kind == wkA and p.t[1].a == 9:
    symexTarget("bv_tuple")

suite "S8at (4): a by-value case object field of a ref object":
  test "a read of the discriminator and the active branch":
    let r = symexFind(bvRead, tLabel("bv_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(heUnsupportedPointeeRead)
    if r.status == sxSat: check reproduces(bvRead(r.witness[0]), "bv_read")

  test "a read of an inactive branch's field raises FieldDefect":
    let r = symexFind(bvWrongArm, tLabel("bv_wrong"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxUnsat, sxRaised}
    check not r.errors.hasKind(heUnsupportedPointeeRead)
    let f = symexFind(bvWrongArm, tFieldDefect())
    checkpoint $f.status & " " & show(f.errors)
    check f.status == sxRaised
    check f.raisedTypeId == "FieldDefect"
    check not f.errors.hasKind(heUnsupportedPointeeRead)
    if f.status == sxRaised:
      check f.raisedWitness[0] != nil
      if f.raisedWitness[0] != nil:
        check f.raisedWitness[0].bv.kind == wkA

  test "construction zeroes the field":
    let r = symexFind(bvNew, tLabel("bv_new"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(heNewFieldZeroUnsupported)
    block:
      let d = symexFind(bvNew, tLabel("bv_new_dead"))
      checkpoint "bv_new_dead " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(bvNew, tLabel("bv_new_dead2"))
      checkpoint "bv_new_dead2 " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat

  test "a store of a case object value":
    let r = symexFind(bvStore, tLabel("bv_store"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(bvStore(r.witness[0], r.witness[1]), "bv_store")
    block:
      let d = symexFind(bvStore, tLabel("bv_store_dead"))
      checkpoint "bv_store_dead " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat
    block:
      let d = symexFind(bvStore, tLabel("bv_store_dead2"))
      checkpoint "bv_store_dead2 " & $d.status & " " & show(d.errors)
      check d.status == sxUnsat

  test "a discriminator move within one branch keeps its field":
    let r = symexFind(bvSameBranch, tLabel("bv_same_branch"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(bvSameBranch(r.witness[0]), "bv_same_branch")
    let d = symexFind(bvSameBranch, tLabel("bv_same_branch_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a tuple holding a case object":
    let r = symexFind(bvTuple, tLabel("bv_tuple"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(heUnsupportedPointeeRead)
    if r.status == sxSat: check reproduces(bvTuple(r.witness[0]), "bv_tuple")

type
  EK = enum ekA, ekB, ekC, ekD
  BE = object            # an `else` arm, and a plain field
    tag: int
    case k: EK
    of ekA: x: int
    else: y: bool
  BEH = ref object
    e: BE
  MV2 = object           # two `case` sections
    case p: bool
    of true: pa: int
    of false: pb: bool
    case q: WK
    of wkA: qa: int
    of wkB, wkC: discard
  MVH = ref object
    m: MV2

proc bvWhole(p: ref BV) =
  # `p[] = v` of a ref case object writes the heaps `p.kind` / `p.b` read.
  if p != nil:
    p[] = BV(kind: wkB, b: true)
    if p.kind == wkB and p.b: symexTarget("bv_whole")
    if p.kind != wkB: symexTarget("bv_whole_dead")

proc bvWholeRead(p: ref BV) =
  if p != nil and p.kind == wkA and p.a == 5:
    let v = p[]
    if v.kind == wkA and v.a == 5: symexTarget("bv_whole_read")
    if v.kind != wkA: symexTarget("bv_whole_read_dead")

proc bvCrossBranch(p: BVH) =
  # Moving the discriminator to another branch raises FieldDefect.
  if p != nil and p.bv.kind == wkA:
    p.bv.kind = wkB
    symexTarget("bv_cross_after")

proc beElse(p: BEH) =
  if p != nil and p.e.k == ekC and p.e.y and p.e.tag == 3:
    symexTarget("be_else")

proc beNew(n: int) =
  let h = BEH()
  if h.e.k == ekA and h.e.x == 0 and h.e.tag == 0 and n == 1:
    symexTarget("be_new")
  if h.e.k != ekA: symexTarget("be_new_dead")

proc mvField(p: MVH) =
  if p != nil and not p.m.p and p.m.pb and p.m.q == wkC:
    symexTarget("mv_field")

suite "S8at (4): case objects through a ref, more shapes":
  test "a whole store `p[] = v` of a ref case object":
    let r = symexFind(bvWhole, tLabel("bv_whole"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(bvWhole, tLabel("bv_whole_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a whole read `p[]` of a ref case object":
    let r = symexFind(bvWholeRead, tLabel("bv_whole_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(bvWholeRead, tLabel("bv_whole_read_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a discriminator move to another branch raises FieldDefect":
    let r = symexFind(bvCrossBranch, tLabel("bv_cross_after"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxUnsat, sxRaised}
    let f = symexFind(bvCrossBranch, tFieldDefect())
    checkpoint $f.status & " " & show(f.errors)
    check f.status == sxRaised
    check f.raisedTypeId == "FieldDefect"

  test "an else arm and a plain field":
    let r = symexFind(beElse, tLabel("be_else"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check r.witness[0].e.k == ekC
      check reproduces(beElse(r.witness[0]), "be_else")

  test "construction zeroes an else-armed case object":
    let r = symexFind(beNew, tLabel("be_new"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(beNew, tLabel("be_new_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a multi-variant field":
    let r = symexFind(mvField, tLabel("mv_field"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(heUnsupportedPointeeRead)
    if r.status == sxSat: check reproduces(mvField(r.witness[0]), "mv_field")

# ---- (1) a `ref` to an anonymous tuple --------------------------------------

proc rtRead(p: ref (int, int)) =
  if p != nil and p[0] == 3 and p[1] == 4: symexTarget("rt_read")

proc rtWrite(p: ref (int, int), x: int) =
  if p != nil:
    p[0] = x
    if p[0] == 9 and p[1] == 2: symexTarget("rt_write")
    if p[0] != x: symexTarget("rt_write_dead")

proc rtWhole(p: ref (int, bool)) =
  if p != nil:
    let before = p[1]
    p[] = (5, not before)
    if p[0] == 5 and p[1] != before: symexTarget("rt_whole")
    if p[0] != 5: symexTarget("rt_whole_dead")

proc rtNew(x: int) =
  var p: ref (int, int)
  new(p)
  if p[0] == 0 and p[1] == 0 and x == 1: symexTarget("rt_new")
  if p[1] != 0: symexTarget("rt_new_dead")

proc rtAlias(p, q: ref (int, int)) =
  if p != nil and q != nil:
    p[0] = 1
    q[0] = 2
    if p[0] == 2: symexTarget("rt_alias")

suite "S8at (1): a ref to an anonymous tuple":
  test "a read of its elements":
    let r = symexFind(rtRead, tLabel("rt_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(rtRead(r.witness[0]), "rt_read")

  test "an element write":
    let r = symexFind(rtWrite, tLabel("rt_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(rtWrite(r.witness[0], r.witness[1]), "rt_write")
    let d = symexFind(rtWrite, tLabel("rt_write_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a whole store":
    let r = symexFind(rtWhole, tLabel("rt_whole"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(rtWhole(r.witness[0]), "rt_whole")
    let d = symexFind(rtWhole, tLabel("rt_whole_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "new zeroes it":
    let r = symexFind(rtNew, tLabel("rt_new"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(rtNew, tLabel("rt_new_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "two refs may alias":
    let r = symexFind(rtAlias, tLabel("rt_alias"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(rtAlias(r.witness[0], r.witness[1]), "rt_alias")

# ---- (3) a symbolic index into an array of seqs ----------------------------

type ASH = ref object
  a: array[3, seq[int]]

proc asHeap(p: ASH, i: int) =
  if p != nil and i >= 0 and i < 3 and p.a[i].len == 2 and p.a[i][1] == 5 and
     p.a[0].len == 0:
    symexTarget("as_heap")
  if p != nil and i >= 0 and i < 3 and p.a[i].len > 1024:
    symexTarget("as_heap_dead")

proc asLocal(i, x: int) =
  var a: array[2, seq[int]]
  a[1].add x
  if i >= 0 and i < 2 and a[i].len == 1 and a[i][0] == 8: symexTarget("as_local")
  if i >= 0 and i < 2 and a[i].len == 1 and i == 0: symexTarget("as_local_dead")

proc asParam(a: array[2, seq[int]], i: int) =
  if i >= 0 and i < 2 and a[i].len == 3 and i == 1: symexTarget("as_param")

proc asMut(p: ASH, i, x: int) =
  if p != nil and i >= 0 and i < 3:
    p.a[i].add x
    if p.a[2].len == 1 and p.a[2][0] == 6: symexTarget("as_mut")
    if p.a[i].len == 0: symexTarget("as_mut_dead")

proc asOob(i: int) =
  var a: array[2, seq[int]]
  try:
    a[i].add 1
  except IndexDefect:
    if i == 2 and a[0].len == 0 and a[1].len == 0: symexTarget("as_oob")
    if i == 1: symexTarget("as_oob_dead")

proc asTab(k: string) =
  var a: array[2, Table[string, int]]
  a[1][k] = 4
  a[0].del k
  if a[1].hasKey(k) and a[1][k] == 4 and k == "z" and a[0].len == 0:
    symexTarget("as_tab")
  if not a[1].hasKey(k): symexTarget("as_tab_dead")

suite "S8at (3): a symbolic index into an array of seqs":
  test "through a ref":
    let r = symexFind(asHeap, tLabel("as_heap"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedOpHavoc)
    if r.status == sxSat:
      check reproduces(asHeap(r.witness[0], r.witness[1]), "as_heap")
    let d = symexFind(asHeap, tLabel("as_heap_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a local array":
    let r = symexFind(asLocal, tLabel("as_local"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asLocal(r.witness[0], r.witness[1]), "as_local")
    let d = symexFind(asLocal, tLabel("as_local_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a parameter":
    let r = symexFind(asParam, tLabel("as_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      replays(asParam(r.witness[0], r.witness[1]), "as_param")

  test "a mutation of an element":
    let r = symexFind(asMut, tLabel("as_mut"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asMut(r.witness[0], r.witness[1], r.witness[2]), "as_mut")
    let d = symexFind(asMut, tLabel("as_mut_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an out-of-range element mutation raises":
    let r = symexFind(asOob, tLabel("as_oob"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asOob(r.witness[0]), "as_oob")
    let d = symexFind(asOob, tLabel("as_oob_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a Table element":
    let r = symexFind(asTab, tLabel("as_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(asTab(r.witness[0]), "as_tab")
    let d = symexFind(asTab, tLabel("as_tab_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

# ---- (5) a `distinct` over a composite base ---------------------------------

type
  DSq = distinct seq[int]
  DTp = distinct (int, bool)
  DSH = ref object
    ds: DSq
    dt: DTp
    n: int

proc dsRead(p: DSH) =
  if p != nil and seq[int](p.ds).len == 2 and seq[int](p.ds)[1] == 7 and
     (int, bool)(p.dt)[0] == 3:
    symexTarget("ds_read")

proc dsWrite(p: DSH, v: int) =
  if p != nil:
    p.ds = DSq(@[v])
    if seq[int](p.ds).len == 1 and seq[int](p.ds)[0] == 6: symexTarget("ds_write")
    if seq[int](p.ds)[0] != v: symexTarget("ds_write_dead")

proc dsNew(n: int) =
  let h = DSH(n: n)
  if seq[int](h.ds).len == 0 and n == 2: symexTarget("ds_new")
  if seq[int](h.ds).len != 0: symexTarget("ds_new_dead")

proc dsParam(d: DSq) =
  if seq[int](d).len == 1 and seq[int](d)[0] == 3: symexTarget("ds_param")

type
  DOb = object
    a: int
    s: string
  DO = distinct DOb
  DOH = ref object
    d: DO

proc len(d: DSq): int {.borrow.}

proc dtWrite(p: DSH, x: int) =
  if p != nil:
    p.dt = DTp((x, true))
    if (int, bool)(p.dt)[0] == 9 and (int, bool)(p.dt)[1]: symexTarget("dt_write")
    if not (int, bool)(p.dt)[1]: symexTarget("dt_write_dead")

proc doRead(p: DOH) =
  if p != nil and DOb(p.d).a == 4 and DOb(p.d).s == "q": symexTarget("do_read")

proc dsBorrow(d: DSq) =
  if d.len == 2: symexTarget("ds_borrow")

suite "S8at (5): a distinct over a composite base":
  test "a field read":
    let r = symexFind(dsRead, tLabel("ds_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(heUnsupportedPointeeRead)
    if r.status == sxSat: check reproduces(dsRead(r.witness[0]), "ds_read")

  test "a field write":
    let r = symexFind(dsWrite, tLabel("ds_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(dsWrite, tLabel("ds_write_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "construction zeroes it":
    let r = symexFind(dsNew, tLabel("ds_new"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(dsNew, tLabel("ds_new_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a parameter":
    let r = symexFind(dsParam, tLabel("ds_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(dsParam(r.witness[0]), "ds_param")

  test "a distinct tuple field write":
    let r = symexFind(dtWrite, tLabel("dt_write"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      check reproduces(dtWrite(r.witness[0], r.witness[1]), "dt_write")
    let d = symexFind(dtWrite, tLabel("dt_write_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a distinct object field":
    let r = symexFind(doRead, tLabel("do_read"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: check reproduces(doRead(r.witness[0]), "do_read")

  test "a borrowed proc":
    # RFC-0005 S8at pinned this declined: a `{.borrow.}` routine that is not
    # an operator had the borrowed symbol as its body
    # (`feUnsupportedStmtKind`). RFC-0005 S8bc (item 2) lowers it as the base
    # routine on the unwrapped argument.
    let r = symexFind(dsBorrow, tLabel("ds_borrow"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(feUnsupportedStmtKind)
    if r.status == sxSat: replays(dsBorrow(r.witness[0]), "ds_borrow")

# ---- (6) a value object that recurs through a container ---------------------
#
# RFC-0005 S8at: the recursion is not what declines here. A seq whose
# element is a tuple or object is backed in no position (a parameter, a
# field, a local: `isBackedSeqElemTy`), recursive or not; `seq[P]` with a
# plain `P = object a: int` declines the same way. That is a different
# mechanism (a leaf-split seq element) and stays a scoped, stated decline:
# a path that does not read the seq is exact.

type
  VRc = object
    kids: seq[VRc]
    v: int
  VFlat = object
    a: int
  VHold = object
    ps: seq[VFlat]

proc vrKids(p: VRc) =
  if p.v == 1: symexTarget("vr_v")
  if p.kids.len == 1 and p.kids[0].v == 3: symexTarget("vr_kids")

proc vrFlat(h: VHold) =
  if h.ps.len == 1 and h.ps[0].a == 3: symexTarget("vr_flat")

suite "S8at (6): a value object recurring through a seq":
  test "a path that does not read the seq is exact":
    let r = symexFind(vrKids, tLabel("vr_v"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    check not r.errors.hasKind(weInternalWalkerFault)

  test "its elements decline at the read, as a non-recursive element does":
    let r = symexFind(vrKids, tLabel("vr_kids"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(seNestedSeqUnsupported)
    check not r.errors.hasKind(weInternalWalkerFault)
    let f = symexFind(vrFlat, tLabel("vr_flat"))
    checkpoint $f.status & " " & show(f.errors)
    check f.status == sxUnknown
    check f.errors.hasKind(seNestedSeqUnsupported)

# ---- (7) Table float keys and container values ------------------------------

type BTab = ref object
  tq: Table[string, seq[int]]

proc tfZero(x: int) =
  var t = initTable[float, int]()
  t[0.0] = 1
  if (-0.0) in t and t[-0.0] == 1 and x == 2: symexTarget("tf_zero")
  if (-0.0) notin t: symexTarget("tf_zero_dead")

proc tfNan(x: int) =
  var t = initTable[float, int]()
  let n = NaN
  t[n] = 1
  if n notin t and x == 1: symexTarget("tf_nan")
  if n in t: symexTarget("tf_nan_dead")

proc tfNanTwice(x: int) =
  # Each NaN insert is its own entry; `del(NaN)` finds none of them.
  var t = initTable[float, int]()
  let n = NaN
  t[n] = 1
  t[n] = 2
  t.del(n)
  if t.len == 2 and x == 3: symexTarget("tf_nan2")
  if t.len != 2: symexTarget("tf_nan2_dead")

proc tfParam(t: Table[float, int]) =
  if t.len == 1 and 1.5 in t and t[1.5] == 4: symexTarget("tf_param")

proc tfF32(t: Table[float32, int], k: float32) =
  if k < 0'f32 and k in t and t.len == 1 and t[k] == 7: symexTarget("tf_f32")

proc tfSymKey(t: Table[float, int], k: float) =
  # A symbolic NaN key is never found, whatever the table holds.
  if k != k and k in t: symexTarget("tf_symnan_dead")

proc tcVal(t: Table[string, seq[int]]) =
  if "a" in t and t["a"].len == 2 and t["a"][1] == 9: symexTarget("tc_val")

proc tcLocal(x: int) =
  var t = initTable[int, seq[int]]()
  t[1] = @[x]
  if t[1].len == 1 and t[1][0] == 5: symexTarget("tc_local")
  if t[1].len != 1: symexTarget("tc_local_dead")

proc tcHeap(p: BTab) =
  if p != nil and p.tq.len == 1 and "k" in p.tq and p.tq["k"].len == 1:
    symexTarget("tc_heap")

proc tcSet(t: Table[int, HashSet[int]]) =
  if 3 in t and t[3].len == 2 and 8 in t[3]: symexTarget("tc_set")

proc tcNested(t: Table[string, Table[string, int]]) =
  if "o" in t and "i" in t["o"] and t["o"]["i"] == 6: symexTarget("tc_nested")

proc tcStrs(t: Table[char, seq[string]]) =
  if 'c' in t and t['c'].len == 1 and t['c'][0] == "hi": symexTarget("tc_strs")

proc tcOverwrite(t: Table[string, seq[int]]) =
  var u = t
  u["a"] = @[1, 2, 3]
  if "a" in t and t["a"].len == 1 and u["a"].len == 3: symexTarget("tc_over")
  if u["a"].len != 3: symexTarget("tc_over_dead")

proc tcBranch(x: int) =
  var t = initTable[string, seq[int]]()
  if x > 0: t["a"] = @[1]
  else: t["a"] = @[1, 2]
  if t["a"].len == 2 and x == -4: symexTarget("tc_branch")
  if t["a"].len == 2 and x > 0: symexTarget("tc_branch_dead")

proc tcAdd(x: int) =
  # `t[k].add x` mutates the value in place (`[]`'s `var` overload).
  var t = initTable[string, seq[int]]()
  t["a"] = @[1]
  t["a"].add x
  if t["a"].len == 2 and t["a"][1] == 7: symexTarget("tc_add")
  if t["a"].len == 1: symexTarget("tc_add_dead")

proc tcAddParam(t: Table[string, seq[int]]) =
  var u = t
  if "a" in u:
    u["a"].add 4
    if u["a"].len == t["a"].len: symexTarget("tc_addp_dead")
    if u["a"].len == 3 and u["a"][2] == 4 and t["a"][0] == 2:
      symexTarget("tc_addp")

proc tcAddAbsent(t: Table[string, seq[int]]) =
  # An absent key raises `KeyError` before anything is added.
  var u = t
  try:
    u["z"].add 1
    if "z" notin t: symexTarget("tc_absent_dead")
  except KeyError:
    if "z" notin t: symexTarget("tc_absent")

proc tcIncl(t: Table[string, HashSet[int]]) =
  var u = t
  if "a" in u and u["a"].len == 0:
    u["a"].incl 4
    if 4 notin u["a"] or u["a"].len != 1: symexTarget("tc_incl_dead")
    if 4 in u["a"]: symexTarget("tc_incl")

proc tkKeyErr(t: Table[string, int]) =
  # An absent key's `[]` raises `KeyError`; it was a narrowed path only, so
  # the handler was dead (a false sxUnsat at base).
  try:
    let v = t["z"]
    if v == 3: symexTarget("tk_hit")
  except KeyError:
    symexTarget("tk_keyerr")

proc tkKeyErrDead(t: Table[string, int]) =
  if "z" in t:
    try:
      discard t["z"]
    except KeyError:
      symexTarget("tk_keyerr_dead")

suite "S8at (7): Table float keys and container values":
  test "-0.0 and 0.0 are one key":
    let r = symexFind(tfZero, tLabel("tf_zero"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tfZero, tLabel("tf_zero_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a NaN key is never found":
    let r = symexFind(tfNan, tLabel("tf_nan"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tfNan, tLabel("tf_nan_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "each NaN insert is an entry, and del(NaN) removes none":
    let r = symexFind(tfNanTwice, tLabel("tf_nan2"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tfNanTwice, tLabel("tf_nan2_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a symbolic NaN key is never found":
    let d = symexFind(tfSymKey, tLabel("tf_symnan_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a float-keyed parameter":
    let r = symexFind(tfParam, tLabel("tf_param"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tfParam(r.witness[0]), "tf_param")

  test "a float32-keyed parameter, negative key":
    let r = symexFind(tfF32, tLabel("tf_f32"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat:
      replays(tfF32(r.witness[0], r.witness[1]), "tf_f32")

  test "a seq-valued parameter":
    let r = symexFind(tcVal, tLabel("tc_val"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcVal(r.witness[0]), "tc_val")

  test "a seq-valued local":
    let r = symexFind(tcLocal, tLabel("tc_local"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcLocal, tLabel("tc_local_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq-valued field":
    let r = symexFind(tcHeap, tLabel("tc_heap"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcHeap(r.witness[0]), "tc_heap")

  test "a set-valued parameter":
    let r = symexFind(tcSet, tLabel("tc_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcSet(r.witness[0]), "tc_set")

  test "a table-valued parameter":
    let r = symexFind(tcNested, tLabel("tc_nested"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcNested(r.witness[0]), "tc_nested")

  test "a seq[string]-valued parameter":
    let r = symexFind(tcStrs, tLabel("tc_strs"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcStrs(r.witness[0]), "tc_strs")

  test "an overwrite leaves the copied-from table alone":
    let r = symexFind(tcOverwrite, tLabel("tc_over"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcOverwrite(r.witness[0]), "tc_over")
    let d = symexFind(tcOverwrite, tLabel("tc_over_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a seq value is added to in place":
    let r = symexFind(tcAdd, tLabel("tc_add"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcAdd, tLabel("tc_add_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a parameter's seq value is added to in place":
    let r = symexFind(tcAddParam, tLabel("tc_addp"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcAddParam(r.witness[0]), "tc_addp")
    let d = symexFind(tcAddParam, tLabel("tc_addp_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "adding to an absent key's value raises KeyError":
    let r = symexFind(tcAddAbsent, tLabel("tc_absent"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcAddAbsent, tLabel("tc_absent_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a set value is included into in place":
    let r = symexFind(tcIncl, tLabel("tc_incl"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tcIncl(r.witness[0]), "tc_incl")
    let d = symexFind(tcIncl, tLabel("tc_incl_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "an absent key raises KeyError":
    let r = symexFind(tkKeyErr, tLabel("tk_keyerr"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(tkKeyErr(r.witness[0]), "tk_keyerr")
    let d = symexFind(tkKeyErrDead, tLabel("tk_keyerr_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

  test "a container value merges across a branch":
    let r = symexFind(tcBranch, tLabel("tc_branch"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    let d = symexFind(tcBranch, tLabel("tc_branch_dead"))
    checkpoint $d.status & " " & show(d.errors)
    check d.status == sxUnsat

# ---- (8) uint8 vs char top-level containers ---------------------------------

proc u8Tab(t: Table[uint8, int]) =
  if t.len == 1 and 200'u8 in t: symexTarget("u8_tab")

proc chTab(t: Table[char, int]) =
  if t.len == 1 and 'z' in t: symexTarget("ch_tab")

proc u8Seq(s: seq[uint8]) =
  if s.len == 1 and s[0] == 250: symexTarget("u8_seq")

proc chSet(s: HashSet[char]) =
  if s.len == 1 and 'q' in s: symexTarget("ch_set")

proc u32Set(s: HashSet[uint32]) =
  # A 2^32-cell domain: `mkInt` (a `cint`) faulted on its size at base.
  if s.len == 1 and 4_000_000_000'u32 in s: symexTarget("u32_set")

proc u32Tab(t: Table[uint32, int]) =
  if t.len == 1 and 3_000_000_000'u32 in t: symexTarget("u32_tab")

suite "S8at (8): uint8 and char containers are told apart":
  test "Table[uint8, int]":
    let r = symexFind(u8Tab, tLabel("u8_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u8Tab(r.witness[0]), "u8_tab")

  test "Table[char, int]":
    let r = symexFind(chTab, tLabel("ch_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chTab(r.witness[0]), "ch_tab")

  test "seq[uint8]":
    let r = symexFind(u8Seq, tLabel("u8_seq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u8Seq(r.witness[0]), "u8_seq")

  test "HashSet[char]":
    let r = symexFind(chSet, tLabel("ch_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(chSet(r.witness[0]), "ch_set")

  test "HashSet[uint32] (a 2^32-cell domain)":
    let r = symexFind(u32Set, tLabel("u32_set"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u32Set(r.witness[0]), "u32_set")

  test "Table[uint32, int] (a 2^32-cell domain)":
    let r = symexFind(u32Tab, tLabel("u32_tab"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat
    if r.status == sxSat: replays(u32Tab(r.witness[0]), "u32_tab")

suite "S8at: walker version floor":
  test "walker version floor >= 193":
    check parseInt(symexWalkerVersion) >= 193
