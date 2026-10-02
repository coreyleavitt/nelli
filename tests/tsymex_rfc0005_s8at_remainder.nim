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

  test "newSeq through such a generic compiles; newSeq itself is not modelled":
    # `newSeq` has no model: its stdlib body is walked until the call-depth
    # budget runs out, an honest sxUnknown (reported, not fixed here).
    let r = symexFind(retOnlyNewSeq, tLabel("ret_newseq"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
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
  BTab = ref object
    tq: Table[string, seq[int]]

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
