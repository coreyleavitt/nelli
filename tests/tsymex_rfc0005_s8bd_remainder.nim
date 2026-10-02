## RFC-0005 (soundness channels) slice S8bd -- S8ba's remainder.
##
## Pinned here (the RFC's "As landed (S8bd)" note has the design and the
## measurements):
##   (1) a string index `i` that is a bit-vector, compared with `s.len`
##       both as itself and as `i + 1`, decides: the two Int views of `i`
##       and `i + 1` are linked by an exact theorem of two's complement
##       (`bvOffsetLinks`). It ran ~41M units to `sxUnknown`;
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo], k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

const exact = SymexSettings(integerSemantics: isExact)

# ---- (1) a bit-vector string index against the length ------------------------

proc sIdx(s: string, i: int) =
  ## `i` is a bit-vector (`i + 1` can overflow); `i < s.len` reads its Int
  ## view, `i + 1 > s.len` the Int view of `i + 1`.
  if i >= 0 and i < s.len and s[i] == 'a' and i + 1 > s.len:
    symexTarget("si_dead")
  if i >= 0 and i < s.len and s[i] == 'a' and i + 1 == s.len:
    symexTarget("si")

proc sIdxNoAt(s: string, i: int) =
  if i >= 0 and i < s.len and i + 1 > s.len: symexTarget("sn_dead")

proc sIdxPrev(s: string, i: int) =
  ## The subtraction twin: `s[i - 1]` with `i - 1 >= s.len`.
  if i >= 1 and i <= s.len and s[i - 1] == 'b' and i - 1 >= s.len:
    symexTarget("sp_dead")
  if i >= 1 and i <= s.len and s[i - 1] == 'b' and i == s.len:
    symexTarget("sp")

suite "S8bd (1): a bit-vector string index against the length decides":

  test "nim":
    let s = "xa"
    check s[1] == 'a' and 1 + 1 == s.len

  test "s[i] with i + 1 > s.len is refuted":
    ## RED: `sxUnknown` (`beSolverUndef`, "no model with every string / seq
    ## at most 128 elements"), ~41M units, on both Z3 versions.
    discard clean(sIdx, "si_dead", sxUnsat)
    let r = clean(sIdx, "si", sxSat)
    if r.status == sxSat:
      let i = r.witness[1]
      check i + 1 == r.witness[0].len and r.witness[0][i] == 'a'

  test "the same without the character read":
    discard clean(sIdxNoAt, "sn_dead", sxUnsat)

  test "the subtraction twin":
    discard clean(sIdxPrev, "sp_dead", sxUnsat)
    let r = clean(sIdxPrev, "sp", sxSat)
    if r.status == sxSat:
      check r.witness[0][r.witness[1] - 1] == 'b'

  test "the bit-vector encoding (isExact)":
    discard clean(sIdx, "si_dead", sxUnsat, exact)
    discard clean(sIdxNoAt, "sn_dead", sxUnsat, exact)

  test "the links are theorems":
    ## Every link `bvOffsetLinks` states, at width 8 over a grid of `x` and
    ## `c` (both signs, the wrap at both ends), is valid: with `x` fixed,
    ## its negation is UNSAT.
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bd_x")
    proc view(b: Z3BitVec[8], signed: bool): Z3Int =
      wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, b.raw, signed))
    var n = 0
    for xv in [0, 1, 2, 126, 127, 128, 129, 200, 254, 255]:
      for cv in [1, 2, 127, 128, 129, 255]:
        let c = mkBitVec[8](ctx, cv)
        for signed in [false, true]:
          for t in [x + c, c + x, x - c]:
            let facts = bvOffsetLinks(ctx, [view(t, signed) == view(t, signed),
                                            view(x, signed) == view(x, signed)])
            checkpoint $xv & " " & $cv & " " & $signed
            check facts.len == 1
            for f in facts:
              let s = querySolver(ctx, [x == mkBitVec[8](ctx, xv), not f], 0)
              check s.check() == zsUnsat
              inc n
    check n == 10 * 6 * 2 * 3

  test "a view the query does not hold is not linked":
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bd_y")
    let t = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw,
      (x + mkBitVec[8](ctx, 1)).raw, false))
    check bvOffsetLinks(ctx, [t > mkInt(ctx, 3)]).len == 0

# ---- (2) a seq[distinct] parameter -------------------------------------------

type Meters = distinct int
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}
type Grams = distinct int32
type Secs = distinct float
type Km = distinct Meters    # a distinct of a distinct

proc dParam(s: seq[Meters]) =
  if s.len > 1 and s[0] == Meters(3) and s[1] < Meters(-5): symexTarget("dp")
  if s.len > 0 and s[0] == Meters(3) and int(s[0]) != 3: symexTarget("dp_dead")

proc dParam32(s: seq[Grams]) =
  if s.len == 2 and int32(s[1]) == 70000'i32: symexTarget("d32")

proc dParamF(s: seq[Secs]) =
  if s.len == 1 and float(s[0]) > 2.5: symexTarget("df")

proc dParamNested(s: seq[Km]) =
  if s.len == 1 and int(Meters(s[0])) == 11: symexTarget("dn")

suite "S8bd (2): a seq[distinct] parameter has a witness":

  test "nim":
    let s = @[Meters(3), Meters(-6)]
    check s[0] == Meters(3) and s[1] < Meters(-5)

  test "seq[Meters]":
    ## RED: `sxUnknown`, `feUnsupportedWitnessType` (S8ba pinned it so).
    let r = clean(dParam, "dp", sxSat)
    if r.status == sxSat:
      let w: seq[Meters] = r.witness[0]
      check w.len > 1 and int(w[0]) == 3 and int(w[1]) < -5
      check replayWitness(dParam, r.witness, tLabel("dp"), {}) == roConfirmed
    discard clean(dParam, "dp_dead", sxUnsat)

  test "other widths, a float base, a nested distinct":
    let a = clean(dParam32, "d32", sxSat)
    if a.status == sxSat:
      let w: seq[Grams] = a.witness[0]
      check w.len == 2 and int32(w[1]) == 70000'i32
      check replayWitness(dParam32, a.witness, tLabel("d32"), {}) == roConfirmed
    # A distinct of a float, or of a distinct, carries S8ba's
    # `geDistinctBijectivitySkipped` hint (sevHint): the sort is modelled
    # without the round-trip axiom.
    template hinted(fn: typed, lbl: string): untyped =
      block:
        let r = symexFind(fn, tLabel(lbl))
        checkpoint lbl & " " & $r.status & " " & show(r.errors)
        check r.status == sxSat
        for e in r.errors: check e.severity == sevHint
        r
    let b = hinted(dParamF, "df")
    if b.status == sxSat:
      let w: seq[Secs] = b.witness[0]
      check float(w[0]) > 2.5
      check replayWitness(dParamF, b.witness, tLabel("df"), {}) == roConfirmed
    let c = hinted(dParamNested, "dn")
    if c.status == sxSat:
      let w: seq[Km] = c.witness[0]
      check int(Meters(w[0])) == 11
      check replayWitness(dParamNested, c.witness, tLabel("dn"), {}) == roConfirmed

# ---- (3) the heap-depth budget bounds a chain, not a count -------------------

type Box = ref object
  x: int
type Outer = ref object
  inner: Box
type Node = ref object
  val: int
  next: Node

var gBox: Box

proc setXG(v: var int, k: int) =
  v = k
  gBox.x = 5

proc rebindThenSet(v: var int, k: int) =
  gBox = Box(x: 1)
  v = k

proc manyReads(k: int) =
  ## Twelve dereferences of one object, none of them through another.
  let p = Box(x: 0)
  p.x = k
  if p.x > 0 and p.x < 9 and p.x != 1 and p.x != 2 and p.x == k and
     p.x != 4 and p.x != 5 and p.x < 7 and p.x != 6 and p.x >= 3:
    symexTarget("mr")
  if p.x != k: symexTarget("mr_dead")

proc sutHeapRebind(k: int) =
  let p = Box(x: 0)
  gBox = p
  rebindThenSet(p.x, k)
  if p.x == k and gBox.x == 1 and k == 6: symexTarget("hr")
  if p.x != k or gBox.x != 1: symexTarget("hr_dead")

proc sutHeapNested(k: int) =
  let o = Outer(inner: Box(x: 0))
  gBox = o.inner
  setXG(o.inner.x, k)
  if o.inner.x == 5 and k == 8: symexTarget("hn")
  if o.inner.x == k and k != 5: symexTarget("hn_dead")

proc chain7(n: Node) =
  ## A chain of seven links: the last read is seven dereferences deep.
  if n != nil and n.next != nil and n.next.next != nil and
     n.next.next.next != nil and n.next.next.next.next != nil and
     n.next.next.next.next.next != nil and
     n.next.next.next.next.next.next != nil and
     n.next.next.next.next.next.next.val == 7:
    symexTarget("c7")

proc chain9(n: Node) =
  ## Nine links: past the default budget of eight.
  if n == nil: return
  let n1 = n.next
  if n1 == nil: return
  let n2 = n1.next
  if n2 == nil: return
  let n3 = n2.next
  if n3 == nil: return
  let n4 = n3.next
  if n4 == nil: return
  let n5 = n4.next
  if n5 == nil: return
  let n6 = n5.next
  if n6 == nil: return
  let n7 = n6.next
  if n7 == nil: return
  let n8 = n7.next
  if n8 != nil and n8.val == 9: symexTarget("c9")

const shallow = SymexSettings(budget: ResourceBudget(maxHeapDepth: 3))

suite "S8bd (3): the heap-depth budget bounds a chain":

  test "nim":
    let o = Outer(inner: Box(x: 0))
    gBox = o.inner
    setXG(o.inner.x, 8)
    check o.inner.x == 5

  test "many reads of one object are within the default budget":
    ## RED: `sxUnknown`, `heDepthExhausted` (the count of every dereference
    ## on the path passed 8).
    discard clean(manyReads, "mr", sxSat)
    discard clean(manyReads, "mr_dead", sxUnsat)

  test "S8ba's hr and hn decide at the default budget":
    ## RED: `heDepthExhausted` (S8ba pinned them under `maxHeapDepth: 32`).
    discard clean(sutHeapRebind, "hr", sxSat)
    discard clean(sutHeapRebind, "hr_dead", sxUnsat)
    discard clean(sutHeapNested, "hn", sxSat)
    discard clean(sutHeapNested, "hn_dead", sxUnsat)

  test "a chain within the budget decides":
    let r = clean(chain7, "c7", sxSat)
    if r.status == sxSat:
      check r.witness[0].next.next.next.next.next.next.val == 7

  test "a chain past the budget still declines, and names it":
    for (r, lbl) in [(symexFind(chain9, tLabel("c9")), "default"),
                     (symexFind(chain7, tLabel("c7"), shallow), "shallow")]:
      checkpoint lbl & " " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check r.errors.hasKind(heDepthExhausted)
      var named = false
      for e in r.errors:
        if e.kind == heDepthExhausted and "maxHeapDepth" in e.msg: named = true
      check named

  test "the decline names the budget it hit":
    check "maxHeapDepth" in heapDerefDecline(8, 8, 8)
    check heapDerefDecline(7, 4000, 8) == ""
    check "heapDerefsPerPathCap" in
      heapDerefDecline(1, heapDerefsPerPathCap + 1, 8)
    check "heapDerefsPerPathCap" in
      heapDerefDecline(1, heapDerefsPerPathCap + 1, 0)
    check heapDerefDecline(100, 100, 0) == ""

# ---- (4) by reference: an indexed ref, a call result, a generic callee -------

var gI: int
var gCount: int

proc bumpThenSet(v: var int, k: int) =
  ## Moves the index the caller's lvalue was spelled with, then writes.
  gI = 1
  v = k
  if gBox.x == 77: gBox.x = 78

proc nextI(): int =
  inc gCount
  gCount - 1

proc getB(): Box =
  inc gCount
  gBox

proc setGen[T](v: var T, k: T) =
  v = k
  gBox.x = 5

type Box2 = ref object
  x: int
  y: int16
var gB2: Box2

proc setGen2[T](v: var T, k: T) =
  v = k
  gB2.x = 5

proc sutArrElem(k: int) =
  var a = [Box(x: 0)]
  gBox = a[0]
  setXG(a[0].x, k)
  if a[0].x == 5 and k == 2: symexTarget("he")
  if a[0].x == k and k != 5: symexTarget("he_dead")

proc sutIdxOnce(k: int) =
  ## The index is read before the call; the callee moving it does not move
  ## the cell.
  var a = [Box(x: 0), Box(x: 0)]
  gI = 0
  gBox = a[1]
  bumpThenSet(a[gI].x, k)
  if a[0].x == k and a[1].x == 0 and gI == 1 and k == 4: symexTarget("hi")
  if a[1].x == k and k != 0: symexTarget("hi_dead")

proc sutIdxCall(k: int) =
  ## The index is evaluated once.
  var s = @[Box(x: 0), Box(x: 0)]
  gCount = 0
  gBox = s[0]
  setXG(s[nextI()].x, k)
  if s[0].x == 5 and gCount == 1 and k == 6: symexTarget("hic")
  if gCount != 1 or s[1].x != 0: symexTarget("hic_dead")

proc sutCallResult(k: int) =
  gBox = Box(x: 0)
  gCount = 0
  setXG(getB().x, k)
  if gBox.x == 5 and gCount == 1 and k == 2: symexTarget("hcr")
  if gBox.x == k and k != 5: symexTarget("hcr_dead")
  if gCount != 1: symexTarget("hcr_dead2")

proc sutGeneric(k: int) =
  let p = Box(x: 0)
  gBox = p
  setGen(p.x, k)
  if p.x == 5 and k == 1: symexTarget("hgen")
  if p.x == k and k != 5: symexTarget("hgen_dead")

proc sutGeneric2(k: int) =
  ## Two instantiations of one generic, each passed a cell by reference.
  let p = Box2(x: 0, y: 0)
  gB2 = p
  setGen2(p.y, int16(k and 0x7f))
  setGen2(p.x, k)
  if p.x == 5 and p.y == 9 and k == 9: symexTarget("hgen2")
  if p.x != 5 or p.y != int16(k and 0x7f): symexTarget("hgen2_dead")

var gP: ptr int

proc keepPtrG[T](p: ptr T, k: T) =
  gP = p
  p[] = k

proc sutGenericEscape(k: int) =
  ## A generic callee that keeps the pointer it is passed.
  var x = 0
  keepPtrG(addr x, k)
  gP[] = 7
  if x != 7: symexTarget("ge_dead")

suite "S8bd (4): more lvalues and callees are passed by reference":

  test "nim":
    var a = [Box(x: 0), Box(x: 0)]
    gI = 0
    gBox = a[1]
    bumpThenSet(a[gI].x, 4)
    check a[0].x == 4 and a[1].x == 0 and gI == 1
    var s = @[Box(x: 0), Box(x: 0)]
    gCount = 0
    gBox = s[0]
    setXG(s[nextI()].x, 6)
    check s[0].x == 5 and gCount == 1
    gBox = Box(x: 0)
    gCount = 0
    setXG(getB().x, 2)
    check gBox.x == 5 and gCount == 1
    let p = Box(x: 0)
    gBox = p
    setGen(p.x, 1)
    check p.x == 5
    let q = Box2(x: 0, y: 0)
    gB2 = q
    setGen2(q.y, 9'i16)
    setGen2(q.x, 9)
    check q.x == 5 and q.y == 9

  test "an array element":
    ## RED: `sxUnknown`, `feUnsupportedOp` (S8au's decline; S8ba pinned it).
    discard clean(sutArrElem, "he", sxSat)
    discard clean(sutArrElem, "he_dead", sxUnsat)

  test "the index is read once, before the call":
    discard clean(sutIdxOnce, "hi", sxSat)
    discard clean(sutIdxOnce, "hi_dead", sxUnsat)
    discard clean(sutIdxCall, "hic", sxSat)
    discard clean(sutIdxCall, "hic_dead", sxUnsat)

  test "a call result":
    discard clean(sutCallResult, "hcr", sxSat)
    discard clean(sutCallResult, "hcr_dead", sxUnsat)
    discard clean(sutCallResult, "hcr_dead2", sxUnsat)

  test "a generic callee":
    discard clean(sutGeneric, "hgen", sxSat)
    discard clean(sutGeneric, "hgen_dead", sxUnsat)
    discard clean(sutGeneric2, "hgen2", sxSat)
    discard clean(sutGeneric2, "hgen2_dead", sxUnsat)

  test "a generic callee's escaping pointer is not a local cell":
    ## RED: `sxSat` (a false one). S8an's `ptrFormalStaysLocal` read the
    ## generic instance's body with its formal list's symbol, found no
    ## use, and modelled the escaping pointer as a cell for the call.
    let r = symexFind(sutGenericEscape, tLabel("ge_dead"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(heUnsafeCast)

suite "S8bd: walker version":
  test "symexWalkerVersion >= 204":
    check parseInt(symexWalkerVersion) >= 204
