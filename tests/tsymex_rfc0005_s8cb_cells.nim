## RFC-0005 S8cb, items 1 to 4: per-field address cells. `newSeq[T](n)` in a
## callee, a positional tuple's field cells, a multi-axis case object's arm
## field cells, and a whole `p[]` read asserting the pointee's declared ranges.
## Every expected value is checked against native Nim in the first test.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs:
    if e.severity != sevHint: parts.add $e.kind & ": " & e.msg
  "[" & parts.join(", ") & "]"

template c(name: untyped, want: SymexStatusKind, body: untyped) {.dirty.} =
  proc name(x: int, y: int) =
    body
  test astToStr(name):
    let r = symexFind(name, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == want

type
  K1 = enum k1a, k1b
  K2 = enum k2a, k2b
  MV = object
    h: int
    case k1: K1
    of k1a: y: int
    of k1b: u: string
    case k2: K2
    of k2a: z: int
    of k2b: w: bool
  Box = object
    p: ptr int
  TBox = object
    tp: ptr (int, int)
  MBox = object
    mp: ptr MV
  Small = range[0 .. 10]
  RO = object
    r: Small
    n: int
  RIn = object
    i: Small
  RNest = object
    inner: RIn
    a: array[2, Small]
  Col = enum red, green, blue
  Ce = range[red .. green]
  RE = object
    e: Ce
  D = distinct int

proc mkSeq(n: int): seq[int] =
  result = newSeq[int](n)

proc mkSeqS(n: int): seq[string] =
  result = newSeq[string](n)

proc stampY(p: ptr int) =
  p[] = 11

proc stampT(p: ptr (int, int)) =
  p[] = (21, 22)

proc stampF(p: ptr int) =
  p[] = 31

var gHold: ptr int

proc holdIt(p: ptr int) =
  gHold = p

proc lookT(p: ptr (int, string)): int =
  p[][1].len

suite "RFC-0005 S8cb cells: the walker floor":
  test "symexWalkerVersion is at least 243":
    check parseInt(symexWalkerVersion) >= 243

suite "RFC-0005 S8cb cells: native Nim":
  test "the expected values":
    var t = (5, 6)
    let q = addr t[1]
    q[] = 7
    check t == (5, 7)
    let r0 = addr t[0]
    t[0] = 8
    check r0[] == 8
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let py = addr o.y
    let pz = addr o.z
    py[] = 5
    pz[] = 6
    check o.y == 5 and o.z == 6
    o.z = 9
    check pz[] == 9
    let s = mkSeq(3)
    check s.len == 3 and s[2] == 0
    let ss = mkSeqS(2)
    check ss[1] == ""
    var b = Box(p: addr t[1])
    b.p[] = 40
    check t[1] == 40

suite "RFC-0005 S8cb cells (1): newSeq in a callee":
  c(callee, sxSat):
    let s = mkSeq(3)
    if s.len == 3 and s[2] == 0 and x == 1: symexTarget("t")
  c(calleeu, sxUnsat):
    let s = mkSeq(3)
    if s[2] != 0 and x == 1: symexTarget("t")
  c(calleelenu, sxUnsat):
    let s = mkSeq(3)
    if s.len != 3: symexTarget("t")
  c(calleestr, sxUnsat):
    let s = mkSeqS(2)
    if s[1] != "": symexTarget("t")

suite "RFC-0005 S8cb cells (2): a positional tuple's fields":
  c(viaptr, sxUnsat):
    var t = (5, 6)
    let p = addr t
    p[][1] = 7
    if t[1] != 7: symexTarget("t")
  c(fieldptr, sxSat):
    var t = (x, 6)
    let p = addr t[1]
    p[] = 7
    if t[0] == 1 and t[1] == 7 and x == 1: symexTarget("t")
  c(fieldptru, sxUnsat):
    var t = (x, 6)
    let p = addr t[1]
    p[] = 7
    if t[1] != 7: symexTarget("t")
  c(fieldread, sxUnsat):
    var t = (5, 6)
    let p = addr t[0]
    t[0] = x
    if p[] != x: symexTarget("t")
  c(fieldother, sxUnsat):
    var t = (5, 6)
    let p = addr t[0]
    p[] = x
    if t[1] != 6: symexTarget("t")
  c(fieldbox, sxUnsat):
    var t = (5, 6)
    let b = Box(p: addr t[1])
    b.p[] = x
    if t[1] != x: symexTarget("t")
  c(fieldcallee, sxUnsat):
    var t = (5, 6)
    stampF(addr t[1])
    if t[1] != 31 or t[0] != 5: symexTarget("t")
  c(wholecallee, sxUnsat):
    var t = (5, 6)
    stampT(addr t)
    if t[0] != 21 or t[1] != 22: symexTarget("t")
  c(tboxwhole, sxUnsat):
    var t = (5, x)
    let b = TBox(tp: addr t)
    b.tp[][0] = 9
    if t[0] != 9 or t[1] != x: symexTarget("t")
  c(strfield, sxUnsat):
    var t = (x, "abc")
    let p = addr t
    if lookT(p) != 3: symexTarget("t")
  c(nested, sxUnsat):
    var t = (1, (2, 3))
    let p = addr t
    p[][1][1] = x
    if t[1][1] != x or t[1][0] != 2: symexTarget("t")
  c(whole, sxUnsat):
    var t = (5, x)
    let p = addr t
    let w = p[]
    t[0] = 9
    if w[0] != 5 or p[][0] != 9: symexTarget("t")
  c(fieldwhole, sxUnsat):
    var t = (5, 6)
    let p = addr t
    let q = addr t[1]
    q[] = x
    if p[][1] != x: symexTarget("t")
  c(wholefield, sxUnsat):
    var t = (5, 6)
    let p = addr t
    let q = addr t[1]
    p[][1] = x
    if q[] != x: symexTarget("t")
  c(wholename, sxUnsat):
    var t = (5, 6)
    let q = addr t[1]
    t = (x, x)
    if q[] != x: symexTarget("t")

suite "RFC-0005 S8cb cells (3): a multi-axis case object's arm fields":
  c(armbox, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let b = Box(p: addr o.y)
    b.p[] = x
    if o.y != x or o.z != 2: symexTarget("t")
  c(armlocal, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let b = addr o.z
    o.z = x
    if b[] != x: symexTarget("t")
  c(armwrite, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let b = addr o.z
    b[] = x
    if o.z != x or o.y != 1: symexTarget("t")
  c(armsat, sxSat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let b = Box(p: addr o.z)
    b.p[] = x
    if o.z == 4 and x == 4: symexTarget("t")
  c(armcallee, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    stampY(addr o.y)
    if o.y != 11 or o.z != 2: symexTarget("t")
  c(armhold, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    holdIt(addr o.z)
    gHold = nil
    if o.z != 2: symexTarget("t")
  c(armwrongfield, sxSat):
    var o = MV(k1: k1b, u: "a", k2: k2a, z: 2)
    try:
      let b = Box(p: addr o.y)
      discard b
    except FieldDefect:
      if x == 1: symexTarget("t")
  c(armwrongfieldu, sxUnsat):
    var o = MV(k1: k1a, y: 3, k2: k2a, z: 2)
    try:
      let b = Box(p: addr o.y)
      discard b
    except FieldDefect:
      symexTarget("t")
  c(otheraxislive, sxUnsat):
    var o = MV(k1: k1a, y: 3, k2: k2a, z: 2)
    let b = Box(p: addr o.y)
    o = MV(k1: k1a, y: 3, k2: k2b, w: true)
    b.p[] = x
    if o.y != x: symexTarget("t")
  c(otheraxisdead, sxUnknown):
    var o = MV(k1: k1a, y: 3, k2: k2a, z: 2)
    let b = Box(p: addr o.y)
    o = MV(k1: k1b, u: "s", k2: k2a, z: 2)
    b.p[] = x
    if x == 1: symexTarget("t")
  c(otheraxisname, sxUnsat):
    var o = MV(k1: k1a, y: 3, k2: k2a, z: 2)
    let b = Box(p: addr o.y)
    o = MV(k1: k1a, y: x, k2: k2b, w: true)
    if b.p[] != x: symexTarget("t")
  c(whole, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let b = addr o
    b[].z = x
    if o.z != x or b[].y != 1: symexTarget("t")
  c(wholename, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let b = addr o
    o.y = x
    if b[].y != x: symexTarget("t")
  c(wholebox, sxUnsat):
    var o = MV(k1: k1a, y: 1, k2: k2a, z: 2)
    let b = MBox(mp: addr o)
    b.mp[].y = x
    if o.y != x: symexTarget("t")

proc rangeObj(p: ptr RO) =
  if p != nil:
    let w = p[]
    if w.r > 10 or w.r < 0: symexTarget("t")

proc rangeObjSat(p: ptr RO) =
  if p != nil:
    let w = p[]
    if w.r == 10 and w.n == 99: symexTarget("t")

proc rangeRef(p: ref RO) =
  if p != nil:
    let w = p[]
    if int(w.r) > 10: symexTarget("t")

proc rangeNested(p: ptr RNest) =
  if p != nil:
    let w = p[]
    if int(w.inner.i) > 10: symexTarget("t")

proc rangeNestedArr(p: ptr RNest) =
  if p != nil:
    let w = p[]
    if int(w.a[1]) > 10: symexTarget("t")

proc rangeEnum(p: ptr RE) =
  if p != nil:
    let w = p[]
    if ord(w.e) == 2: symexTarget("t")

proc rangeTuple(p: ptr tuple[r: Small, n: int]) =
  if p != nil:
    let w = p[]
    if int(w.r) > 10: symexTarget("t")

proc rangeInline(p: ptr RO) =
  if p != nil:
    if p[].r > 10: symexTarget("t")

suite "RFC-0005 S8cb cells (4): a whole read asserts the declared ranges":
  test "a ptr object's range field":
    check symexFind(rangeObj, tLabel("t")).status == sxUnsat
  test "and the values in range are reached":
    check symexFind(rangeObjSat, tLabel("t")).status == sxSat
  test "a ref object's range field":
    check symexFind(rangeRef, tLabel("t")).status == sxUnsat
  test "a nested object's range field":
    let r = symexFind(rangeNested, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
  test "an array field's range elements":
    let r = symexFind(rangeNestedArr, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
  test "an enum range field":
    let r = symexFind(rangeEnum, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
  test "a named tuple's range field":
    let r = symexFind(rangeTuple, tLabel("t"))
    checkpoint show(r.errors)
    check r.status == sxUnsat
  test "a field read of the same pointer":
    check symexFind(rangeInline, tLabel("t")).status == sxUnsat
