## S8cp item 2 (uncheckedAssign), S8cb's threadvar item, and hook variants of the
## havoc pattern: the walker's view of compiler-inserted calls, with and without a
## global read first.
import h

type
  K = enum kA, kB, kC
  V = object
    case k: K
    of kA, kB: x: int
    of kC: y: int

proc ua1(v: int) = # a change that keeps the branch
  var o = V(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kB
  if o.k == kB and o.x == v: symexTarget("ua1_live")
  if o.x != v: symexTarget("ua1_dead")
proc ua2(v: int) = # a change of branch
  var o = V(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kC
  if o.k == kC: symexTarget("ua2_live")
  if o.k != kC: symexTarget("ua2_dead")
proc ua3(v: int) = # read the other arm over the same bytes
  var o = V(k: kA, x: v)
  {.cast(uncheckedAssign).}:
    o.k = kC
  if o.y == v: symexTarget("ua3_same")
  if o.y != v: symexTarget("ua3_diff")

# threadvar behind a routine of the same signature
var tv {.threadvar.}: int
var tvOut = 0
proc tvLook(v: int) {.symexOpaque.} =
  tvOut = tv
proc tvBehind(v: int) =
  symexAssume(v == 3)
  tvLook(v)
  if tvOut == 7: symexTarget("tv_hit")

# ---- hooks with no global read first ---------------------------------------------
var gW: int
type D = object
  v: int
proc `=destroy`(d: D) = gW = 1
proc mkD(k: int): D = D(v: k)
proc dg1(k: int) = # the hook writes a global the SUT wrote first (no havoc)
  gW = 0
  block:
    var d = mkD(k)
    d.v = k + 1
  if gW == 1: symexTarget("dg1_live")
  if gW == 0: symexTarget("dg1_dead")

type DR = object
  r: ref int
proc `=destroy`(d: DR) =
  if d.r != nil: d.r[] = 1
proc dg2(k: int) = # the hook writes through a ref the SUT holds
  let r = new int
  r[] = 0
  block:
    var d = DR(r: r)
    discard d.r
  if r[] == 1: symexTarget("dg2_live")
  if r[] == 0: symexTarget("dg2_dead")
proc dg3(k: int) = # the hook of a callee's local
  gW = 0
  proc inner() =
    var d = mkD(k)
    d.v = k + 1
  inner()
  if gW == 1: symexTarget("dg3_live")
  if gW == 0: symexTarget("dg3_dead")
proc dg4(k: int) = # read first, callee's local: the havoc pattern again
  let a = gW
  proc inner() =
    var d = mkD(k)
    d.v = k + 1
  inner()
  if gW != a and a != 1: symexTarget("dg4_live")
proc dg5(k: int) = # the hook runs on overwrite
  gW = 0
  var d = mkD(k)
  d = mkD(k + 1)
  if gW == 1: symexTarget("dg5_live")
  if gW == 0: symexTarget("dg5_dead")

type DS = object
  v: int
var gDsCount: int
proc `=sink`(d: var DS; s: DS) =
  d.v = s.v
  gDsCount = gDsCount + 1
proc `=copy`(d: var DS; s: DS) =
  d.v = s.v
  gDsCount = gDsCount + 100
proc mkS(k: int): DS = DS(v: k)
proc ds1(k: int) = # a sink hook on assignment
  gDsCount = 0
  var d: DS
  d = mkS(k)
  if gDsCount != 0: symexTarget("ds1_live")
  if gDsCount == 0: symexTarget("ds1_dead")
proc ds2(k: int) = # a copy hook on assignment
  gDsCount = 0
  var s = DS(v: k)
  var d: DS
  d = s
  s.v = 0
  if gDsCount != 0: symexTarget("ds2_live")
  if gDsCount == 0: symexTarget("ds2_dead")

type Dvs = object
  s: string
var gHit: int
proc `=destroy`(d: Dvs) =
  gHit = gHit + 1
  `=destroy`(d.s)
proc dv1(s: seq[int]) = # the hook of the elements of a local seq
  gHit = 0
  block:
    var xs = @[Dvs(s: "a")]
    xs[0].s = "b"
  if gHit > 0: symexTarget("dv1_live")
  if gHit == 0: symexTarget("dv1_dead")

for k in [-1, 0, 1, 3]:
  nat(ua1(k)); nat(ua2(k)); nat(ua3(k))
  nat(dg1(k)); nat(dg2(k)); nat(dg3(k)); gW = 7; nat(dg4(k)); nat(dg5(k)); nat(ds1(k)); nat(ds2(k))
  nat(dv1(@[k]))
tv = 7
nat(tvBehind(3))
natDump()
v(ua1, "ua1_live")
v(ua1, "ua1_dead")
v(ua2, "ua2_live")
v(ua2, "ua2_dead")
v(ua3, "ua3_same")
v(ua3, "ua3_diff")
v(tvBehind, "tv_hit")
v(dg1, "dg1_live")
v(dg1, "dg1_dead")
v(dg2, "dg2_live")
v(dg2, "dg2_dead")
v(dg3, "dg3_live")
v(dg3, "dg3_dead")
v(dg4, "dg4_live")
v(dg5, "dg5_live")
v(dg5, "dg5_dead")
v(ds1, "ds1_live")
v(ds1, "ds1_dead")
v(ds2, "ds2_live")
v(ds2, "ds2_dead")
v(dv1, "dv1_live")
v(dv1, "dv1_dead")
