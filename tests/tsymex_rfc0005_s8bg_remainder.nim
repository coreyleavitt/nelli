## RFC-0005 (soundness channels) slice S8bg -- S8bd's remainder.
##
## Pinned here (the RFC's "As landed (S8bg)" note has the design):
##   (1) `byRefSub` accepts a `var`/`addr` actual reached through a
##       representation-preserving conversion (`distinct` unwrap/rewrap, a
##       `range` to its base) wrapping the whole lvalue (`int(b.m)`, the
##       only shape a representation-preserving conversion can take here:
##       to sit any deeper, at the operand of the mandatory deref further
##       down the chain, it would have to convert TO a ref/ptr, which only
##       inheritance does, and that is NOT representation-preserving in
##       this engine). A `ref`/`ptr` inheritance up/downcast stays
##       declining (a different Z3 sort per declared type; see the "not
##       fixed here" note below).
##   (2) a `var`/`addr` actual reached through a `cast` (a genuine
##       reinterpretation) gets a scoped decline naming the cast, in place
##       of a crash the ordinary read machinery hit for it.
##   (3) `geDistinctBijectivitySkipped` walks the whole `distinct` chain to
##       the real base before judging non-decidability: a `seq[Km]` (`Km =
##       distinct Meters`, `Meters = distinct int`) no longer wrongly
##       claims a non-decidable base.
##   (4) today's decline for a pointer dereference passed further by
##       reference to a "known heap cell" (S8an's `addr lv`-bound `ptr T`
##       formal) is pinned as ALREADY MODELED on this base (no byRefSub
##       change was needed for it) -- see the note on probe A below.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

# ---- (4) a pointer dereference to a "known heap cell" is already modeled ----
#
# `addr b.x` bound DIRECTLY to a `ptr int` FORMAL (S8an's mechanism: the
# formal's own cell) was never byRefSub's gap -- the formal is a bare
# symbol, the shape `byRefSub`'s existing dispatch already names. Pinned
# here as a regression (the S8bd note's "by the code path; not pinned").

type Box = ref object
  x: int

var gBoxA: Box

proc setXG(v: var int, k: int) =
  v = k
  gBoxA.x = 5

proc innerPtr(pb: ptr int, k: int) =
  setXG(pb[], k)

proc sutPtrFormalDeref(k: int) =
  let b = Box(x: 0)
  gBoxA = b
  innerPtr(addr b.x, k)
  if b.x == 5 and gBoxA.x == 5 and k == 1: symexTarget("pfA")
  if b.x == k and k != 5: symexTarget("pfA_dead")

suite "S8bg (1): a known-heap-cell pointer dereference is modeled":

  test "nim":
    var b = Box(x: 0)
    gBoxA = b
    innerPtr(addr b.x, 1)
    check b.x == 5 and gBoxA.x == 5

  test "reachable twin replays, dead label is unsat":
    let r = clean(sutPtrFormalDeref, "pfA", sxSat)
    check replayWitness(sutPtrFormalDeref, r.witness, tLabel("pfA"), {}) ==
          roConfirmed
    discard clean(sutPtrFormalDeref, "pfA_dead", sxUnsat)

# ---- (1a) conversion: distinct, whole-lvalue ---------------------------------

type Meters = distinct int
type MBox = ref object
  m: Meters

var gMBox: MBox

proc setM(v: var int, k: int) =
  v = k
  gMBox.m = Meters(5)

proc sutConvDistinctWhole(k: int) =
  let b = MBox(m: Meters(0))
  gMBox = b
  setM(int(b.m), k)
  if int(b.m) == 5 and int(gMBox.m) == 5 and k == 1: symexTarget("cvd")
  if int(b.m) == k and k != 5: symexTarget("cvd_dead")

# ---- (1b) conversion: range to base, whole-lvalue ----------------------------

type Small = range[0..100]
type SBox = ref object
  m: Small

var gSBox: SBox

proc setS(v: var int, k: Small) =
  v = int(k)
  gSBox.m = Small(5)

proc sutConvRangeWhole(k: Small) =
  let b = SBox(m: Small(0))
  gSBox = b
  setS(int(b.m), k)
  if int(b.m) == 5 and int(gSBox.m) == 5 and int(k) == 1: symexTarget("cvr")
  if int(b.m) == int(k) and int(k) != 5: symexTarget("cvr_dead")

# ---- (1c) conversion: distinct, whole-lvalue, through a deeper ref chain ----

type Meters2 = distinct int
type Farm = ref object of RootObj
  m: Meters2
type FarmBox = ref object
  f: Farm

var gFarmBox: FarmBox

proc setFM(v: var int, k: int) =
  v = k
  gFarmBox.f.m = Meters2(5)

proc sutConvDistinctMid(k: int) =
  let fb = FarmBox(f: Farm(m: Meters2(0)))
  gFarmBox = fb
  # `int(fb.f.m)` -- the conversion wraps `fb.f.m` as a whole, the same
  # shape as (1a)'s, but through an extra ref hop (`fb.f`, not just `b`),
  # so this is its own pin against a regression in `heapSteps` bookkeeping
  # for the by-reference gate (`outerReachesCell`'s cell types).
  setFM(int(fb.f.m), k)
  if int(fb.f.m) == 5 and int(gFarmBox.f.m) == 5 and k == 1: symexTarget("cvm")
  if int(fb.f.m) == k and k != 5: symexTarget("cvm_dead")

suite "S8bg (2): a representation-preserving conversion lvalue is modeled":

  test "nim":
    block:
      var b = MBox(m: Meters(0))
      gMBox = b
      setM(int(b.m), 1)
      check int(b.m) == 5 and int(gMBox.m) == 5
    block:
      var b = SBox(m: Small(0))
      gSBox = b
      setS(int(b.m), Small(1))
      check int(b.m) == 5 and int(gSBox.m) == 5
    block:
      var fb = FarmBox(f: Farm(m: Meters2(0)))
      gFarmBox = fb
      setFM(int(fb.f.m), 1)
      check int(fb.f.m) == 5 and int(gFarmBox.f.m) == 5

  test "distinct, whole lvalue: reachable twin replays, dead label is unsat":
    let r = clean(sutConvDistinctWhole, "cvd", sxSat)
    check replayWitness(sutConvDistinctWhole, r.witness, tLabel("cvd"), {}) ==
          roConfirmed
    discard clean(sutConvDistinctWhole, "cvd_dead", sxUnsat)

  test "range to base, whole lvalue: reachable twin replays, dead label is unsat":
    let r = clean(sutConvRangeWhole, "cvr", sxSat)
    check replayWitness(sutConvRangeWhole, r.witness, tLabel("cvr"), {}) ==
          roConfirmed
    discard clean(sutConvRangeWhole, "cvr_dead", sxUnsat)

  test "distinct, through a deeper ref chain: reachable twin replays, dead label is unsat":
    let r = clean(sutConvDistinctMid, "cvm", sxSat)
    check replayWitness(sutConvDistinctMid, r.witness, tLabel("cvm"), {}) ==
          roConfirmed
    discard clean(sutConvDistinctMid, "cvm_dead", sxUnsat)

# ---- (2) cast: a scoped decline naming the cast, not a crash -----------------

type Box2 = ref object
  x: int

var gBoxC: Box2

proc setXC(v: var int, k: int) =
  v = k
  gBoxC.x = 5

proc sutCastLvalue(k: int) =
  let p = Box2(x: 0)
  gBoxC = p
  setXC(cast[ptr int](addr p.x)[], k)
  if p.x == 5 and gBoxC.x == 5 and k == 1: symexTarget("ccC")
  if p.x == k and k != 5: symexTarget("ccC_dead")

proc sutCastClosure(k: int) =
  ## RFC-0005 batch 5: the same actual through a proc value (S8bh's
  ## `closureCallIR`). Before batch 5 it was a `weInternalWalkerFault`
  ## (`lowerLeafInExpr` given the declined cast's dummy value).
  let p = Box2(x: 0)
  gBoxC = p
  let f = setXC
  f(cast[ptr int](addr p.x)[], k)
  if p.x == 5 and gBoxC.x == 5 and k == 1: symexTarget("ccF")
  if p.x == k and k != 5: symexTarget("ccF_dead")

suite "S8bg (3): a cast lvalue gets a scoped decline, not a crash":

  test "nim":
    var p = Box2(x: 0)
    gBoxC = p
    setXC(cast[ptr int](addr p.x)[], 1)
    check p.x == 5 and gBoxC.x == 5

  test "through a proc value, the decline names the cast too":
    block:
      var p = Box2(x: 0)
      gBoxC = p
      let f = setXC
      f(cast[ptr int](addr p.x)[], 1)
      check p.x == 5 and gBoxC.x == 5
    for r in [symexFind(sutCastClosure, tLabel("ccF")),
              symexFind(sutCastClosure, tLabel("ccF_dead"))]:
      checkpoint $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      var named = false
      for e in r.errors:
        check e.kind != weInternalWalkerFault
        if e.kind == feUnsupportedOp and "cast" in e.msg: named = true
      check named

  test "the decline names the cast":
    let r = symexFind(sutCastLvalue, tLabel("ccC"))
    checkpoint "ccC " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.len > 0
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and "cast" in e.msg: named = true
    check named
    let rd = symexFind(sutCastLvalue, tLabel("ccC_dead"))
    checkpoint "ccC_dead " & $rd.status & " " & show(rd.errors)
    check rd.status == sxUnknown
    named = false
    for e in rd.errors:
      if e.kind == feUnsupportedOp and "cast" in e.msg: named = true
    check named

# ---- (4) the distinct-chain-aware bijectivity hint ---------------------------

type DMeters = distinct int
type DKm = distinct DMeters        ## a distinct of a distinct, over int
type DTemp = distinct float        ## a genuinely non-decidable base

proc sutOneLevel(m: DMeters) =
  if int(m) == 7: symexTarget("one")

proc sutTwoLevel(k: DKm) =
  if int(DMeters(k)) == 9: symexTarget("two")

proc sutNonDecidable(t: DTemp) =
  if float(t) > 1.0: symexTarget("nd")

suite "S8bg (4): the bijectivity hint walks the whole distinct chain":

  test "nim":
    check int(DMeters(7)) == 7
    check int(DMeters(DKm(DMeters(9)))) == 9

  test "one level of distinct over int: no hint":
    discard clean(sutOneLevel, "one", sxSat)

  test "two levels over int (a distinct of a distinct): no hint":
    ## RED before this slice: wrongly carried `geDistinctBijectivitySkipped`
    ## naming the immediate base `itDistinct` as "non-decidable", though the
    ## chain's real base (`int`) is decidable.
    discard clean(sutTwoLevel, "two", sxSat)

  test "a genuinely non-decidable base still carries the hint, named by its real kind":
    let r = symexFind(sutNonDecidable, tLabel("nd"))
    checkpoint "nd " & $r.status & " " & show(r.errors)
    check r.status == sxSat
    check r.errors.len == 1
    check r.errors[0].kind == geDistinctBijectivitySkipped
    check r.errors[0].severity == sevHint
    check "itFloat64" in r.errors[0].msg

suite "S8bg: walker version":
  test "symexWalkerVersion >= 218":
    check parseInt(symexWalkerVersion) >= 218
