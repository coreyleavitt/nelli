## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 1:
## a walk that never terminated.
##
## An `int` read from an Int-sorted heap (an `int` field, a `ptr int` cell)
## and linked to a bit-vector return value or local gave Z3 an UNSAT query
## over the signed `bv2int` bridge it did not decide: `sbv2int(r) ==
## sbv2int(k) and r != k`, or `r == int2bv(sbv2int(k)) and r != k`. Under
## the default `queryRLimit` (then 0, unbounded) the walk never finished.
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (1) the shapes decide: beside the query, the inverse of each signed
##       Int view it holds -- an `int2bv` of the view is the bit-vector, and
##       two views it equates are of equal bit-vectors -- theorems of two's
##       complement (`bvIntInverseFacts`). Only terms the query holds are
##       related: an `int2bv` of every view made Z3 bit-blast S8ad's Int
##       quotients (`tsymex_rfc0005_s8ad_remainder` hung on Windows);
##   (2) arithmetic on an `int` read back out of an Int-sorted heap stays
##       in the bit-vector it was stored from: a literal beside it lowers as
##       that bit-vector (`probeProto`), so `v * 2` is `bvmul(2, k)`, not
##       `2 * sbv2int(k)`, which met the caller's bit-vector across the
##       bridge again in a query whose step count Z3 never advanced;
##   (3) no query is unbounded under the defaults: `queryRLimit` defaults
##       to a finite budget, and `queryTimeoutMs` bounds every solve by the
##       clock (a step bound cannot end a search that takes no steps); a
##       solve either cuts off is `sxUnknown` with the decline named
##       (`beSolverUndef`), never a hang, and a clock cut-off is not cached.
##
## Every verdict expectation is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/engine/markers
import z3

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

# ---- (1) the int-field form: a by-address `int` field read by a callee ----

type BigI = object
  x, a, b, c: int

type HoldBigI = object
  bg: BigI
  n: int

var gphi: ptr HoldBigI

proc rdBigI(b: BigI, k: int): int =
  gphi[].bg.x = k
  b.x

proc sutIntField(k: int) =
  var h = HoldBigI(bg: BigI(x: 0), n: 0)
  gphi = addr h
  let r = rdBigI(h.bg, k)
  if r == k and k == 33: symexTarget("tf")
  if r != k: symexTarget("tf_dead")

# ---- (1) the `seq[int]` form: an element cell read by a callee -------------

var gpi: ptr int

proc rdSeqI(t: seq[int], k: int): int =
  gpi[] = k
  t[0]

proc sutSeqInt(k: int) =
  var s = @[0, 0]
  gpi = addr s[0]
  let r = rdSeqI(s, k)
  if r == k and k == 29: symexTarget("ts")
  if r != k: symexTarget("ts_dead")

# ---- (2) arithmetic on an `int` read back out of an Int-sorted heap -------

proc twice(v: var int, k: int): int =
  v = k
  gpi[] = v * 2
  v

proc sutHeapArith(k: int) =
  if k < 0 or k > 1000: return
  var x = 0
  gpi = addr x
  let r = twice(x, k)
  if r == 2 * k and x == 2 * k and k == 5: symexTarget("ta")
  if r != 2 * k or x != 2 * k: symexTarget("ta_dead")

# ---- (3) a solve whose answer takes Z3 long ---------------------------------

proc sutCubes(x, y, z: int) =
  if x > 0 and y > 0 and z > 0 and x < 1000 and y < 1000 and z < 1000:
    if x * x * x + y * y * y == z * z * z: symexTarget("tc")

const clockOnly = SymexSettings(budget: ResourceBudget(queryRLimit: 0,
                                                       queryTimeoutMs: 2000))

suite "S8bu (1): the signed bv2int bridge decides":

  test "nim: the int forms":
    let ks = [-1, 0, 5, 29, 33]
    let h = nativeHits(sutIntField, ks) + nativeHits(sutSeqInt, ks) +
            nativeHits(sutHeapArith, ks)
    for l in ["tf", "ts", "ta"]:
      checkpoint l & " " & $(l in h) & " " & $((l & "_dead") in h)
      check l in h
      check (l & "_dead") notin h

  test "the int forms":
    clean(sutIntField, "tf", sxSat)
    clean(sutIntField, "tf_dead", sxUnsat)
    clean(sutSeqInt, "ts", sxSat)
    clean(sutSeqInt, "ts_dead", sxUnsat)

  test "arithmetic on a value read back out of an Int heap":
    clean(sutHeapArith, "ta", sxSat)
    clean(sutHeapArith, "ta_dead", sxUnsat)

  test "the inverse facts are theorems":
    ## Both forms `bvIntInverseFacts` states (an `int2bv` of a view the
    ## query holds is its bit-vector; two views are equal only for equal
    ## bit-vectors) are valid at width 8, for every `x` and `y`: with both
    ## free, each one's negation is UNSAT.
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bu_x")
    let y = mkBitVecVar[8](ctx, "s8bu_y2")
    proc sv(b: Z3BitVec[8]): Z3Int =
      wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, b.raw, true))
    let back = wrap[Z3BitVec[8]](ctx, ctx.checkErr Z3_mk_int2bv(ctx.raw, 8,
                                                               sv(x).raw))
    let facts = bvIntInverseFacts(ctx, [back == back, sv(x) == sv(y)])
    check facts.len == 2
    # And through a heap cell: `y`'s view stored, then read back.
    let h = wrap[Z3AnyAst](ctx,
      checkedStore(ctx, mkArrayVar[Z3Int, Z3Int](ctx, "s8bu_h").raw,
                   mkInt(ctx, 0).raw, sv(y).raw))
    let rd = wrap[Z3Int](ctx, checkedSelect(ctx, h.raw, mkInt(ctx, 0).raw))
    let viaHeap = bvIntInverseFacts(ctx, [sv(x) == rd])
    check viaHeap.len == 1
    for f in facts & viaHeap:
      checkpoint $f
      check querySolver(ctx, [not f], 0).check() == zsUnsat

  test "no fact brings a term the query does not hold":
    ## A view with no `int2bv` of it, and two views the query does not
    ## equate: no fact (an `int2bv` of every view made Z3 bit-blast the Int
    ## arithmetic of `tsymex_rfc0005_s8ad_remainder`'s quotients).
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bu_z")
    let y = mkBitVecVar[8](ctx, "s8bu_z2")
    let sx = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, x.raw, true))
    let sy = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, y.raw, true))
    check bvIntInverseFacts(ctx, [sx > mkInt(ctx, 3), sx <= sy]).len == 0

  test "an unsigned-only view is not linked":
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bu_y")
    let uv = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, x.raw, false))
    check bvIntInverseFacts(ctx, [uv > mkInt(ctx, 3)]).len == 0

  test "the bridge shapes decide offline, under a small budget":
    ## The two walker queries, rebuilt at width 64: `checkCapped` decides
    ## them through `trySolve`'s path; here the facts alone are shown to.
    let ctx = newContext()
    let k = mkBitVecVar[64](ctx, "s8bu_k")
    let r = mkBitVecVar[64](ctx, "s8bu_r")
    proc sv(b: Z3BitVec[64]): Z3Int =
      wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, b.raw, true))
    let back = wrap[Z3BitVec[64]](ctx, ctx.checkErr Z3_mk_int2bv(ctx.raw, 64,
                                                                sv(k).raw))
    for q in [@[sv(r) == sv(k), r != k], @[r == back, r != k]]:
      let s = querySolver(ctx, q & bvIntInverseFacts(ctx, q), 100_000'u)
      check s.check() == zsUnsat

suite "S8bu (1): no query is unbounded under the defaults":

  test "queryRLimit and queryTimeoutMs default to finite budgets":
    check ResourceBudget().queryRLimit == 250_000_000'u
    # The solves `defaultConcreteBranchRLimit` bounds keep it.
    check concreteBranchRLimit(defaultSymexSettings()) ==
          defaultConcreteBranchRLimit
    check taintedSolveRLimit(defaultSymexSettings()) ==
          defaultConcreteBranchRLimit
    check defaultSymexSettings().budget.queryRLimit != 0'u
    check ResourceBudget().queryTimeoutMs == 600_000'u
    check ";qto=" notin canonicalize(defaultSymexSettings())
    check ";qto=2000" in canonicalize(clockOnly)

  test "a solve the clock cuts off declines, named, and is not cached":
    ## No step bound at all (`queryRLimit: 0`); the cubes query is one Z3
    ## does not answer in 2 s.
    let r = symexFind(sutCubes, tLabel("tc"), clockOnly)
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == beSolverUndef and "queryTimeoutMs = 2000" in e.msg:
        named = true
    check named
    check symexQueryTimedOut()

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
