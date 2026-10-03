## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 1:
## a walk that never terminated.
##
## An `int` read from an Int-sorted heap (an `int` field, a `ptr int` cell)
## and linked to a bit-vector return value or local gave Z3 an UNSAT query
## over the signed `bv2int` bridge it did not decide: `sbv2int(r) ==
## sbv2int(k) and r != k`, or `r == int2bv(sbv2int(k)) and r != k`. Under
## the default `queryRLimit` (then 0, unbounded) the walk never finished.
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (1) the shapes decide: beside the query, each bit-vector whose signed
##       Int view it holds is asserted equal to `int2bv` of that view, a
##       theorem of two's complement (`bvIntInverseFacts`);
##   (2) no query is unbounded under the defaults: `queryRLimit` defaults
##       to a finite budget, and a query that exhausts it is `sxUnknown`
##       with the decline named (`beSolverUndef`), never a hang.
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

suite "S8bu (1): the signed bv2int bridge decides":

  test "nim: the int forms":
    let ks = [-1, 0, 5, 29, 33]
    let h = nativeHits(sutIntField, ks) + nativeHits(sutSeqInt, ks)
    for l in ["tf", "ts"]:
      checkpoint l & " " & $(l in h) & " " & $((l & "_dead") in h)
      check l in h
      check (l & "_dead") notin h

  test "the int forms":
    clean(sutIntField, "tf", sxSat)
    clean(sutIntField, "tf_dead", sxUnsat)
    clean(sutSeqInt, "ts", sxSat)
    clean(sutSeqInt, "ts_dead", sxUnsat)

  test "the inverse facts are theorems":
    ## Every fact `bvIntInverseFacts` states, at width 8 over every `x`, is
    ## valid: with `x` fixed, its negation is UNSAT.
    let ctx = newContext()
    let x = mkBitVecVar[8](ctx, "s8bu_x")
    let sv = wrap[Z3Int](ctx, ctx.checkErr Z3_mk_bv2int(ctx.raw, x.raw, true))
    var n = 0
    for xv in 0 .. 255:
      let facts = bvIntInverseFacts(ctx, [sv == sv])
      checkpoint $xv
      check facts.len == 1
      for f in facts:
        let s = querySolver(ctx, [x == mkBitVec[8](ctx, xv), not f], 0)
        check s.check() == zsUnsat
        inc n
    check n == 256

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

  test "queryRLimit defaults to a finite budget":
    check ResourceBudget().queryRLimit == 20_000_000'u
    check defaultSymexSettings().budget.queryRLimit != 0'u

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
