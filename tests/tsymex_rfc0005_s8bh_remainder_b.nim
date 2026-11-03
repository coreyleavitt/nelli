## RFC-0005 (soundness channels) slice S8bh -- S8bf's remainder.
##
## Three soundness findings S8bf reported and did not fix:
##
## 1. A call through a proc-valued variable dropped its `var` writes: the
##    closure-call arm (`applyClosureGround`) lowered the arguments by value
##    and had no copy-out, so `let f = setBoth; f(x, y)` left `x` as it was
##    (a false `sxSat` for `x != 1`). The same held for every indirect call
##    that reaches that arm: a lambda, a generic callee's proc parameter, a
##    proc passed to a callee, and a heap actual (`f(p.x, y)`).
## 2. A `ptr` parameter never addressed a ref object's field: `q.x = 1;
##    pi[] = 2; if q.x == 2` was `sxUnsat`, but Nim reaches it with
##    `pi = addr q.x`.
## 3. Converting a ref up its inheritance chain built an ill-sorted term:
##    `Base(d) == b` was `weInternalWalkerFault`.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 2 of 6 of this suite, with
## `tsymex_rfc0005_s8bh_remainder`, `tsymex_rfc0005_s8bh_remainder_c`,
## `tsymex_rfc0005_s8bh_remainder_d`, `tsymex_rfc0005_s8bh_remainder_e`,
## `tsymex_rfc0005_s8bh_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 112 s).

import std/[unittest, strutils, options]
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
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

# ---- 1. var writes through an indirect call ---------------------------------

type Box = ref object
  x: int
  y: int

proc setBoth(a, b: var int) =
  ## Writes `b`, then `a`: on one location, `a`'s write is the last.
  b = 2
  a = 1

proc setOne(a: var int) =
  a = 4

proc sutField(k: int) =
  ## A field of a value tuple.
  var t = (a: k, b: k)
  let f = setOne
  f(t.a)
  if t.a != 4 or t.b != k: symexTarget("vf_dead")
  if t.a == 4 and k == 8: symexTarget("vf")

proc sutHeap(k: int) =
  let f = setBoth
  let p = Box(x: k)
  var y = k
  f(p.x, y)
  if p.x != 1 or y != 2: symexTarget("h_dead")
  if p.x == 1 and k == 3: symexTarget("h")

proc sutHeapPeers(k: int) =
  ## Two heap actuals through different refs to one cell (S8bf's shape).
  let f = setBoth
  let p = Box(x: k)
  let q = p
  f(p.x, q.x)
  if p.x != 1: symexTarget("hp_dead")
  if q.x == 1 and k == 4: symexTarget("hp")

proc sutHeapParams(p, q: Box) =
  ## Two parameter refs: one cell exactly when `p == q`.
  if p == nil or q == nil: return
  let f = setBoth
  f(p.x, q.x)
  if p == q and p.x != 1: symexTarget("hq_dead")
  if p == q and p.x == 1: symexTarget("hq_same")
  if p != q and p.x == 1 and q.x == 2: symexTarget("hq_diff")
  if p != q and q.x != 2: symexTarget("hq_diff_dead")

proc sutHeapFresh(k: int) =
  ## Two allocations: two cells, each with its own write.
  let f = setBoth
  let p = Box(x: k)
  let q = Box(x: k)
  f(p.x, q.x)
  if p.x != 1 or q.x != 2: symexTarget("hf_dead")
  if p.x == 1 and q.x == 2 and k == 5: symexTarget("hf")

proc setBothP(a, b: ptr int) =
  b[] = 2
  a[] = 1

proc sutAddr(k: int) =
  let f = setBothP
  var x = k
  var y = k
  f(addr x, addr y)
  if x != 1 or y != 2: symexTarget("ad_dead")
  if x == 1 and k == 6: symexTarget("ad")

proc sutAddrSame(k: int) =
  let f = setBothP
  var x = k
  f(addr x, addr x)
  if x != 1: symexTarget("as_dead")
  if x == 1 and k == 7: symexTarget("as")

proc sutAddrPeers(k: int) =
  let f = setBothP
  let p = Box(x: k)
  let q = p
  f(addr p.x, addr q.x)
  if p.x != 1: symexTarget("ap_dead")
  if p.x == 1 and k == 8: symexTarget("ap")

type Ops = object
  f: proc (a, b: var int) {.nimcall.}

suite "S8bh (1): var writes through an indirect call":
  test "a field of a value tuple":
    discard clean(sutField, "vf_dead", sxUnsat)
    discard clean(sutField, "vf", sxSat)

  test "a heap actual":
    discard clean(sutHeap, "h_dead", sxUnsat)
    discard clean(sutHeap, "h", sxSat)

  test "two heap actuals through different refs (S8bf's peers)":
    discard clean(sutHeapPeers, "hp_dead", sxUnsat)
    discard clean(sutHeapPeers, "hp", sxSat)
    discard clean(sutHeapParams, "hq_dead", sxUnsat)
    discard clean(sutHeapParams, "hq_same", sxSat)
    discard clean(sutHeapParams, "hq_diff", sxSat)
    discard clean(sutHeapParams, "hq_diff_dead", sxUnsat)
    discard clean(sutHeapFresh, "hf_dead", sxUnsat)
    discard clean(sutHeapFresh, "hf", sxSat)

  test "addr actuals":
    ## Before S8bh: `feUnsupportedExprKind` (`nnkAddr`), a decline.
    discard clean(sutAddr, "ad_dead", sxUnsat)
    discard clean(sutAddr, "ad", sxSat)
    discard clean(sutAddrSame, "as_dead", sxUnsat)
    discard clean(sutAddrSame, "as", sxSat)
    discard clean(sutAddrPeers, "ap_dead", sxUnsat)
    discard clean(sutAddrPeers, "ap", sxSat)

# ---- 2. a ptr of unknown origin --------------------------------------------
#
# RFC-0005 S8bh item 2. A `ptr T` the SUT is handed (a parameter, a global,
# a field it reads) addressed only its own `ptr`-family cells: never a ref
# object's field, a global or a `var` parameter of type T, which Nim
# reaches with `addr q.x`, `addr g`, `addr v`.

type PQ = ref object
  x: int
  s: string
  b: bool
