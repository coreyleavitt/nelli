## RFC-0005 (soundness channels) slice S8bf -- S8bd's soundness finding.
##
## Two `var` (or `ptr`) heap actuals reached through DIFFERENT refs to ONE
## cell: `let q = p; setBoth(p.x, q.x)` with a callee that writes `b`, then
## `a`. Nim passes both addresses, so the cell ends with `a`'s write. The
## copy-in/copy-out write-backs ran in ARGUMENT order and left `b`'s: a
## false `sxSat`. `varActualMayAlias` missed it: the other actual's type is
## `var int` (it holds no ref) and the two roots are different symbols.
##
## Pinned here (the RFC's "As landed (S8bf)" note has the design): every
## dead label below is one Nim provably cannot reach, beside a reachable
## twin, for a ref copied by `let`, through a `let` chain, held in a tuple,
## reached through a field of another ref, a parameter ref, a `var` formal
## forwarded to a second callee, and `addr` actuals.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

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

type Box = ref object
  x: int
  y: int
type Outer = ref object
  inner: Box

proc setBoth(a, b: var int) =
  ## Writes `b`, then `a`: on one cell, `a`'s write is the last.
  b = 2
  a = 1

proc fwd(a, b: var int) =
  ## A `var` formal forwarded to a second callee.
  setBoth(a, b)

proc setBothP(a, b: ptr int) =
  b[] = 2
  a[] = 1

proc setMix(a: var int; b: ptr int) =
  b[] = 2
  a = 1

proc sutLet(k: int) =
  let p = Box(x: k)
  let q = p
  setBoth(p.x, q.x)
  if p.x != 1: symexTarget("let_dead")
  if p.x == 1 and q.x == 1 and k == 3: symexTarget("let")

proc sutChain(k: int) =
  let p = Box(x: k)
  let q = p
  var r = q
  setBoth(p.x, r.x)
  if p.x != 1 or r.x != 1: symexTarget("chain_dead")
  if p.x == 1 and k == 4: symexTarget("chain")

proc sutTuple(k: int) =
  let p = Box(x: k)
  let t = (p, k)
  setBoth(p.x, t[0].x)
  if p.x != 1: symexTarget("tup_dead")
  if p.x == 1 and t[1] == 5: symexTarget("tup")

proc sutField(k: int) =
  let p = Box(x: k)
  let o = Outer(inner: p)
  setBoth(p.x, o.inner.x)
  if p.x != 1 or o.inner.x != 1: symexTarget("fld_dead")
  if o.inner.x == 1 and k == 6: symexTarget("fld")

proc sutFwd(k: int) =
  let p = Box(x: k)
  let q = p
  fwd(p.x, q.x)
  if p.x != 1: symexTarget("fwd_dead")
  if p.x == 1 and k == 7: symexTarget("fwd")

proc sutParam(p, q: Box) =
  ## Two parameter refs: one cell exactly when `p == q`.
  if p == nil or q == nil: return
  setBoth(p.x, q.x)
  if p == q and p.x != 1: symexTarget("par_dead")
  if p == q and p.x == 1: symexTarget("par_same")
  if p != q and p.x == 1 and q.x == 2: symexTarget("par_diff")
  if p != q and q.x != 2: symexTarget("par_diff_dead")

proc sutParamLet(p: Box; k: int) =
  ## A `let` copy of a parameter ref and the parameter itself.
  if p == nil: return
  let q = p
  setBoth(q.x, p.x)
  if q.x != 1: symexTarget("pl_dead")
  if p.x == 1 and k == 2: symexTarget("pl")

proc sutAddr(k: int) =
  let p = Box(x: k)
  let q = p
  setBothP(addr p.x, addr q.x)
  if p.x != 1: symexTarget("adr_dead")
  if p.x == 1 and k == 8: symexTarget("adr")

proc sutMix(k: int) =
  let p = Box(x: k)
  let q = p
  setMix(p.x, addr q.x)
  if p.x != 1: symexTarget("mix_dead")
  if p.x == 1 and k == 9: symexTarget("mix")

proc sutOtherField(k: int) =
  ## Different fields of one object never alias: the write-backs stay exact.
  let p = Box(x: k)
  let q = p
  setBoth(p.x, q.y)
  if p.x != 1 or q.y != 2: symexTarget("of_dead")
  if p.x == 1 and p.y == 2 and k == 1: symexTarget("of")

proc sutFresh(k: int) =
  ## Two distinct allocations: two cells, each with its own write.
  let p = Box(x: k)
  let q = Box(x: k)
  setBoth(p.x, q.x)
  if p.x != 1 or q.x != 2: symexTarget("fr_dead")
  if p.x == 1 and q.x == 2 and k == 2: symexTarget("fr")

proc sutSame(k: int) =
  ## One ref named twice: one cell, written in the callee's order.
  let p = Box(x: k)
  setBoth(p.x, p.x)
  if p.x != 1: symexTarget("ss_dead")
  if p.x == 1 and k == 5: symexTarget("ss")

proc sutElems(k: int) =
  ## Two elements of one array holding one ref.
  let p = Box(x: k)
  let a = [p, p]
  setBoth(a[0].x, a[1].x)
  if p.x != 1: symexTarget("el_dead")
  if p.x == 1 and k == 6: symexTarget("el")

proc sutPtrBox(pb: ptr Box; q: Box) =
  ## `pb[].x` cannot be passed by reference (its ref is reached through a
  ## pointer dereference): it takes the write-back, which declines.
  if pb == nil or q == nil or pb[] == nil: return
  setBoth(pb[].x, q.x)
  if pb[] == q and q.x != 1: symexTarget("pb_dead")

suite "S8bf: two var heap actuals through different refs to one cell":

  test "nim":
    let p = Box(x: 3)
    let q = p
    setBoth(p.x, q.x)
    check p.x == 1
    var r = q
    fwd(p.x, r.x)
    check p.x == 1
    let o = Outer(inner: p)
    setBoth(p.x, o.inner.x)
    check o.inner.x == 1
    let t = (p, 0)
    setBoth(t[0].x, p.x)
    check p.x == 1
    setBothP(addr p.x, addr q.x)
    check p.x == 1
    setMix(p.x, addr q.x)
    check p.x == 1
    setBoth(p.x, q.y)
    check p.x == 1 and p.y == 2

  test "a let copy of the ref":
    ## RED: `sxSat` (a false one) -- the write-backs ran in argument order.
    discard clean(sutLet, "let_dead", sxUnsat)
    discard clean(sutLet, "let", sxSat)

  test "a let chain":
    discard clean(sutChain, "chain_dead", sxUnsat)
    discard clean(sutChain, "chain", sxSat)

  test "a ref held in a tuple":
    discard clean(sutTuple, "tup_dead", sxUnsat)
    discard clean(sutTuple, "tup", sxSat)

  test "a ref reached through a field of another ref":
    discard clean(sutField, "fld_dead", sxUnsat)
    discard clean(sutField, "fld", sxSat)

  test "a var formal forwarded to a second callee":
    discard clean(sutFwd, "fwd_dead", sxUnsat)
    discard clean(sutFwd, "fwd", sxSat)

  test "two parameter refs":
    discard clean(sutParam, "par_dead", sxUnsat)
    discard clean(sutParam, "par_same", sxSat)
    discard clean(sutParam, "par_diff", sxSat)
    discard clean(sutParam, "par_diff_dead", sxUnsat)

  test "a let copy of a parameter ref":
    discard clean(sutParamLet, "pl_dead", sxUnsat)
    discard clean(sutParamLet, "pl", sxSat)

  test "addr actuals":
    discard clean(sutAddr, "adr_dead", sxUnsat)
    discard clean(sutAddr, "adr", sxSat)
    discard clean(sutMix, "mix_dead", sxUnsat)
    discard clean(sutMix, "mix", sxSat)

  test "no alias: different fields, different allocations":
    discard clean(sutOtherField, "of_dead", sxUnsat)
    discard clean(sutOtherField, "of", sxSat)
    discard clean(sutFresh, "fr_dead", sxUnsat)
    discard clean(sutFresh, "fr", sxSat)

  test "one ref named twice (was a decline)":
    ## Before S8bf: `sxUnknown`, `feUnsupportedOp` (`varActualMayAlias`
    ## saw the shared root and declined the write-back).
    discard clean(sutSame, "ss_dead", sxUnsat)
    discard clean(sutSame, "ss", sxSat)
    discard clean(sutElems, "el_dead", sxUnsat)
    discard clean(sutElems, "el", sxSat)

  test "an actual that cannot be passed by reference declines":
    let r = symexFind(sutPtrBox, tLabel("pb_dead"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and "`pb[].x`" in e.msg: named = true
    check named

suite "S8bf: walker version":
  test "symexWalkerVersion >= 206":
    check parseInt(symexWalkerVersion) >= 206
