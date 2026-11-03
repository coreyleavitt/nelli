## RFC-0005 (soundness channels) slice S8ba -- S8au's remainder.
##
## Pinned here (the RFC's "As landed (S8ba)" note has the design and the
## measurements):
##   (1) a declined seq read left its compiler temporary (`__sym_idx_N`)
##       unbound, and the next read of it was recorded as an unmodelled
##       global (`feGlobalReadUnmodelled`). Every declining arm that owns a
##       result now binds it; a parser temporary read unbound is a walker
##       fault, never a global; a global write next to a temporary is
##       still seen;
##   (2) a `seq` of a distinct type is modelled: the backing array holds
##       the base sort, and an element is re-boxed on every read;
##   (3) every string / seq leaf has `len <= high(int)` (Nim's `len` is a
##       non-negative `int`), so an overflow or range raise path over a
##       string-derived index decides, in both integer encodings;
##   (4) a `var` / `addr` actual whose heap cell the callee can also reach
##       through a global or a capture is passed by reference through that
##       cell (S8au declined it): S8au's five dead labels are `sxUnsat`;
##   (5) a split's axioms are built once, by the first query that reaches
##       it, newly reached splits in lowering order and before any chain or
##       link fact; later queries reuse them. S8ag's B1-1 probe is the
##       canary (a unit ceiling, both Z3 versions).
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8ba_remainder`, `tsymex_rfc0005_s8ba_remainder_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 76 s).

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

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    check r.errors.len == 0
    r

# ---- (2) a seq of a distinct type --------------------------------------------

type Meters = distinct int
proc `+`(a, b: Meters): Meters {.borrow.}
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}

type Mod10 = distinct int
proc `==`(a, b: Mod10): bool = int(a) mod 10 == int(b) mod 10
  ## A USER `==` (not borrowed): equality modulo 10. A builtin model that
  ## compares a seq's cells by their base values would contradict it.

# ---- (4) by reference through a heap cell --------------------------------------

type Box = ref object
  x: int
type Outer = ref object
  inner: Box

var gBox: Box
proc setXG(v: var int, k: int) =
  v = k
  gBox.x = 5

proc rebindThenSet(v: var int, k: int) =
  gBox = Box(x: 1)
  v = k

proc sutHeapCap(k: int) =
  let p = Box(x: 0)
  let q = p
  proc setXC(v: var int) =
    v = k
    q.x = 5
  setXC(p.x)
  if p.x == 5 and k == 3: symexTarget("hc")
  if p.x == k and k != 5: symexTarget("hc_dead")

proc sutHeapDirect(k: int) =
  gBox = Box(x: 0)
  setXG(gBox.x, k)
  if gBox.x == 5 and k == 4: symexTarget("hd")
  if gBox.x == k and k != 5: symexTarget("hd_dead")

proc sutHeapRebind(k: int) =
  ## The address is taken at the call: the callee's later rebind of
  ## `gBox` does not move `v`.
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

proc sutHeapTupField(k: int) =
  ## The ref is a value-object field: still one ref, read at the call.
  var t = (b: Box(x: 0), n: 1)
  gBox = t.b
  setXG(t.b.x, k)
  if t.b.x == 5 and k == 7: symexTarget("ht")
  if t.b.x == k and k != 5: symexTarget("ht_dead")

proc sutHeapArrElem(k: int) =
  var a = [Box(x: 0)]
  gBox = a[0]
  setXG(a[0].x, k)
  if a[0].x == k and k != 5: symexTarget("he_dead")

suite "S8ba (4): a heap cell the callee also reaches is passed by reference":
  test "hc":
    discard clean(sutHeapCap, "hc", sxSat)
    discard clean(sutHeapCap, "hc_dead", sxUnsat)
  test "a global root":
    discard clean(sutHeapDirect, "hd", sxSat)
    discard clean(sutHeapDirect, "hd_dead", sxUnsat)
  # RFC-0005 S8bd: these paths made more than the default eight
  # dereferences and declined as `heDepthExhausted` until `maxHeapDepth`
  # bounded a chain's depth rather than the count; they are pinned at the
  # default budget.
  test "a rebind in the callee does not move the address":
    discard clean(sutHeapRebind, "hr", sxSat)
    discard clean(sutHeapRebind, "hr_dead", sxUnsat)
  test "a cell behind two refs":
    discard clean(sutHeapNested, "hn", sxSat)
    discard clean(sutHeapNested, "hn_dead", sxUnsat)
  test "a ref held in a value field":
    discard clean(sutHeapTupField, "ht", sxSat)
    discard clean(sutHeapTupField, "ht_dead", sxUnsat)
  test "an array element is passed by reference (RFC-0005 S8bd)":
    ## S8ba pinned this as S8au's `feUnsupportedOp` decline; S8bd passes
    ## an element's ref (`tsymex_rfc0005_s8bd_remainder.nim` pins the
    ## shapes that still decline).
    discard clean(sutHeapArrElem, "he_dead", sxUnsat)

# ---- (5) split term order -------------------------------------------------------

proc opDataStyleSlice(data: seq[byte]) =
  ## S8ag's B1-1 probe (`tsymex_r6_b1_stringbacked`).
  var i = 0
  while i < data.len and data[i] != 0'u8:
    inc i
  let payload = data[4 .. ^1]
  if payload.len > 3 and payload[0] == 42'u8:
    symexTarget("opdata_slice_sat")

suite "S8ba (5): split terms are built once, in a fixed order":

  test "a split's axioms are built by the first query that reaches it, once":
    indexSplits = @[]
    let ctx = newContext()
    let ix = lowerIndexSplit(mkStringVar(ctx, "s8ba_s"), mkString(ctx, ":"),
                             mkInt(ctx, 0))
    check not indexSplits[^1].built   # lowering builds no axiom term
    let q = @[ix >= mkInt(ctx, 0)]
    let a = indexSplitRoots(ctx, q)
    check indexSplits[^1].built
    let b = indexSplitRoots(ctx, q)
    check a.len == 2 and b.len == 2
    for k in 0 ..< a.len: check a[k].raw == b[k].raw
    indexSplits = @[]

  test "B1-1 stays under its unit ceiling":
    symexQueryStats = @[]
    let r = symexFind(opDataStyleSlice, tLabel("opdata_slice_sat"))
    var units = 0
    for q in symexQueryStats: units += q.rlimitDelta
    checkpoint symexQueryStatsSummary()
    check r.status == sxSat
    ## A ceiling per linked Z3. S8ba measured 187199 units here on 5.1
    ## (380570 run alone) and 2293304 on 4.13.4, on S8au. The eager
    ## construction this replaces cost 5-11x more on the suites it moved;
    ## the test above ("built once") is the direct guard against it.
    ##
    ## RFC-0005 batch 3 re-pinned these at 7M and 16M: the cost was q10's
    ## step-1 search, and it moved with whatever the walk's context held
    ## (S8ay's facts-first check moved it from 187,401 to 3,383,332 on
    ## 5.1). RFC-0005 S8bm runs step 1 in a context of its own and puts
    ## q10's byte test (an element of a slice) in character form: 46,533
    ## units on 5.1 and 79,494 on 4.13.4, wherever the walk runs
    ## (`tsymex_rfc0005_s8bm_stability`). The ceilings are about 2x those,
    ## so an eager construction's 5-11x still trips them.
    let v = z3Version()
    if v.major >= 5: check units <= 100_000
    else: check units <= 160_000

suite "S8ba: walker version floor":

  test "symexWalkerVersion >= 200":
    check parseInt(symexWalkerVersion) >= 200
