## RFC-0005 (soundness channels) slice S8bd -- S8ba's remainder.
##
## Pinned here (the RFC's "As landed (S8bd)" note has the design and the
## measurements):
##   (1) a string index `i` that is a bit-vector, compared with `s.len`
##       both as itself and as `i + 1`, decides: the two Int views of `i`
##       and `i + 1` are linked by an exact theorem of two's complement
##       (`bvOffsetLinks`). It ran ~41M units to `sxUnknown`;
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8bd_remainder`, `tsymex_rfc0005_s8bd_remainder_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 69 s).

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

# ---- (2) a seq[distinct] parameter -------------------------------------------

type Meters = distinct int
proc `==`(a, b: Meters): bool {.borrow.}
proc `<`(a, b: Meters): bool {.borrow.}
# ---- (3) the heap-depth budget bounds a chain, not a count -------------------

type Box = ref object
  x: int
var gBox: Box

proc setXG(v: var int, k: int) =
  v = k
  gBox.x = 5

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
  if x == 7 and k == 3: symexTarget("ge")

suite "S8bd (4): more lvalues and callees are passed by reference":
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
    ## S8bd made it decline (`heUnsafeCast`). RFC-0005 batch 3: S8ax's
    ## address cells model it -- `addr x` is a `ptr` cell holding `x` for
    ## the frame's lifetime, so the kept pointer writes `x`, as Nim does.
    let rd = symexFind(sutGenericEscape, tLabel("ge_dead"))
    checkpoint "ge_dead " & $rd.status & " " & show(rd.errors)
    check rd.status == sxUnsat
    for e in rd.errors: check e.severity != sevError
    let rl = symexFind(sutGenericEscape, tLabel("ge"))
    checkpoint "ge " & $rl.status & " " & show(rl.errors)
    check rl.status == sxSat
    for e in rl.errors: check e.severity != sevError
    var x = 0
    keepPtrG(addr x, 1)
    gP[] = 7
    check x == 7

suite "S8bd: walker version":
  test "symexWalkerVersion >= 204":
    check parseInt(symexWalkerVersion) >= 204
