## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 3:
## `addr` of a part of an address-taken variable.
##
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (3) `addr b.x` of an address-taken `b` is a sub-cell of `b`'s cell at
##       `.x`.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
import std/[unittest, strutils, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/engine/markers

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

template declines(fn: typed, lbl, why: string): untyped =
  ## A shape the walk does not model: `sxUnknown`, with the decline named.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == feUnsupportedOp and why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 3, 5, 7]

type Box = object
  x: int

var gpb: ptr Box
var gpi: ptr int

# ---- (3) `addr` of a part of an address-taken variable ---------------------

proc rdXAddr(p: ptr int, k: int): int =
  gpb[].x = k
  p[]

proc sutDirectAddrPart(k: int) =
  var b = Box(x: 0)
  gpb = addr b
  let r = rdXAddr(addr b.x, k)
  if r == k and b.x == k and k == 3: symexTarget("da")
  if r != k or b.x != k: symexTarget("da_dead")

proc wrXAddr(p: ptr int, k: int) =
  gpb[].x = 5
  p[] = k

proc sutDirectAddrPartWrite(k: int) =
  var b = Box(x: 0)
  gpb = addr b
  wrXAddr(addr b.x, k)
  if b.x == k and k == 3: symexTarget("dw")
  if b.x != k: symexTarget("dw_dead")

type Outer = object
  inner: Box
  n: int

var gpo: ptr Outer

proc rdOuter(p: ptr int, k: int): int =
  gpo[].inner.x = k
  p[]

proc sutDirectAddrNested(k: int) =
  var o = Outer(inner: Box(x: 0), n: 0)
  gpo = addr o
  let r = rdOuter(addr o.inner.x, k)
  if r == k and o.inner.x == k and k == 3: symexTarget("dn")
  if r != k or o.inner.x != k: symexTarget("dn_dead")

proc wrIAddr(p: ptr int, k: int) =
  gpi[] = 5
  p[] = k

proc sutDirectAddrWhole(k: int) =
  var x = 0
  gpi = addr x
  wrIAddr(addr x, k)
  if x == k and k == 3: symexTarget("dx")
  if x != k: symexTarget("dx_dead")

proc bumpAddr(p: ptr int, k: int) =
  p[] = k
  gpi[] = gpi[] + 1

proc sutDirectAddrElem(k: int) =
  if k < 0 or k > 1000: return
  var s = @[0, 0]
  gpi = addr s[0]
  bumpAddr(addr s[0], k)
  if s[0] == k + 1 and k == 3: symexTarget("de")
  if s[0] != k + 1: symexTarget("de_dead")

suite "S8bu (3): addr of a part of an address-taken variable":

  test "nim":
    let h = nativeHits(sutDirectAddrPart, ks) +
            nativeHits(sutDirectAddrPartWrite, ks) +
            nativeHits(sutDirectAddrNested, ks) +
            nativeHits(sutDirectAddrWhole, ks) + nativeHits(sutDirectAddrElem, ks)
    for l in ["da", "dw", "dn", "dx", "de"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a direct call":
    clean(sutDirectAddrPart, "da", sxSat)
    clean(sutDirectAddrPart, "da_dead", sxUnsat)
    clean(sutDirectAddrPartWrite, "dw", sxSat)
    clean(sutDirectAddrPartWrite, "dw_dead", sxUnsat)
    clean(sutDirectAddrNested, "dn", sxSat)
    clean(sutDirectAddrNested, "dn_dead", sxUnsat)
    clean(sutDirectAddrWhole, "dx", sxSat)
    clean(sutDirectAddrWhole, "dx_dead", sxUnsat)
    # An element of a seq with element cells: declined (reported in the
    # RFC): the call's cell shares the element's heap.
    declines(sutDirectAddrElem, "de", "in the element's own heap")
    declines(sutDirectAddrElem, "de_dead", "in the element's own heap")


suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
