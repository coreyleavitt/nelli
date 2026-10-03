## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 5:
## an array element on a path into an address-taken variable.
##
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (5) a `var` (or `addr`, or by-address) actual `b.v[i]`, `b.v[i].x`, an
##       element of an array in an address-taken variable, is bound to the
##       variable's cell at that path, by a constant index or a symbolic one
##       (an `ite` over the elements, as a read `a[i]` is); it declined as a
##       path the walk did not follow.
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
      if e.severity == sevError and why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 1, 2, 3, 5, 7]

# ---- (5) an array element on a path into an address-taken variable --------

type Arr3 = object
  v: array[3, int]

var gpa: ptr Arr3

proc setAfter(x: var int, k: int) =
  x = k
  gpa[].v[1] = 5

proc sutConstIndex(k: int) =
  var b: Arr3
  gpa = addr b
  setAfter(b.v[1], k)
  if b.v[1] == 5 and k == 3: symexTarget("ac")
  if b.v[1] != 5: symexTarget("ac_dead")

proc sutSymIndex(k: int) =
  ## `j` is the element the write through the pointer reaches when it is 1.
  let j = k mod 3
  if j < 0: return
  var b: Arr3
  gpa = addr b
  setAfter(b.v[j], k)
  if b.v[1] == 5 and j == 1 and k == 7: symexTarget("as")
  if b.v[1] != 5 or (j != 1 and b.v[j] != k): symexTarget("as_dead")

type Low2 = object
  v: array[2 .. 4, int]

var gpl: ptr Low2

proc setLow(x: var int, k: int) =
  gpl[].v[3] = 7
  x = k

proc sutLowIndex(k: int) =
  ## An array whose first index is 2: the step is the position.
  var b: Low2
  gpl = addr b
  setLow(b.v[3], k)
  if b.v[3] == k and b.v[2] == 0 and k == 3: symexTarget("al")
  if b.v[3] != k or b.v[2] != 0: symexTarget("al_dead")

type
  Pt = object
    x, y: int
  Pts = object
    p: array[2, Pt]

var gpp: ptr Pts

proc setX(x: var int, k: int) =
  x = k
  gpp[].p[0].x = x + 1

proc sutElemField(k: int) =
  ## A field of an array element.
  if k < 0 or k > 1000: return
  var b: Pts
  gpp = addr b
  setX(b.p[0].x, k)
  if b.p[0].x == k + 1 and b.p[1].x == 0 and k == 3: symexTarget("af")
  if b.p[0].x != k + 1: symexTarget("af_dead")

proc rdPtr(p: ptr int, k: int): int =
  gpa[].v[2] = k
  p[]

proc sutAddrElem(k: int) =
  ## `addr b.v[2]`: a sub-cell of `b`'s cell (S8bu item 3) at an element.
  var b: Arr3
  gpa = addr b
  let r = rdPtr(addr b.v[2], k)
  if r == k and k == 3: symexTarget("ae")
  if r != k: symexTarget("ae_dead")

suite "S8bu (5): an array element on a path into an address-taken variable":

  test "nim":
    let h = nativeHits(sutConstIndex, ks) + nativeHits(sutSymIndex, ks) +
            nativeHits(sutLowIndex, ks) + nativeHits(sutElemField, ks) +
            nativeHits(sutAddrElem, ks)
    for l in ["ac", "as", "al", "af", "ae"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a constant and a symbolic index":
    clean(sutConstIndex, "ac", sxSat)
    clean(sutConstIndex, "ac_dead", sxUnsat)
    clean(sutSymIndex, "as", sxSat)
    clean(sutSymIndex, "as_dead", sxUnsat)
    clean(sutLowIndex, "al", sxSat)
    clean(sutLowIndex, "al_dead", sxUnsat)

  test "a field of an element, and addr of an element":
    clean(sutElemField, "af", sxSat)
    clean(sutElemField, "af_dead", sxUnsat)
    clean(sutAddrElem, "ae", sxSat)
    clean(sutAddrElem, "ae_dead", sxUnsat)

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
