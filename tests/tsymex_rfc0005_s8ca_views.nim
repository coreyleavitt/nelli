## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 2: a
## by-value seq sharing an address-taken variable's memory (S8bu's `view`)
## followed the cell by the shape of its terms.
##
## S8bu's `viewFollows` read a change of the cell as an in-place write when
## the new length was the old term and the new data a store chain over the
## old. That is structural: `swap(gps[], other)` with `other = newSeq(2)`
## gives the variable other memory whose terms are the old ones exactly
## (`newSeq(2)` twice), and a later `gps[][0] = k` is then a store over
## them, so the copy followed into memory it does not share. Natively the
## copy keeps the old buffer (`other` owns it, so the program is defined):
## `vw` is hit, and the walk had `vw` sxUnsat and `vw_dead` sxSat.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (2) identity is tracked by the write: each element write-back the
##       parser emits (`p[][i] = v`, `p.s[i] = v`: `dwInPlace`) and each
##       sync of an element written by name is logged as an in-place step
##       of the heap arrays it changed (`Path.inPlaceSteps`); a view
##       follows only while its arrays changed by a chain of such steps
##       (`viewInPlace`). Any other write -- a swap, an assignment of the
##       whole, a resize, whatever its terms -- declines the path.
##
## Found on the way (SOUNDNESS): `swap` was a no-op. Its bodiless
## `{.magic.}` routine was registered with an empty body, so `swap(a, b);
## if a[1] == 3` was a clean, wrong sxUnsat. It is modelled (`parseSwap`):
## both operands read, each written the other's value through the
## assignment's own lvalue arms.
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
    for e in r.errors: check e.severity == sevHint

template declines(fn: typed, lbl, why: string): untyped =
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

var gps: ptr seq[int]

proc rdSwap(t: seq[int], k: int): int =
  var other = newSeq[int](2)
  swap(gps[], other)       # the variable takes `other`'s memory
  gps[][0] = k             # written there, not in `t`'s
  t[0]                     # the old memory, alive in `other`

proc sutSwap(k: int) =
  var s = newSeq[int](2)
  gps = addr s
  let r = rdSwap(s, k)
  if r == 0 and k == 3: symexTarget("vw")
  if r == k and k == 3: symexTarget("vw_dead")

proc rdFresh(t: seq[int], k: int): int =
  gps[] = newSeq[int](2)   # the old memory is freed: `t` dangles
  gps[][0] = k
  t[0]

proc sutFresh(k: int) =
  ## Not run natively (a read of freed memory).
  var s = newSeq[int](2)
  gps = addr s
  if rdFresh(s, k) == k and k == 3: symexTarget("vf")

proc setFirst(v: var seq[int], k: int) = v[0] = k

proc rdVar(t: seq[int], k: int): int =
  setFirst(gps[], k)       # by address: written in place
  t[0]

proc sutVarWrite(k: int) =
  var s = newSeq[int](2)
  gps = addr s
  let r = rdVar(s, k)
  if r == k and k == 3: symexTarget("vv")
  if r != k: symexTarget("vv_dead")

proc rdTwice(t: seq[int], k: int): int =
  gps[][0] = k
  gps[][1] = k + 1         # two in-place steps
  t[0] + t[1]

proc sutTwice(k: int) =
  if k < 0 or k > 1000: return
  var s = newSeq[int](2)
  gps = addr s
  let r = rdTwice(s, k)
  if r == 2 * k + 1 and k == 3: symexTarget("vt")
  if r != 2 * k + 1: symexTarget("vt_dead")

proc sutSwapLocal(k: int) =
  var a = @[1, 2]
  var b = @[7, k]
  swap(a, b)
  if a[1] == 3 and b[0] == 1: symexTarget("ls")
  if a[0] != 7: symexTarget("ls_dead")

proc sutSwapInts(k: int) =
  var x = k
  var y = 5
  swap(x, y)
  if x == 5 and y == 3: symexTarget("li")
  if x != 5: symexTarget("li_dead")

proc sutSwapPtr(k: int) =
  var s = @[0, 0]
  gps = addr s
  var other = @[7, k]
  swap(gps[], other)
  if s[1] == 3 and other[0] == 0: symexTarget("lp")
  if s[0] != 7: symexTarget("lp_dead")

suite "S8ca (2): swap is modelled":

  test "nim":
    let h = nativeHits(sutSwapLocal, ks) + nativeHits(sutSwapInts, ks) +
            nativeHits(sutSwapPtr, ks)
    for l in ["ls", "li", "lp"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "swap of locals, of ints, and through a pointer":
    clean(sutSwapLocal, "ls", sxSat)
    clean(sutSwapLocal, "ls_dead", sxUnsat)
    clean(sutSwapInts, "li", sxSat)
    clean(sutSwapInts, "li_dead", sxUnsat)
    clean(sutSwapPtr, "lp", sxSat)
    clean(sutSwapPtr, "lp_dead", sxUnsat)

suite "S8ca (2): a view follows logged in-place writes, not term shapes":

  test "nim":
    let h = nativeHits(sutSwap, ks) + nativeHits(sutVarWrite, ks) +
            nativeHits(sutTwice, ks)
    for l in ["vw", "vv", "vt"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a swap that leaves equal terms is not an in-place write":
    declines(sutSwap, "vw", "assigned whole or resized")
    declines(sutSwap, "vw_dead", "assigned whole or resized")

  test "an assignment of the whole whose terms match declines":
    declines(sutFresh, "vf", "assigned whole or resized")

  test "in-place writes through the pointer and by a var formal are seen":
    clean(sutTwice, "vt", sxSat)
    clean(sutTwice, "vt_dead", sxUnsat)
    clean(sutVarWrite, "vv", sxSat)
    clean(sutVarWrite, "vv_dead", sxUnsat)

suite "S8ca (2): walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
