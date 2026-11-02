## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 4:
## `mitems` / `mpairs`, which yield each element by address.
##
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (4c) `for x in mitems(c)` / `for i, x in mpairs(c)` over a seq or an
##        array: `x` is the element itself (Nim's inline expansion), so a
##        write through it, through a pointer to it, and a read of `c` in the
##        body are one location; a seq resized in the body (Nim's `assert`)
##        declines on its paths. Before, the stdlib body was inlined and
##        declined at `unCheckedInc`'s pragma (a seq) or `low(IX)` (an
##        array).
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
    # A hint (a decline no path reaches, `hePtrFamily`) is not a decline.
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

const ks = [-3, 0, 1, 2, 3, 4, 5, 7]

var gpi: ptr int

# ---- (4c) mitems / mpairs --------------------------------------------------

proc sutMitemsSeq(k: int) =
  var s = @[1, 2]
  for x in mitems(s): x = k
  if s[0] == k and s[1] == k and k == 3: symexTarget("ms")
  if s[0] != k or s[1] != k: symexTarget("ms_dead")

proc sutMitemsArray(k: int) =
  var a = [1, 2]
  for x in mitems(a): x = k
  if a[0] == k and a[1] == k and k == 3: symexTarget("ma")
  if a[0] != k or a[1] != k: symexTarget("ma_dead")

proc sutMpairsSeq(k: int) =
  if k < -1000 or k > 1000: return
  var s = @[1, 2]
  for i, x in mpairs(s): x = k + i
  if s[1] == k + 1 and k == 3: symexTarget("mp")
  if s[1] != k + 1: symexTarget("mp_dead")

proc sutMpairsArray(k: int) =
  if k < -1000 or k > 1000: return
  var a: array[2 .. 3, int]
  for i, x in mpairs(a): x = k + i
  if a[3] == k + 3 and k == 3: symexTarget("mq")
  if a[2] != k + 2 or a[3] != k + 3: symexTarget("mq_dead")

type P2 = object
  v, w: int

proc sutMitemsObj(k: int) =
  if k < -1000 or k > 1000: return
  var a = [P2(v: 0, w: 1), P2(v: 0, w: 2)]
  for x in mitems(a): x.v = k + x.w
  if a[1].v == k + 2 and k == 3: symexTarget("mo")
  if a[1].v != k + 2: symexTarget("mo_dead")

type Arr3 = object
  v: array[3, int]

proc sutMitemsBreak(k: int) =
  ## A field of an object; a `break` leaves the loop.
  var b: Arr3
  for x in mitems(b.v):
    x = k
    if k > 2: break
  if b.v[0] == k and b.v[1] == 0 and k == 3: symexTarget("mb")
  if b.v[0] != k or (k > 2 and b.v[1] != 0): symexTarget("mb_dead")

proc sutMitemsReadsSeq(k: int) =
  ## The body reads the seq: the element written through `x` is seen.
  var s = @[0, 0]
  var seen = -1
  for x in mitems(s):
    x = k
    seen = s[0]
  if seen == k and k == 3: symexTarget("mr")
  if seen != k: symexTarget("mr_dead")

proc sutMitemsPointer(k: int) =
  ## A write through a pointer to an element is the element `x` names.
  var s = @[0, 0]
  gpi = addr s[1]
  var got = -1
  for x in mitems(s):
    gpi[] = 7
    got = x
  if got == 7 and s[1] == 7 and k == 3: symexTarget("mt")
  if got != 7: symexTarget("mt_dead")

proc fillAll(a: var openArray[int], k: int) =
  for x in mitems(a): x = k

proc sutMitemsView(k: int) =
  ## `mitems` over a `var openArray` formal.
  var s = @[1, 2]
  fillAll(s, k)
  if s[1] == k and k == 3: symexTarget("mv")
  if s[1] != k: symexTarget("mv_dead")

proc sutMitemsGrow(k: int) =
  ## The body resizes the seq: Nim's `assert` (and the element's address)
  ## is declined on the paths that reach it.
  var s = @[1]
  for x in mitems(s):
    if k == 3: s.add 5
  if s.len == 2: symexTarget("mg")

suite "S8bu (4c): mitems and mpairs yield each element by address":

  test "nim":
    let h = nativeHits(sutMitemsSeq, ks) + nativeHits(sutMitemsArray, ks) +
            nativeHits(sutMpairsSeq, ks) + nativeHits(sutMpairsArray, ks) +
            nativeHits(sutMitemsObj, ks) + nativeHits(sutMitemsBreak, ks) +
            nativeHits(sutMitemsReadsSeq, ks) +
            nativeHits(sutMitemsPointer, ks) + nativeHits(sutMitemsView, ks)
    for l in ["ms", "ma", "mp", "mq", "mo", "mb", "mr", "mt", "mv"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "over a seq and an array":
    clean(sutMitemsSeq, "ms", sxSat)
    clean(sutMitemsSeq, "ms_dead", sxUnsat)
    clean(sutMitemsArray, "ma", sxSat)
    clean(sutMitemsArray, "ma_dead", sxUnsat)
    clean(sutMpairsSeq, "mp", sxSat)
    clean(sutMpairsSeq, "mp_dead", sxUnsat)
    clean(sutMpairsArray, "mq", sxSat)
    clean(sutMpairsArray, "mq_dead", sxUnsat)
    clean(sutMitemsObj, "mo", sxSat)
    clean(sutMitemsObj, "mo_dead", sxUnsat)
    clean(sutMitemsBreak, "mb", sxSat)
    clean(sutMitemsBreak, "mb_dead", sxUnsat)

  test "the element is one location":
    clean(sutMitemsReadsSeq, "mr", sxSat)
    clean(sutMitemsReadsSeq, "mr_dead", sxUnsat)
    clean(sutMitemsPointer, "mt", sxSat)
    clean(sutMitemsPointer, "mt_dead", sxUnsat)
    clean(sutMitemsView, "mv", sxSat)
    clean(sutMitemsView, "mv_dead", sxUnsat)

  test "a resize in the body declines":
    declines(sutMitemsGrow, "mg", "mitems over a seq whose length changed")

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
