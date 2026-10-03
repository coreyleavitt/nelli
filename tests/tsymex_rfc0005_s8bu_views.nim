## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 4:
## `openArray[T]` as a view of its storage.
##
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (4a) an `openArray[T]` formal is the seq it views: a seq itself (a
##        `var` one the seq passed by address), an array's elements, or a
##        `toOpenArray(x, first, last)` slice of either, with Nim's bounds
##        check (`IndexDefect` unless the view is empty by `last == first -
##        1`) and a negative length (`last < first - 1`, which Nim does not
##        check) declined on its paths;
##   (4b) (`tsymex_rfc0005_s8bu_varviews`) a `var openArray` view;
##   (4c) (`tsymex_rfc0005_s8bu_mitems`) `mitems` and `mpairs`;
##   (4d) a string viewed as `openArray[char]` declines (it was a false
##        `sxUnsat`: the formal was an opaque value).
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

# ---- (4a) a read-only view -------------------------------------------------

proc sumOA(a: openArray[int]): int =
  for x in a: result += x

proc sutSeqView(k: int) =
  if k < 0 or k > 1000: return
  let s = @[k, 2]
  if sumOA(s) == k + 2 and k == 3: symexTarget("vs")
  if sumOA(s) != k + 2: symexTarget("vs_dead")

proc sutArrayView(k: int) =
  if k < 0 or k > 1000: return
  let a = [k, 2]
  if sumOA(a) == k + 2 and k == 3: symexTarget("va")
  if sumOA(a) != k + 2: symexTarget("va_dead")

proc passOn(a: openArray[int]): int = sumOA(a)

proc sutPassedOn(k: int) =
  ## A view passed on to another `openArray` formal.
  if k < 0 or k > 1000: return
  let s = @[k, 1]
  if passOn(s) == k + 1 and k == 3: symexTarget("vp")
  if passOn(s) != k + 1: symexTarget("vp_dead")

proc sutSliceView(k: int) =
  ## A slice with symbolic bounds.
  if k < 0 or k > 2: return
  let s = @[1, 2, 30, 4]
  let r = sumOA(s.toOpenArray(k, k + 1))
  if r == 34 and k == 2: symexTarget("vt")
  if r != s[k] + s[k + 1]: symexTarget("vt_dead")

proc lenOA(a: openArray[int]): int = a.len

proc sutSliceBounds(k: int) =
  ## Nim checks the bounds unless the view is empty by `last == first - 1`.
  if k < 2: return
  let s = @[1, 2, 3, 4]
  var hit = false
  var n = -1
  try:
    n = lenOA(s.toOpenArray(3, k))
  except IndexDefect:
    hit = true
  if hit and k == 4: symexTarget("vb")
  if n == 0 and k == 2: symexTarget("vb2")
  if hit and k < 4: symexTarget("vb_dead")

proc sutSliceNegative(k: int) =
  ## `last < first - 1`: Nim makes a view of negative length.
  if k > 1: return
  let s = @[1, 2, 3, 4]
  if lenOA(s.toOpenArray(2, k)) == -1 and k == 0: symexTarget("vn")

proc cntOA(a: openArray[char]): int = a.len

proc sutStringView(k: int) =
  let st = "ab"
  if cntOA(st) == 2 and k == 3: symexTarget("vc")

suite "S8bu (4a): an openArray is a view of its storage":

  test "nim":
    let h = nativeHits(sutSeqView, ks) + nativeHits(sutArrayView, ks) +
            nativeHits(sutPassedOn, ks) + nativeHits(sutSliceView, ks) +
            nativeHits(sutSliceBounds, ks) + nativeHits(sutStringView, ks)
    for l in ["vs", "va", "vp", "vt", "vb", "vb2", "vc"]:
      checkpoint l
      check l in h
    for l in ["vs", "va", "vp", "vt", "vb"]:
      checkpoint l & "_dead"
      check (l & "_dead") notin h

  test "a seq, an array, a view passed on":
    clean(sutSeqView, "vs", sxSat)
    clean(sutSeqView, "vs_dead", sxUnsat)
    clean(sutArrayView, "va", sxSat)
    clean(sutArrayView, "va_dead", sxUnsat)
    clean(sutPassedOn, "vp", sxSat)
    clean(sutPassedOn, "vp_dead", sxUnsat)

  test "a toOpenArray slice":
    clean(sutSliceView, "vt", sxSat)
    clean(sutSliceView, "vt_dead", sxUnsat)
    clean(sutSliceBounds, "vb", sxSat)
    clean(sutSliceBounds, "vb2", sxSat)
    clean(sutSliceBounds, "vb_dead", sxUnsat)
    declines(sutSliceNegative, "vn", "toOpenArray of negative length")

  test "a string's view declines":
    declines(sutStringView, "vc", "openArray view of an unmodelled storage")

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
