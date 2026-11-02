## RFC-0005 (soundness channels) slice S8bu -- S8bs's remainder, item 4:
## a `var openArray[T]`, a view written through to its storage.
##
## Pinned here (the RFC's "As landed (S8bu)" note has the design):
##   (4b) a `var openArray` view of a whole seq is the seq passed by
##        address; one of an array or a `toOpenArray` slice is a temporary
##        written back over the elements it views (`iekSeqSplice` for a
##        seq), through a direct call and an inlined iterator alike.
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

# ---- (4b) a `var` view -----------------------------------------------------

proc setFirst(a: var openArray[int], k: int) =
  a[0] = k

proc sutVarSeq(k: int) =
  var s = @[0, 0]
  setFirst(s, k)
  if s[0] == k and k == 3: symexTarget("ws")
  if s[0] != k or s[1] != 0: symexTarget("ws_dead")

proc sutVarArray(k: int) =
  var a = [0, 0, 0]
  setFirst(a, k)
  if a[0] == k and k == 3: symexTarget("wa")
  if a[0] != k or a[1] != 0: symexTarget("wa_dead")

proc sutVarSlice(k: int) =
  var s = @[0, 0, 0, 0]
  setFirst(s.toOpenArray(2, 3), k)
  if s[2] == k and k == 3: symexTarget("wt")
  if s[2] != k or s[0] != 0 or s[3] != 0 or s.len != 4: symexTarget("wt_dead")

proc sutVarArraySlice(k: int) =
  var a = [0, 0, 0]
  setFirst(a.toOpenArray(1, 2), k)
  if a[1] == k and k == 3: symexTarget("wy")
  if a[1] != k or a[0] != 0 or a[2] != 0: symexTarget("wy_dead")

proc sutVarSymSlice(k: int) =
  ## A slice from a symbolic position, written back there.
  if k < 0 or k > 3: return
  var s = @[0, 0, 0, 0]
  setFirst(s.toOpenArray(k, 3), 9)
  if s[k] == 9 and k == 1 and s[0] == 0: symexTarget("wk")
  if s[k] != 9 or (k > 0 and s[0] != 0): symexTarget("wk_dead")

iterator firstOf(a: var openArray[int], k: int): int =
  a[0] = k
  yield a[0]

proc sutIterVarView(k: int) =
  ## An inlined iterator's `var openArray` formal is the seq.
  var s = @[0, 0]
  var got = -1
  for x in firstOf(s, k): got = x
  if got == k and s[0] == k and k == 3: symexTarget("wi")
  if got != k or s[0] != k: symexTarget("wi_dead")

var gpi: ptr int

iterator headOf(a: openArray[int]): int =
  gpi[] = 9
  yield a[0]

proc sutIterView(k: int) =
  ## An inlined iterator's by-value `openArray` formal is the location: a
  ## write through a pointer to the element is seen through it.
  var s = @[k, 0]
  gpi = addr s[0]
  var got = 0
  for x in headOf(s): got = x
  if got == 9 and k == 3: symexTarget("wh")
  if got != 9: symexTarget("wh_dead")

proc sutProcValueView(k: int) =
  ## Through a proc value: a seq argument of a proc value is not modelled
  ## (S8bh's `seUnsupportedCompoundSortLeaf`, reported in the RFC).
  var a = [0, 0, 0]
  let f = setFirst
  f(a, k)
  if a[0] == k and k == 3: symexTarget("wf")
  if a[0] != k: symexTarget("wf_dead")

suite "S8bu (4b): a var openArray writes through to its storage":

  test "nim":
    let h = nativeHits(sutVarSeq, ks) + nativeHits(sutVarArray, ks) +
            nativeHits(sutVarSlice, ks) + nativeHits(sutVarArraySlice, ks) +
            nativeHits(sutVarSymSlice, ks) + nativeHits(sutIterVarView, ks) +
            nativeHits(sutIterView, ks) + nativeHits(sutProcValueView, ks)
    for l in ["ws", "wa", "wt", "wy", "wk", "wi", "wh", "wf"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a direct call":
    clean(sutVarSeq, "ws", sxSat)
    clean(sutVarSeq, "ws_dead", sxUnsat)
    clean(sutVarArray, "wa", sxSat)
    clean(sutVarArray, "wa_dead", sxUnsat)
    clean(sutVarSlice, "wt", sxSat)
    clean(sutVarSlice, "wt_dead", sxUnsat)
    clean(sutVarArraySlice, "wy", sxSat)
    clean(sutVarArraySlice, "wy_dead", sxUnsat)
    clean(sutVarSymSlice, "wk", sxSat)
    clean(sutVarSymSlice, "wk_dead", sxUnsat)

  test "an inlined iterator":
    clean(sutIterVarView, "wi", sxSat)
    clean(sutIterVarView, "wi_dead", sxUnsat)
    clean(sutIterView, "wh", sxSat)
    clean(sutIterView, "wh_dead", sxUnsat)

  test "through a proc value: declined":
    declines(sutProcValueView, "wf", "no single-leaf Z3 sort")
    declines(sutProcValueView, "wf_dead", "no single-leaf Z3 sort")

suite "S8bu: walker version":
  test "symexWalkerVersion >= 225":
    check parseInt(symexWalkerVersion) >= 225
