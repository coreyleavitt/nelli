## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 8: a
## mutation of the whole value behind a pointer (`gps[].add v`).
##
## A mutation verb on `p[]` fell to the generic call, which inlined the
## system `add` down to the NimSeqV2 payload cast and declined
## (`heUnsafeCast`).
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (8) `p[].add v`, `p[].del i`, `p[].insert(v, i)` on a seq, `p[].add`
##       on a string, `p[].incl` on a set, through a `ptr` or a `ref`: the
##       value is read through the pointer, the bare arm's mutation applied
##       to it, and the result stored back; a by-value copy sharing the
##       memory (a `view`) declines, the mutation may resize.
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

var gps: ptr seq[int]
var gpstr: ptr string

proc push(k: int) = gps[].add k

proc sutPtrAdd(k: int) =
  if k < -1000 or k > 1000: return
  var s = @[1]
  gps = addr s
  gps[].add k
  push(k + 1)
  if s.len == 3 and s[1] == k and s[2] == k + 1 and k == 3:
    symexTarget("da")
  if s.len != 3 or s[1] != k: symexTarget("da_dead")

proc sutRefAdd(k: int) =
  let r = new seq[int]
  r[].add k
  r[].add 2
  if r[].len == 2 and r[][0] == k and k == 3: symexTarget("dr")
  if r[].len != 2 or r[][0] != k: symexTarget("dr_dead")

proc sutPtrDel(k: int) =
  ## `del`'s index is a `Natural`: a negative one is a RangeDefect.
  if k < 0: return
  var s = @[1, 2, 3]
  gps = addr s
  var hit = false
  try:
    gps[].del k
  except IndexDefect:
    hit = true
  if not hit and s.len == 2 and s[0] == 3 and k == 0: symexTarget("dd")
  if hit and k == 5: symexTarget("dd_raise")
  if hit and k >= 0 and k < 3: symexTarget("dd_dead")

proc sutPtrInsert(k: int) =
  var s = @[1, 2]
  gps = addr s
  var hit = false
  try:
    gps[].insert(k, 1)
  except IndexDefect:
    hit = true
  if not hit and s.len == 3 and s[0] == 1 and s[1] == k and s[2] == 2 and
     k == 3:
    symexTarget("di")
  if hit or s.len != 3 or s[0] != 1 or s[1] != k or s[2] != 2:
    symexTarget("di_dead")

proc sutPtrStrAdd(k: int) =
  var st = "ab"
  gpstr = addr st
  gpstr[].add 'c'
  if st == "abc" and k == 3: symexTarget("ds")
  if st != "abc": symexTarget("ds_dead")

suite "S8ca (8): a mutation through a pointer to the whole value":

  test "nim":
    let h = nativeHits(sutPtrAdd, ks) + nativeHits(sutRefAdd, ks) +
            nativeHits(sutPtrDel, ks) + nativeHits(sutPtrInsert, ks) +
            nativeHits(sutPtrStrAdd, ks)
    for l in ["da", "dr", "dd", "dd_raise", "di", "ds"]:
      checkpoint l
      check l in h
    for l in ["da", "dr", "dd", "di", "ds"]:
      check (l & "_dead") notin h

  test "add, through a ptr and a ref":
    clean(sutPtrAdd, "da", sxSat)
    clean(sutPtrAdd, "da_dead", sxUnsat)
    clean(sutRefAdd, "dr", sxSat)
    clean(sutRefAdd, "dr_dead", sxUnsat)

  test "del and insert":
    clean(sutPtrDel, "dd", sxSat)
    clean(sutPtrDel, "dd_raise", sxSat)
    clean(sutPtrDel, "dd_dead", sxUnsat)
    clean(sutPtrInsert, "di", sxSat)
    clean(sutPtrInsert, "di_dead", sxUnsat)

  test "a string":
    clean(sutPtrStrAdd, "ds", sxSat)
    clean(sutPtrStrAdd, "ds_dead", sxUnsat)

suite "S8ca: walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
