## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 3: an
## `addr s[i]` actual of a seq with element cells.
##
## S8be gives `addr s[i]` an element cell (`walkElemCell`) when the pointer
## may outlive its use; a pointer passed to a call that keeps it local was a
## cell for the call, copied in and written back. When the seq already had
## an element cell (another `addr s[j]` of the routine: a global holding
## it), the call's cell was a second copy of that memory, and S8bu declined
## ("in the element's own heap").
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (3) such an actual is the element's cell itself (`sharesElemCell`), for
##       a direct call, a proc-value call and a closure call: a write
##       through either pointer is one write, which the walker keeps equal
##       to the element across the call.
##
## Found on the way (SOUNDNESS): two `addr s[0]` in one frame give two
## element cells, the newer shadowed (`walkElemCell` hands out the older
## through an `ite` on the index). A callee's store through that `ite` left
## the shadowed cell's heap read a new term with its old value, which the
## caller's sync read back after the older cell's and so clobbered the
## element: `let q = addr s[0]; onlyP(q, k)` then `s[0] != k` was a false
## sxSat. A shadowed cell is now read back under the negation of its
## shadowing (`withCellElem`).
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

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 1, 2, 3, 5, 7]

var gpi: ptr int

proc bumpAddr(p: ptr int, k: int) =
  p[] = k
  gpi[] = gpi[] + 1

proc sutElemDirect(k: int) =
  if k < 0 or k > 1000: return
  var s = @[0, 0]
  gpi = addr s[0]
  bumpAddr(addr s[0], k)
  if s[0] == k + 1 and k == 3: symexTarget("ed")
  if s[0] != k + 1: symexTarget("ed_dead")

proc sutElemOther(k: int) =
  ## The call's element is not the one the global holds.
  if k < 0 or k > 1000: return
  var s = @[0, 0]
  gpi = addr s[0]
  bumpAddr(addr s[1], k)
  if s[1] == k and s[0] == 1 and k == 3: symexTarget("eo")
  if s[1] != k or s[0] != 1: symexTarget("eo_dead")

proc sutElemProcValue(k: int) =
  if k < 0 or k > 1000: return
  var s = @[0, 0]
  gpi = addr s[0]
  let f = bumpAddr
  f(addr s[0], k)
  if s[0] == k + 1 and k == 3: symexTarget("ev")
  if s[0] != k + 1: symexTarget("ev_dead")

proc sutElemClosure(k: int) =
  if k < 0 or k > 1000: return
  var s = @[0, 0]
  gpi = addr s[0]
  let f = proc (p: ptr int, v: int) =
    p[] = v
    gpi[] = gpi[] + 1
  f(addr s[0], k)
  if s[0] == k + 1 and k == 3: symexTarget("ec")
  if s[0] != k + 1: symexTarget("ec_dead")

proc setP(p: ptr int, k: int) = p[] = k

proc sutElemLetPtr(k: int) =
  if k < 0 or k > 1000: return
  var s = @[0, 0]
  gpi = addr s[0]
  let q = addr s[0]
  setP(q, k)
  if s[0] == k and k == 3: symexTarget("el")
  if s[0] != k: symexTarget("el_dead")

suite "S8ca (3): addr of an element of a seq with element cells":

  test "nim":
    let h = nativeHits(sutElemDirect, ks) + nativeHits(sutElemOther, ks) +
            nativeHits(sutElemProcValue, ks) + nativeHits(sutElemClosure, ks) +
            nativeHits(sutElemLetPtr, ks)
    for l in ["ed", "eo", "ev", "ec", "el"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a direct call":
    clean(sutElemDirect, "ed", sxSat)
    clean(sutElemDirect, "ed_dead", sxUnsat)
    clean(sutElemOther, "eo", sxSat)
    clean(sutElemOther, "eo_dead", sxUnsat)
    clean(sutElemLetPtr, "el", sxSat)
    clean(sutElemLetPtr, "el_dead", sxUnsat)

  test "a proc-value call and a closure call":
    clean(sutElemProcValue, "ev", sxSat)
    clean(sutElemProcValue, "ev_dead", sxUnsat)
    clean(sutElemClosure, "ec", sxSat)
    clean(sutElemClosure, "ec_dead", sxUnsat)

suite "S8ca (3): walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
