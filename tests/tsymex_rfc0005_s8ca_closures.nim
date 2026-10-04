## RFC-0005 (soundness channels) slice S8ca -- S8bu's remainder, item 4:
## closures over address-taken variables and heap lvalues.
##
## (4a) A closure capturing a variable whose address is taken held two
## copies of it: S8ax's capture cell (an env cell the closure reads and
## writes) and the address cell (the heap a pointer reads and writes).
## `syncAddrCells` declined any statement of such a frame ("also captured
## by a closure").
## (4b) A `var` actual that is a heap lvalue (`grb.x`) passed to a closure
## or a proc value whose body also reaches that object (a global, a
## capture) declined (S8bh's `touchMeetsOuter`): the body's write through
## the formal and its direct access were two copies.
##
## Pinned here (the RFC's "As landed (S8ca)" note has the design):
##   (4a) the closure's frame binds a by-reference capture that is an
##        address-taken variable of the frame applying it to the variable's
##        cell, as a named callee's capture is (`inheritAddrCells`); the
##        applying frame keeps the local, the cell and the env cell one
##        value;
##   (4b) such a heap lvalue is passed by reference: the body is
##        specialised to the lvalue (`byRefSub`, as for a direct call).
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

# ---- (4a) a closure capturing an address-taken variable ------------------

var gpx: ptr int

proc sutCapWrite(k: int) =
  ## The closure writes; the pointer reads.
  var x = 0
  gpx = addr x
  let f = proc () = x = k
  f()
  if gpx[] == k and k == 3: symexTarget("cw")
  if gpx[] != k: symexTarget("cw_dead")

proc sutCapRead(k: int) =
  ## The pointer writes; the closure reads.
  var x = 0
  gpx = addr x
  let f = proc (): int = x
  gpx[] = k
  if f() == k and k == 3: symexTarget("cr")
  if f() != k: symexTarget("cr_dead")

proc wrPtr(k: int) = gpx[] = k

proc sutCapMixed(k: int) =
  ## Inside the closure, a call writes through the pointer and the body
  ## then reads the capture.
  if k < 0 or k > 1000: return
  var x = 0
  gpx = addr x
  let f = proc (): int =
    wrPtr(k)
    x + 1
  if f() == k + 1 and x == k and k == 3: symexTarget("cm")
  if x != k: symexTarget("cm_dead")

# ---- (4b) a heap lvalue a closure's body also reaches --------------------

type RB = ref object
  x, y: int

var grb: RB

proc sutHeapClosure(k: int) =
  if k < 0 or k > 1000: return
  grb = RB()
  let f = proc (v: var int) =
    v = k
    grb.y = grb.x + 1
  f(grb.x)
  if grb.y == k + 1 and k == 3: symexTarget("hc")
  if grb.y != k + 1: symexTarget("hc_dead")

proc setThenBump(v: var int, k: int) =
  v = k
  grb.y = grb.x + 1

proc sutHeapProcValue(k: int) =
  if k < 0 or k > 1000: return
  grb = RB()
  let g = setThenBump
  g(grb.x, k)
  if grb.y == k + 1 and k == 3: symexTarget("hp")
  if grb.y != k + 1: symexTarget("hp_dead")

suite "S8ca (4a): a closure capturing an address-taken variable":

  test "nim":
    let h = nativeHits(sutCapWrite, ks) + nativeHits(sutCapRead, ks) +
            nativeHits(sutCapMixed, ks)
    for l in ["cw", "cr", "cm"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a write through either copy is seen through the other":
    clean(sutCapWrite, "cw", sxSat)
    clean(sutCapWrite, "cw_dead", sxUnsat)
    clean(sutCapRead, "cr", sxSat)
    clean(sutCapRead, "cr_dead", sxUnsat)
    clean(sutCapMixed, "cm", sxSat)
    clean(sutCapMixed, "cm_dead", sxUnsat)

suite "S8ca (4b): a heap lvalue a closure's body also reaches":

  test "nim":
    let h = nativeHits(sutHeapClosure, ks) + nativeHits(sutHeapProcValue, ks)
    for l in ["hc", "hp"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "passed by reference":
    clean(sutHeapClosure, "hc", sxSat)
    clean(sutHeapClosure, "hc_dead", sxUnsat)
    clean(sutHeapProcValue, "hp", sxSat)
    clean(sutHeapProcValue, "hp_dead", sxUnsat)

suite "S8ca (4): walker version":
  test "symexWalkerVersion >= 233":
    check parseInt(symexWalkerVersion) >= 233
