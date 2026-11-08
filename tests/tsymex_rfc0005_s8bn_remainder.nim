## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 1 of 6 of this suite, with
## `tsymex_rfc0005_s8bn_remainder_b`, `tsymex_rfc0005_s8bn_remainder_c`,
## `tsymex_rfc0005_s8bn_remainder_d`, `tsymex_rfc0005_s8bn_remainder_e`,
## `tsymex_rfc0005_s8bn_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 121 s).

import std/[unittest, strutils, options, macros, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser
import s8ct_platform   ## RFC-0005 S8ct
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8bn_remainder")

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
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

template confirmed(fn: typed, lbl: string): untyped =
  ## A sound `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

# ---- 1-2. ptr alias witnesses ------------------------------------------------
#
# RFC-0005 S8bn items 1 and 2. S8bh aimed a `ptr` of unknown origin at a
# ref object's field, a global or a `var` parameter, and the `sxSat` was
# sound; but its witness replayed only when the field's object was built
# before the pointer (parameter order), and never for a global or a `var`
# parameter (the snapshot held no cell for either).

type PQ = ref object
  x: int
  s: string

var gPI: int
var gPS: string

proc sutPOrder(pi: ptr int; q: PQ) =
  ## The pointer's parameter comes before its target object's.
  if q == nil or pi == nil: return
  q.x = 1
  pi[] = 2
  if q.x == 2: symexTarget("po")

proc sutPOrderStr(ps: ptr string; k: int; q: PQ) =
  if q == nil or ps == nil: return
  q.s = "a"
  ps[] = "b"
  if q.s == "b" and k == 3: symexTarget("pos")

proc sutPGlobal(pi: ptr int) =
  if pi == nil: return
  gPI = 1
  pi[] = 2
  if gPI == 2: symexTarget("pg")

proc sutPGlobalStr(ps: ptr string) =
  if ps == nil: return
  gPS = "a"
  ps[] = "b"
  if gPS == "b": symexTarget("pgs")

proc sutPVar(v: var int; pi: ptr int) =
  if pi == nil: return
  v = 1
  pi[] = 2
  if v == 2: symexTarget("pv")

proc sutPVarFirst(pi: ptr int; v: var int) =
  ## The pointer before the `var` parameter it addresses.
  if pi == nil: return
  v = 1
  pi[] = 2
  if v == 2: symexTarget("pvf")

proc sutPVarStr(v: var string; ps: ptr string) =
  if ps == nil: return
  v = "a"
  ps[] = "b"
  if v == "b": symexTarget("pvs")

suite "S8bn (1-2): ptr alias witnesses":

  test "nim":
    let q = PQ(x: 0)
    sutPOrder(addr q.x, q)
    check q.x == 2
    sutPGlobal(addr gPI)
    check gPI == 2
    var v = 0
    sutPVar(v, addr v)
    check v == 2
    sutPVarFirst(addr v, v)
    check v == 2

  test "the pointer's parameter before its target object's":
    ## RED: `roRefuted` -- the witness built `pi` before `q`, so `pi` kept
    ## its own cell.
    confirmed(sutPOrder, "po")
    confirmed(sutPOrderStr, "pos")

  test "a pointer aimed at a global":
    ## RED: `roRefuted` -- the snapshot held no cell for the global.
    confirmed(sutPGlobal, "pg")
    confirmed(sutPGlobalStr, "pgs")

  test "a pointer aimed at a var parameter":
    ## RED: `roRefuted` -- the snapshot held no cell for the parameter.
    confirmed(sutPVar, "pv")
    confirmed(sutPVarFirst, "pvf")
    confirmed(sutPVarStr, "pvs")

# ---- 3. a var formal whose actual no pointer can address --------------------
#
# RFC-0005 S8bn item 3. While a callee (or a closure) runs, S8bh declined
# every deref of a `ptr T` of unknown origin when any frame had a `var`
# formal that may hold a T: the walk copies the formal in and out, so a
# store through a pointer into the actual's location would miss the
# formal. A local whose address is never taken is no pointer's target: no
# store through a pointer of unknown origin can reach it.

proc bumpVia(v: var int; pi: ptr int) =
  v = 1
  pi[] = 2

proc fwdVia(v: var int; pi: ptr int) = bumpVia(v, pi)

proc writeVia(pi: ptr int) = pi[] = 9

proc sutVFLocal(pi: ptr int) =
  if pi == nil: return
  var x = 0
  bumpVia(x, pi)
  if x == 1: symexTarget("vfl")
  if x != 1: symexTarget("vfl_dead")

proc sutVFFwd(pi: ptr int) =
  ## The callee passes its own `var` formal on: still the caller's local.
  if pi == nil: return
  var x = 0
  fwdVia(x, pi)
  if x == 1: symexTarget("vff")
  if x != 1: symexTarget("vff_dead")

proc sutVFClosure(pi: ptr int) =
  if pi == nil: return
  let f = proc (a: var int) =
    a = 1
    pi[] = 2
  var x = 0
  f(x)
  if x == 1: symexTarget("vfc")
  if x != 1: symexTarget("vfc_dead")

proc sutVFAddrTaken(pi: ptr int) =
  ## Control: the local's address is taken, so a pointer may be it.
  if pi == nil: return
  var x = 0
  writeVia(addr x)
  bumpVia(x, pi)
  if x == 1: symexTarget("vfa")

proc sutVFRootVar(v: var int; pi: ptr int) =
  ## Control: the SUT's own `var` parameter, forwarded.
  if pi == nil: return
  fwdVia(v, pi)
  if v == 2: symexTarget("vfr")

type VQ = ref object
  x: int

proc sutVFHeap(q: VQ; pi: ptr int) =
  ## A heap field. RFC-0005 batch 6: S8bs passes a heap lvalue by reference
  ## (`byRefSub`), so the callee writes the cell itself, not a copy, and a
  ## pointer into it needs no decline.
  if q == nil or pi == nil: return
  bumpVia(q.x, pi)
  if q.x == 2: symexTarget("vfh")
  if q.x != 1 and q.x != 2: symexTarget("vfh_dead")

suite "S8bn (3): a var formal whose actual no pointer can address":

  test "nim":
    var y = 0
    sutVFLocal(addr y)
    check y == 2
    var v = 0
    sutVFRootVar(v, addr v)
    check v == 2
    let q = VQ()
    sutVFHeap(q, addr q.x)
    check q.x == 2

  test "a local whose address is never taken":
    ## RED: `sxUnknown` (`feUnsupportedOp`, naming S8bh).
    discard clean(sutVFLocal, "vfl", sxSat)
    discard clean(sutVFLocal, "vfl_dead", sxUnsat)
    discard clean(sutVFFwd, "vff", sxSat)
    discard clean(sutVFFwd, "vff_dead", sxUnsat)
    discard clean(sutVFClosure, "vfc", sxSat)
    discard clean(sutVFClosure, "vfc_dead", sxUnsat)

  test "a location a pointer may address still declines":
    pinDecline(sutVFAddrTaken, declKey, feUnsupportedOp, tLabel("vfa"), "RFC-0005 S8bh")
    pinDecline(sutVFRootVar, declKey, feUnsupportedOp, tLabel("vfr"), "RFC-0005 S8bh")

  test "a heap field is passed by reference (S8bs)":
    ## Was a decline (the copy-in/copy-out formal). Native: the "nim" test
    ## above reaches `q.x == 2` with `pi = addr q.x`; the witness replays.
    confirmed(sutVFHeap, "vfh")
    discard clean(sutVFHeap, "vfh_dead", sxUnsat)

# ---- 6b. S8bk's late address on a call through a proc value -----------------
#
# RFC-0005 S8bn item 6 (S8bk's integration note). Nim takes a `var` / `addr`
# actual's address AT THE CALL, after every later argument: `let f = touch;
# f(gB.x, moveB())` compiles to `T1_ = moveB(); f(&(*gB).x, T1_)`, so when
# `moveB` rebinds `gB` the callee reads and writes the new object. S8bh's
# call through a proc value copied the value in (or filled the `addr` cell)
# where the argument stood and wrote it back through the late address. Only
# the address's checks (an index's bound) run where the argument stands; a
# later call that changes what one read declines.

type LBox = ref object
  x: int

type Ops6 = object
  f: proc (a, b: var int) {.nimcall.}
  k: int

type ROps6 = ref object
  f: proc (a, b: var int) {.nimcall.}
