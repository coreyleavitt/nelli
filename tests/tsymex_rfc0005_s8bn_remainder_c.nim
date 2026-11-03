## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 3 of 6 of this suite, with
## `tsymex_rfc0005_s8bn_remainder`, `tsymex_rfc0005_s8bn_remainder_b`,
## `tsymex_rfc0005_s8bn_remainder_d`, `tsymex_rfc0005_s8bn_remainder_e`,
## `tsymex_rfc0005_s8bn_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 121 s).

import std/[unittest, strutils, options, macros, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser

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

template declines(fn: typed, lbl: string, ek: SymexErrorKind,
                  needle: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == ek and needle in e.msg: named = true
    check named

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

type VQ = ref object
  x: int

# ---- 5. an always-raising closure is a raise ---------------------------------
#
# RFC-0005 S8bn item 5. A closure whose every body path raises reported
# `ceClosureBodyDiverged` (a halt, the run `sxUnknown`) beside the raise it
# had already routed to the caller (`drainClosureRaises`): the raise is the
# body's whole behaviour, not a divergence.

proc sutCloRaise(k: int) =
  let f = proc () = raise newException(ValueError, "always")
  try:
    f()
    symexTarget("clr_dead")
  except ValueError:
    if k == 3: symexTarget("clr")

proc sutCloRaiseVal(k: int) =
  let f = proc (a: int): int =
    if a > 0: raise newException(ValueError, "pos")
    raise newException(IOError, "nonpos")
  try:
    discard f(k)
    symexTarget("clv_dead")
  except ValueError:
    if k == 2: symexTarget("clv")
  except IOError:
    if k == -2: symexTarget("clk")

proc sutCloEscape(k: int) =
  let f = proc () = raise newException(ValueError, "out")
  f()

suite "S8bn (5): an always-raising closure is a raise":

  test "nim":
    sutCloRaise(3)
    sutCloRaiseVal(2)
    expect ValueError: sutCloEscape(0)

  test "every body path raises":
    ## RED: `sxUnknown` (`ceClosureBodyDiverged`).
    discard clean(sutCloRaise, "clr", sxSat)
    discard clean(sutCloRaise, "clr_dead", sxUnsat)
    discard clean(sutCloRaiseVal, "clv", sxSat)
    discard clean(sutCloRaiseVal, "clk", sxSat)
    discard clean(sutCloRaiseVal, "clv_dead", sxUnsat)
    let r = symexFind(sutCloEscape, tRaisedExn("ValueError"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxRaised
    for e in r.errors: check e.severity == sevHint

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

var gB: LBox
var gLArr: array[3, int]
var gLs: seq[int]
var gLi: int

proc moveB(): int =
  gB = LBox(x: 100)
  0

proc bumpLArr(): int =
  gLArr[0] = 50
  0

proc bumpLs(): int =
  gLs[0] = 50
  0

proc incLi(): int =
  inc gLi
  0

proc ltouch(v: var int; k: int) = v = v + 5 + k
proc ltouchP(v: ptr int; k: int) = v[] = v[] + 5 + k

proc sutLateCopy(k: int) =
  if k < 0 or k > 1000: return
  let f = ltouch
  gB = LBox(x: k)
  let old = gB
  f(gB.x, moveB())
  if gB.x == 105 and old.x == k and k == 3: symexTarget("lcp")
  if gB.x != 105 or old.x != k: symexTarget("lcp_dead")

proc sutLateAddr(k: int) =
  if k < 0 or k > 1000: return
  let f = ltouchP
  gB = LBox(x: k)
  let old = gB
  f(addr gB.x, moveB())
  if gB.x == 105 and old.x == k and k == 9: symexTarget("lad")
  if gB.x != 105 or old.x != k: symexTarget("lad_dead")

proc sutLateArr(k: int) =
  ## The later call writes the element: the callee reads it after.
  if k < 0 or k > 1000: return
  let f = ltouch
  gLArr = [k, 20, 30]
  gLi = 0
  f(gLArr[gLi], bumpLArr())
  if gLArr[0] == 55 and k == 6: symexTarget("lar")
  if gLArr[0] != 55: symexTarget("lar_dead")

proc sutLateSeq(k: int) =
  if k < 0 or k > 1000: return
  let f = ltouch
  gLs = @[k, 20, 30]
  gLi = 0
  f(gLs[gLi], bumpLs())
  if gLs[0] == 55 and k == 7: symexTarget("lsq")
  if gLs[0] != 55: symexTarget("lsq_dead")

proc sutLateIdxMoved(k: int) =
  ## The later call moves the index Nim checked: UB, declined.
  if k < 0 or k > 1000: return
  let f = ltouch
  gLArr = [k, 20, 30]
  gLi = 0
  f(gLArr[gLi], incLi())
  if gLArr[1] == 25 and k == 1: symexTarget("lim")

suite "S8bn (6b): a by-address argument's address is taken at the call":

  test "nim":
    gB = LBox(x: 3)
    let old = gB
    let f = ltouch
    f(gB.x, moveB())
    check gB.x == 105 and old.x == 3
    gB = LBox(x: 3)
    let old2 = gB
    let g = ltouchP
    g(addr gB.x, moveB())
    check gB.x == 105 and old2.x == 3
    gLArr = [6, 20, 30]
    gLi = 0
    f(gLArr[gLi], bumpLArr())
    check gLArr[0] == 55
    gLs = @[7, 20, 30]
    f(gLs[gLi], bumpLs())
    check gLs[0] == 55

  test "a copy-in and an addr cell at the call":
    ## RED: the dead labels `sxSat` (false), the live ones `sxUnsat`.
    discard clean(sutLateCopy, "lcp", sxSat)
    discard clean(sutLateCopy, "lcp_dead", sxUnsat)
    discard clean(sutLateAddr, "lad", sxSat)
    discard clean(sutLateAddr, "lad_dead", sxUnsat)
    discard clean(sutLateArr, "lar", sxSat)
    discard clean(sutLateArr, "lar_dead", sxUnsat)
    discard clean(sutLateSeq, "lsq", sxSat)
    discard clean(sutLateSeq, "lsq_dead", sxUnsat)

  test "a later call that moves a checked index declines":
    ## RFC-0005 batch 6: S8bk's `placeLateAddr` (on the base) replaces the
    ## port S8bn made of it; its decline kind is `feEvalOrderUnmodelled`.
    declines(sutLateIdxMoved, "lim", feEvalOrderUnmodelled, "never checked")

type Ops6 = object
  f: proc (a, b: var int) {.nimcall.}
  k: int

type ROps6 = ref object
  f: proc (a, b: var int) {.nimcall.}
