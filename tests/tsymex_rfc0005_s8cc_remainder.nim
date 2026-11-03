## RFC-0005 (soundness channels) slice S8cc -- S8br's remainder, items 2 and 3.
##
## 2. S8as's write summary counted every module-level `var` a callee names as
##    written, so `touch(gH.s[gi], f())` declined when `f` only reads `gi` or
##    `gH`. A callee's global now counts only where the callee may write it.
## 3. A call in a by-address actual's index that has no `result` symbol to
##    mark (through a proc value, or a generic's) declined. It is now bound
##    once into a temporary, as S8br's named calls are.
##
## Item 1 is `tsymex_rfc0005_s8cc_cellquery`. The RFC's "As landed (S8cc)" note
## has the design.
##
## RFC-0005 S8cm: part 1 of 3 of this suite, with
## `tsymex_rfc0005_s8cc_remainder_b`, `tsymex_rfc0005_s8cc_remainder_c`. Split
## so that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 82 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

template verdict(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  ## `want`, with no decline (`hePtrFamily`, a hint, may accompany a `ptr`).
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    for e in r.errors: check e.kind == hePtrFamily
    r

template replays(fn: typed, lbl: string) =
  block:
    let r = verdict(fn, lbl, sxSat)
    if r.status == sxSat:
      check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

template declines(fn: typed, lbl: string) =
  ## The later argument may write what the lvalue reads: never a verdict.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feEvalOrderUnmodelled)
    check not r.errors.hasKind(weInternalWalkerFault)

type Holder = ref object
  s: seq[int]

var gH: Holder
var gi: int
var gSeen: int
var gs: seq[int]
var gBig: array[8, int]

proc touch(v: var int; k: int) = v = v + 5 + k

proc bump(x: var int) = inc x

proc retGi(): var int = gi

# ---- 2. later arguments that only read what the lvalue names ----------------

proc readI(): int =
  ## Reads the index variable.
  if gi > 100: 1 else: 0

proc readS(): int =
  ## Reads through the ref, and its seq's length: `Holder`'s heap is left
  ## alone, and `gH` is not rebound.
  if gH.s.len > 100 or gH.s[0] > 100: 1 else: 0

proc readDeep(): int =
  ## The reads are one call down.
  readI() + readS()

proc readAsg(): int =
  ## An index that is read on the left of an assignment to another global.
  gSeen = gs[gi]
  0

proc sutReadI(k: int) =
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  touch(gH.s[gi], readI())
  if gH.s[2] == k + 5 and k == 7: symexTarget("ri")
  if gH.s[2] != k + 5: symexTarget("ri_dead")

proc sutReadS(k: int) =
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  touch(gH.s[gi], readS())
  if gH.s[2] == k + 5 and k == 8: symexTarget("rs")
  if gH.s[2] != k + 5: symexTarget("rs_dead")

proc sutReadDeep(k: int) =
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gi = 2
  touch(gH.s[gi], readDeep())
  if gH.s[2] == k + 5 and k == 9: symexTarget("rd")
  if gH.s[2] != k + 5: symexTarget("rd_dead")

proc sutReadAsg(k: int) =
  ## `gi` read in the callee, `gSeen` written and not on the lvalue.
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gs = @[4, 5, 6]
  gi = 2
  gSeen = 0
  touch(gH.s[gi], readAsg())
  if gH.s[2] == k + 5 and gSeen == 6 and k == 10: symexTarget("ra")
  if gH.s[2] != k + 5 or gSeen != 6: symexTarget("ra_dead")

# ---- 2. later arguments that write, however they spell it: still decline ----

proc wrAsg(): int =
  gi = 1
  0

proc wrInc(): int =
  inc gi
  0

proc wrVar(): int =
  bump(gi)
  0

proc wrAddr(): int =
  let p = addr gi
  p[] = 1
  0

proc wrRet(): int =
  retGi() = 1
  0

proc wrSwap(): int =
  var o = 1
  swap(gi, o)
  0

proc wrDeep(): int =
  wrAsg()

proc wrAlias(): int =
  ## Reads the ref, and writes its heap through a local copy of it.
  let h = gH
  h.s = @[1, 2, 3]
  0

proc wrArg(h: Holder): int =
  h.s = @[1, 2, 3]
  0

proc wrPass(): int =
  ## Reads the ref by value into a callee that writes its heap.
  wrArg(gH)

template sutWrites(name, callee, live, dead: untyped) =
  proc name(k: int) =
    ## Each writes the index (or the seq) before the call, so Nim's element
    ## differs from the one the argument's place would name.
    if k < 0 or k > 1000: return
    gH = Holder(s: @[10, 20, k])
    gi = 2
    touch(gH.s[gi], callee())
    if gH.s[2] == k + 5 and k == 3: symexTarget(live)
    if gH.s[2] != k + 5: symexTarget(dead)

sutWrites(sutWrAsg, wrAsg, "wa", "wa_dead")
sutWrites(sutWrInc, wrInc, "wi", "wi_dead")
sutWrites(sutWrVar, wrVar, "wv", "wv_dead")
sutWrites(sutWrAddr, wrAddr, "wp", "wp_dead")
sutWrites(sutWrRet, wrRet, "wr", "wr_dead")
sutWrites(sutWrSwap, wrSwap, "ws", "ws_dead")
sutWrites(sutWrDeep, wrDeep, "wd", "wd_dead")
sutWrites(sutWrAlias, wrAlias, "wl", "wl_dead")
sutWrites(sutWrPass, wrPass, "wy", "wy_dead")

proc wrByVal(x: array[8, int]): int =
  ## Nim passes this array by address, so writing through the by-value
  ## formal's `unsafeAddr` lands in the caller's storage.
  let p = unsafeAddr x
  p[][1] = 1
  0

proc wrThrough(): int =
  wrByVal(gBig)

proc sutWrByVal(k: int) =
  if k < 0 or k > 1000: return
  gH = Holder(s: @[10, 20, k])
  gBig[1] = 2
  touch(gH.s[gBig[1]], wrThrough())
  if gH.s[2] == k + 5 and k == 3: symexTarget("wb")
  if gH.s[2] != k + 5: symexTarget("wb_dead")

proc opAsg() {.symexOpaque.} = discard wrAsg()
proc opInc() {.symexOpaque.} = discard wrInc()
proc opVar() {.symexOpaque.} = discard wrVar()
proc opAddr() {.symexOpaque.} = discard wrAddr()
proc opRet() {.symexOpaque.} = discard wrRet()
proc opSwap() {.symexOpaque.} = discard wrSwap()
template sutOpaqueWrite(name, callee, lbl: untyped) =
  proc name(k: int) =
    ## Natively reached: the callee writes `gi` to 1 (or swaps it with 1).
    if k < 0 or k > 1000: return
    gi = 0
    callee()
    if gi == 1: symexTarget(lbl)

sutOpaqueWrite(sutOpAsg, opAsg, "oa")
sutOpaqueWrite(sutOpInc, opInc, "oi")
sutOpaqueWrite(sutOpVar, opVar, "ov")
sutOpaqueWrite(sutOpAddr, opAddr, "op")
sutOpaqueWrite(sutOpRet, opRet, "ot")
sutOpaqueWrite(sutOpSwap, opSwap, "os")

suite "S8cc: a later argument that only reads":

  test "nim":
    gH = Holder(s: @[10, 20, 30])
    gi = 2
    touch(gH.s[gi], readI())
    check gH.s[2] == 35
    gH = Holder(s: @[10, 20, 30])
    touch(gH.s[gi], readDeep())
    check gH.s[2] == 35
    gs = @[4, 5, 6]
    gSeen = 0
    gH = Holder(s: @[10, 20, 30])
    touch(gH.s[gi], readAsg())
    check gH.s[2] == 35 and gSeen == 6
    # Nim reads the lvalue at the call: a write moves the element.
    for f in [wrAsg, wrInc, wrVar, wrAddr, wrRet, wrSwap, wrDeep]:
      gH = Holder(s: @[10, 20, 30, 40])
      gi = 2
      touch(gH.s[gi], f())
      check gH.s[2] == 30
    gH = Holder(s: @[10, 20, 30])
    gi = 2
    touch(gH.s[gi], wrAlias())
    check gH.s[2] == 8
    gH = Holder(s: @[10, 20, 30])
    touch(gH.s[gi], wrPass())
    check gH.s[2] == 8
    gBig[1] = 2
    discard wrThrough()
    check gBig[1] == 1

  test "a callee that only reads the lvalue's variables decides":
    ## RED: each declined (`feEvalOrderUnmodelled`, S8bk's "may change what
    ## the check read"): S8as's summary counts a read as a write.
    replays(sutReadI, "ri")
    discard verdict(sutReadI, "ri_dead", sxUnsat)
    replays(sutReadS, "rs")
    discard verdict(sutReadS, "rs_dead", sxUnsat)
    replays(sutReadDeep, "rd")
    discard verdict(sutReadDeep, "rd_dead", sxUnsat)
    replays(sutReadAsg, "ra")
    discard verdict(sutReadAsg, "ra_dead", sxUnsat)

  test "a callee that writes them, however it spells it, still declines":
    declines(sutWrAsg, "wa_dead")
    declines(sutWrInc, "wi_dead")
    declines(sutWrVar, "wv_dead")
    block:
      # `addr` of a global in a callee halts the path (`heUnsafeCast`).
      let r = symexFind(sutWrAddr, tLabel("wp_dead"))
      checkpoint "wp_dead " & $r.status & " " & show(r.errors)
      check r.status == sxUnknown
      check not r.errors.hasKind(weInternalWalkerFault)
    declines(sutWrRet, "wr_dead")
    declines(sutWrSwap, "ws_dead")
    declines(sutWrDeep, "wd_dead")
    declines(sutWrAlias, "wl_dead")
    declines(sutWrPass, "wy_dead")
    declines(sutWrByVal, "wb_dead")
