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
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8cc_remainder`, `tsymex_rfc0005_s8cc_remainder_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 82 s).

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import s8ct_platform   ## RFC-0005 S8ct

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

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
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

type Holder = ref object
  s: seq[int]

var gH: Holder
var gi: int
var gs: seq[int]
var gCalls: int
proc touch(v: var int; k: int) = v = v + 5 + k

proc bump(x: var int) = inc x

proc retGi(): var int = gi

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

proc idOf[T](x: T): T =
  inc gCalls
  x

proc oneOf[T](x: T): int =
  ## A generic whose `result` is not its type parameter.
  inc gCalls
  1

proc sutGenericNarrow(k: int) =
  ## The index is narrower than `int`.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  touch(gs[idOf(1'i8)], 0)
  if gs[1] == k + 5 and gCalls == 1 and k == 2: symexTarget("gn")
  if gs[1] != k + 5 or gCalls != 1: symexTarget("gn_dead")

proc sutGeneric(k: int) =
  ## `idOf`'s `result` reads as its type parameter.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  touch(gs[idOf(1)], 0)
  if gs[1] == k + 5 and gCalls == 1 and k == 7: symexTarget("gi")
  if gs[1] != k + 5 or gCalls != 1: symexTarget("gi_dead")

proc sutGenericOther(k: int) =
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  touch(gs[oneOf("x")], 0)
  if gs[1] == k + 5 and gCalls == 1 and k == 8: symexTarget("go")
  if gs[1] != k + 5 or gCalls != 1: symexTarget("go_dead")

suite "S8cc: an index call with no symbol to mark":
  test "a generic's":
    ## Already right at the base: the instantiation's `result` has the
    ## call's type, so S8br named these. Kept as pins: S8cc binds them by the
    ## same mark as a call through a proc value.
    replays(sutGeneric, "gi")
    discard verdict(sutGeneric, "gi_dead", sxUnsat)
    replays(sutGenericOther, "go")
    discard verdict(sutGenericOther, "go_dead", sxUnsat)
    replays(sutGenericNarrow, "gn")
    discard verdict(sutGenericNarrow, "gn_dead", sxUnsat)

  test "walker version floor":
    check symexWalkerVersion.parseInt >= 238
