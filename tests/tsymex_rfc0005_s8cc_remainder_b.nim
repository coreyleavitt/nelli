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
## RFC-0005 S8cm: part 2 of 3 of this suite, with
## `tsymex_rfc0005_s8cc_remainder`, `tsymex_rfc0005_s8cc_remainder_c`. Split so
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
var gArr: array[3, int]
var gCalls: int
var gOrder: int
var gBig: array[8, int]

proc touch(v: var int; k: int) = v = v + 5 + k

proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k

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

proc wrByVal(x: array[8, int]): int =
  ## Nim passes this array by address, so writing through the by-value
  ## formal's `unsafeAddr` lands in the caller's storage.
  let p = unsafeAddr x
  p[][1] = 1
  0

# ---- 2. a statement-position opaque call that only reads keeps the global ----

proc showI() {.symexOpaque.} =
  ## An inert opaque call: it names `gi` and only reads it.
  if gi > 100: discard

proc sutOpaqueRead(k: int) =
  if k < 0 or k > 1000: return
  gi = k
  showI()
  if gi == 11: symexTarget("or")
  if gi != k: symexTarget("or_dead")

proc opAsg() {.symexOpaque.} = discard wrAsg()
proc opInc() {.symexOpaque.} = discard wrInc()
proc opVar() {.symexOpaque.} = discard wrVar()
proc opAddr() {.symexOpaque.} = discard wrAddr()
proc opRet() {.symexOpaque.} = discard wrRet()
proc opSwap() {.symexOpaque.} = discard wrSwap()
proc opByVal() {.symexOpaque.} = discard wrByVal(gBig)

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

proc sutOpByVal(k: int) =
  ## The write lands in `gBig` through a by-value formal's address.
  if k < 0 or k > 1000: return
  gBig[1] = 2
  opByVal()
  if gBig[1] == 1: symexTarget("ob")

# ---- 3. an index call the walk has no symbol for ----------------------------

proc nextI(): int =
  inc gCalls
  gOrder = gOrder * 10 + 1
  1

proc dblS(): int =
  gOrder = gOrder * 10 + 2
  gs[1] = gs[1] * 2
  0

proc dblArr(): int =
  gOrder = gOrder * 10 + 2
  gArr[1] = gArr[1] * 2
  0

proc idOf[T](x: T): T =
  inc gCalls
  x

proc oneOf[T](x: T): int =
  ## A generic whose `result` is not its type parameter.
  inc gCalls
  1

proc sutValSeq(k: int) =
  ## S8br's `fs`: through a proc value, into a seq the later call writes.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  gOrder = 0
  let fv = nextI
  touch(gs[fv()], dblS())
  if gs[1] == 2 * k + 5 and gCalls == 1 and gOrder == 12 and k == 3:
    symexTarget("fs")
  if gs[1] != 2 * k + 5 or gCalls != 1 or gOrder != 12: symexTarget("fs_dead")

proc sutValArr(k: int) =
  if k < 0 or k > 1000: return
  gArr = [10, k, 30]
  gCalls = 0
  gOrder = 0
  let fv = nextI
  touch(gArr[fv()], dblArr())
  if gArr[1] == 2 * k + 5 and gCalls == 1 and gOrder == 12 and k == 4:
    symexTarget("fa")
  if gArr[1] != 2 * k + 5 or gCalls != 1 or gOrder != 12: symexTarget("fa_dead")

proc rangedI(): range[0 .. 2] =
  inc gCalls
  1

proc sutValRange(k: int) =
  ## The call's type has no symbol.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  let fr = rangedI
  touch(gs[fr()], 0)
  if gs[1] == k + 5 and gCalls == 1 and k == 1: symexTarget("fr")
  if gs[1] != k + 5 or gCalls != 1: symexTarget("fr_dead")

proc sutValAddr(k: int) =
  ## An `addr` actual, the callee writing through the cell.
  if k < 0 or k > 1000: return
  gs = @[10, 20, 30]
  gCalls = 0
  gOrder = 0
  let fv = nextI
  touchP(addr gs[fv()], k)
  if gs[1] == k + 25 and gCalls == 1 and k == 5: symexTarget("fp")
  if gs[1] != k + 25 or gCalls != 1: symexTarget("fp_dead")

proc sutValClosure(k: int) =
  ## A closure: its capture picks the element.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  var picked = 1
  let c = proc (): int =
    inc gCalls
    picked
  gCalls = 0
  touch(gs[c()], 0)
  if gs[1] == k + 5 and gCalls == 1 and k == 6: symexTarget("fc")
  if gs[1] != k + 5 or gCalls != 1: symexTarget("fc_dead")

proc sutValThrough(k: int) =
  ## The whole call goes through a proc value too.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  gOrder = 0
  let fv = nextI
  let t = touch
  t(gs[fv()], 0)
  if gs[1] == k + 5 and gCalls == 1 and k == 9: symexTarget("ft")
  if gs[1] != k + 5 or gCalls != 1: symexTarget("ft_dead")

suite "S8cc: a later argument that only reads":
  test "an opaque call that only reads a global keeps its value":
    ## RED: `gi` was rebound to a fresh value (`feGlobalHavoc`).
    replays(sutOpaqueRead, "or")
    discard verdict(sutOpaqueRead, "or_dead", sxUnsat)

suite "S8cc: an opaque call that writes a global, however it spells it":

  test "nim":
    for f in [sutOpAsg, sutOpInc, sutOpVar, sutOpAddr, sutOpRet, sutOpSwap,
              sutOpByVal]:
      f(0)
    check gBig[1] == 1
    gi = 0
    opSwap()
    check gi == 1

  test "the target stays reachable":
    ## Any of these read as no write is a false `sxUnsat`.
    check symexFind(sutOpAsg, tLabel("oa")).status != sxUnsat
    check symexFind(sutOpInc, tLabel("oi")).status != sxUnsat
    check symexFind(sutOpVar, tLabel("ov")).status != sxUnsat
    check symexFind(sutOpAddr, tLabel("op")).status != sxUnsat
    check symexFind(sutOpRet, tLabel("ot")).status != sxUnsat
    check symexFind(sutOpSwap, tLabel("os")).status != sxUnsat
    check symexFind(sutOpByVal, tLabel("ob")).status != sxUnsat

suite "S8cc: an index call with no symbol to mark":

  test "nim":
    gs = @[10, 20, 30]
    gCalls = 0
    gOrder = 0
    let fv = nextI
    touch(gs[fv()], dblS())
    check gs == @[10, 45, 30] and gCalls == 1 and gOrder == 12
    gArr = [10, 20, 30]
    gCalls = 0
    gOrder = 0
    touch(gArr[fv()], dblArr())
    check gArr == [10, 45, 30] and gCalls == 1 and gOrder == 12
    gs = @[10, 20, 30]
    gCalls = 0
    touchP(addr gs[fv()], 1)
    check gs == @[10, 26, 30] and gCalls == 1
    gs = @[10, 20, 30]
    gCalls = 0
    touch(gs[idOf(1)], 0)
    touch(gs[oneOf("x")], 0)
    check gs == @[10, 30, 30] and gCalls == 2

  test "through a proc value":
    ## RED: each `_dead` declined (`feUnsupportedOp`, `indexCallDecline`).
    replays(sutValSeq, "fs")
    discard verdict(sutValSeq, "fs_dead", sxUnsat)
    replays(sutValArr, "fa")
    discard verdict(sutValArr, "fa_dead", sxUnsat)
    replays(sutValAddr, "fp")
    discard verdict(sutValAddr, "fp_dead", sxUnsat)
    replays(sutValClosure, "fc")
    discard verdict(sutValClosure, "fc_dead", sxUnsat)
    replays(sutValRange, "fr")
    discard verdict(sutValRange, "fr_dead", sxUnsat)
    replays(sutValThrough, "ft")
    discard verdict(sutValThrough, "ft_dead", sxUnsat)
