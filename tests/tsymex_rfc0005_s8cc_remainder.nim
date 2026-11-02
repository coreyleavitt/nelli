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
var gArr: array[3, int]
var gCalls: int
var gOrder: int
var gBig: array[8, int]

proc touch(v: var int; k: int) = v = v + 5 + k

proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k

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

proc sutGenericNarrow(k: int) =
  ## The index is narrower than `int`.
  if k < 0 or k > 1000: return
  gs = @[10, k, 30]
  gCalls = 0
  touch(gs[idOf(1'i8)], 0)
  if gs[1] == k + 5 and gCalls == 1 and k == 2: symexTarget("gn")
  if gs[1] != k + 5 or gCalls != 1: symexTarget("gn_dead")

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
