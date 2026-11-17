## RFC-0016 S8cg (PRC-29), item 2: a `var openArray` view a later argument
## writes is read at the call.
##
## Nim passes a `var openArray` actual as its storage's address and length,
## in the call expression (`ccgcalls`: an `openArray` formal never takes a
## temporary), so `fill(gArr, bumpA())` with `bumpA` writing `gArr[0]` hands
## `fill` the written storage: `[101, 20, 30]`. Batch 7 copied the view where
## the argument stands and declined it (`feEvalOrderUnmodelled`) whenever a
## later argument may write the storage. The view is now read at the call
## (`viewAtCall`); a slice's bounds are checked where the argument stands,
## and a path on which a later call moved a bound or changed the storage's
## length declines there, as `placeLateAddr` does for an lvalue.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
from ./s8cu_helpers import pinDecline, cellKey, faGeneric

const declKey = cellKey(faGeneric, "s8cg_views")

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(fn: typed, lbl: string, want: SymexStatusKind): untyped =
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
      check replayWitness(fn, r.witness, tLabel(lbl), {}).outcome == roConfirmed

var gArr: array[3, int]
var gS: seq[int]
var gStr: string
var gLo: int

proc fill(x: var openArray[int]; k: int) = x[0] = x[0] + k
proc fillC(x: var openArray[char]; k: int) = x[0] = char(ord(x[0]) + k)

proc bumpA(): int =
  ## The later argument: writes the viewed storage.
  gArr[0] = 100
  1

proc bumpS(): int =
  gS[0] = 100
  1

proc bumpStr(): int =
  gStr[0] = 'p'
  1

proc readA(): int =
  ## A later argument that only reads the viewed storage (item 3).
  gArr[2] div 10

proc growS(): int =
  ## Lengthens the seq a slice's check read.
  gS.add 7
  1

proc moveLo(): int =
  ## Moves the slice's lower bound.
  gLo = 1
  1

proc sutOa(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  fill(gArr, bumpA())
  if gArr[0] == 101 and k == 4: symexTarget("oa")
  if gArr[0] != 101: symexTarget("oa_dead")

proc sutOaSlice(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  fill(toOpenArray(gArr, 0, 1), bumpA())
  if gArr[0] == 101 and k == 4: symexTarget("os")
  if gArr[0] != 101: symexTarget("os_dead")

proc sutOaClosure(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  let f = fill
  f(gArr, bumpA())
  if gArr[0] == 101 and k == 4: symexTarget("oc")
  if gArr[0] != 101: symexTarget("oc_dead")

proc sutOaClosureSlice(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  let f = fill
  f(toOpenArray(gArr, 0, 1), bumpA())
  if gArr[0] == 101 and k == 4: symexTarget("ocs")
  if gArr[0] != 101: symexTarget("ocs_dead")

proc sutSeq(k: int) =
  if k < 0 or k > 1000: return
  gS = @[k, 20, 30]
  fill(toOpenArray(gS, 0, 1), bumpS())
  if gS[0] == 101 and k == 6: symexTarget("sq")
  if gS[0] != 101 or gS.len != 3: symexTarget("sq_dead")

proc sutStr(k: int) =
  if k < 0 or k > 100: return
  gStr = "abc"
  gStr[1] = char(ord('a') + k)
  fillC(gStr, bumpStr())
  if gStr[0] == 'q' and k == 2: symexTarget("st")
  if gStr[0] != 'q': symexTarget("st_dead")

proc sutReadOnly(k: int) =
  ## Item 3: a later argument that only reads the storage counts as a read
  ## (S8cc's `scanRead`): the view stands where it is, exact.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  fill(gArr, readA())
  if gArr[0] == k + 3 and k == 8: symexTarget("ro")
  if gArr[0] != k + 3: symexTarget("ro_dead")

proc sutGrown(k: int) =
  ## The later call changes the length the slice's check read.
  if k < 0 or k > 1000: return
  gS = @[k, 20, 30]
  fill(toOpenArray(gS, 0, 1), growS())
  if k == 3: symexTarget("gr")

proc sutMovedLo(k: int) =
  ## The later call moves a bound the slice's check read: natively
  ## `gArr[1]` is written, never `gArr[0]`.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gLo = 0
  fill(toOpenArray(gArr, gLo, 1), moveLo())
  if gArr[0] == k + 1: symexTarget("ml")

proc fillFrom(lo: var int) =
  ## The bound is read through a `var` formal (a hidden dereference) whose
  ## target `moveLo` writes under another name, `gLo`.
  fill(toOpenArray(gArr, lo, 1), moveLo())

proc fillFromNoLater(lo: var int) =
  fill(toOpenArray(gArr, lo, 1), 1)

proc sutDerefNo(k: int) =
  ## A bound read through a dereference with no later call: exact.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gLo = 0
  fillFromNoLater(gLo)
  if gArr[0] == 21: symexTarget("dn")
  if gArr[0] != k + 1: symexTarget("dn_dead")

proc sutDerefLo(k: int) =
  ## A bound read through a dereference whose target a later call writes
  ## under another name. Fail-closed twice: the call's alias guard declines
  ## first, and `boundReadSyms` lists no dereference, so the view would be
  ## copied where it stands and decline.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gLo = 0
  fillFrom(gLo)
  if gArr[1] == 21: symexTarget("dl")

proc sutKeptLo(k: int) =
  ## A bound read from a variable no later argument writes.
  if k < 0 or k > 1000: return
  gArr = [10, k, 30]
  gLo = 1
  fill(toOpenArray(gArr, gLo, 2), bumpA())
  if gArr[0] == 100 and gArr[1] == k + 1 and gArr[2] == 30 and k == 5:
    symexTarget("kl")
  if gArr[0] != 100 or gArr[1] != k + 1 or gArr[2] != 30:
    symexTarget("kl_dead")

suite "S8cg (2): a var openArray view a later argument writes":

  test "nim":
    gArr = [3, 20, 30]
    gLo = 0
    fill(toOpenArray(gArr, gLo, 1), moveLo())
    check gArr == [3, 21, 30]   # the bound is read at the call
    gArr = [4, 20, 30]
    fill(gArr, bumpA())
    check gArr == [101, 20, 30]
    gArr = [4, 20, 30]
    fill(toOpenArray(gArr, 0, 1), bumpA())
    check gArr == [101, 20, 30]
    block:
      let f = fill
      gArr = [4, 20, 30]
      f(gArr, bumpA())
      check gArr == [101, 20, 30]
      gArr = [4, 20, 30]
      f(toOpenArray(gArr, 0, 1), bumpA())
      check gArr == [101, 20, 30]
    gS = @[6, 20, 30]
    fill(toOpenArray(gS, 0, 1), bumpS())
    check gS == @[101, 20, 30]
    gStr = "abc"
    fillC(gStr, bumpStr())
    check gStr == "qbc"
    gArr = [10, 5, 30]
    gLo = 1
    fill(toOpenArray(gArr, gLo, 2), bumpA())
    check gArr == [100, 6, 30]
    gArr = [3, 20, 30]
    gLo = 0
    fillFrom(gLo)
    check gArr == [3, 21, 30]

  test "a whole array, a slice, through a proc value: read at the call":
    ## RED at da0a4a85: each declined (`feEvalOrderUnmodelled`, batch 7).
    replays(sutOa, "oa")
    discard verdict(sutOa, "oa_dead", sxUnsat)
    replays(sutOaSlice, "os")
    discard verdict(sutOaSlice, "os_dead", sxUnsat)
    replays(sutOaClosure, "oc")
    discard verdict(sutOaClosure, "oc_dead", sxUnsat)
    replays(sutOaClosureSlice, "ocs")
    discard verdict(sutOaClosureSlice, "ocs_dead", sxUnsat)

  test "a seq slice, a whole string, a bound no later argument writes":
    replays(sutSeq, "sq")
    discard verdict(sutSeq, "sq_dead", sxUnsat)
    replays(sutStr, "st")
    discard verdict(sutStr, "st_dead", sxUnsat)
    replays(sutKeptLo, "kl")
    discard verdict(sutKeptLo, "kl_dead", sxUnsat)

  test "a later argument that only reads the storage":
    replays(sutReadOnly, "ro")
    discard verdict(sutReadOnly, "ro_dead", sxUnsat)

  test "a later call that moves what the slice's check read declines":
    ## RED for `ml` at da0a4a85 and after the view moved to the call: a
    ## trusted `sxSat`. The walk read `gLo` where the argument stands, Nim
    ## at the call (the native run above), and batch 7's frame condition
    ## named the storage alone (`laterLeavesView`).
    pinDecline(sutGrown, declKey, feEvalOrderUnmodelled, tLabel("gr"), "never checked")
    pinDecline(sutMovedLo, declKey, feEvalOrderUnmodelled, tLabel("ml"), "never checked")

  test "a bound read through a dereference":
    replays(sutDerefNo, "dn")
    discard verdict(sutDerefNo, "dn_dead", sxUnsat)
    pinDecline(sutDerefLo, declKey, feUnsupportedOp, tLabel("dl"), "both through a `var`/`addr` argument and directly")

  test "walker version floor":
    check symexWalkerVersion.parseInt >= 375
