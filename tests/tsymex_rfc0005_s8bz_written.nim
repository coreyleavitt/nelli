## RFC-0005 (soundness channels) slice S8bz -- S8bw's remainder, part A:
## the written-ness of a part (items 3, 4 and 7) and the address of an array
## element (item 5). Every expectation is Nim's (the "nim" tests run the same
## code).
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/types
import s8ct_platform
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

template confirmed(fn: typed, lbl: string): untyped =
  ## A clean `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

template candidate(fn: typed, lbl: string,
                   raised: set[SymexStatusKind] = {}): untyped =
  ## An observed part no write reached: `feGlobalHavoc`, never `sxUnsat`.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown} + raised
    var havoc = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feGlobalHavoc: havoc = true
    check havoc

# ---- 5. the address of an array element ---------------------------------------
#
# RFC-0005 S8bz item 5. S8as gave `let p = addr gArr[1]` a constant index; a
# computed index (S8ax's `elemAddrNode`) stopped at a module-level root, and a
# `var` parameter's seq was no root at all: `heUnsafeCast`.

type O5 = object
  x, y: int

var gA5: array[4, int]
var gO5: array[3, O5]
var gOOB5: array[4, int]
var gS5: seq[int]
var gCall5: seq[int]

proc growCall5() = gCall5.add 1

proc sutAddrSym(i, k: int) =
  if i < 0 or i > 3: return
  for j in 0 .. 3: gA5[j] = 0
  let p = addr gA5[i]
  p[] = k
  if gA5[2] == 5: symexTarget("as")
  if gA5[i] != k: symexTarget("as_dead")

proc sutAddrSymObj(i, k: int) =
  if i < 0 or i > 2: return
  gO5[i].x = 0
  let p = addr gO5[i].x
  p[] = k
  if gO5[i].x == 5: symexTarget("aso")
  if gO5[i].x != k: symexTarget("aso_dead")

proc sutAddrOob(i: int) =
  let p = addr gOOB5[i]
  if i == 0: symexTarget("aoob_never")
  p[] = 1

proc sutAddrUnwritten(i: int) =
  if i < 0 or i > 3: return
  let p = addr gOOB5[i]
  if p[] == 7: symexTarget("aunw")

proc sutAddrSeqGlobal(i, k: int) =
  gS5 = @[0, 0, 0]
  if i < 0 or i > 2: return
  let p = addr gS5[i]
  p[] = k
  if gS5[i] == 5: symexTarget("asg")
  if gS5[i] != k: symexTarget("asg_dead")

proc sutAddrSeqCallee(i: int) =
  gCall5 = @[0, 0]
  if i < 0 or i > 1: return
  let p = addr gCall5[i]
  growCall5()       # may move the elements: `p` dangles
  p[] = 1
  symexTarget("asc")

suite "S8bz (5): the address of an array element":

  test "nim":
    sutAddrSym(2, 5)
    check gA5[2] == 5
    sutAddrSymObj(1, 5)
    check gO5[1].x == 5
    expect IndexDefect:
      sutAddrOob(7)
    sutAddrSeqGlobal(1, 5)
    check gS5[1] == 5

  test "a computed index into a module-level array":
    ## RED: sxUnknown, `heUnsafeCast` (`elemAddrNode` stopped at a
    ## module-level root).
    confirmed(sutAddrSym, "as")
    discard clean(sutAddrSym, "as_dead", sxUnsat)
    confirmed(sutAddrSymObj, "aso")
    discard clean(sutAddrSymObj, "aso_dead", sxUnsat)

  test "its index is checked where `addr` evaluates it, and nothing is read":
    ## RED: sxUnknown, `heUnsafeCast`. The check read observes no value.
    block:
      let r = symexFind(sutAddrOob, tIndexError())
      checkpoint show(r.errors)
      check r.status == sxRaised
      for e in r.errors: check e.severity == sevHint
    candidate(sutAddrUnwritten, "aunw")   # the dereference does read it

  test "a module-level seq, resized by nothing":
    ## RED: sxUnknown, `heUnsafeCast`.
    confirmed(sutAddrSeqGlobal, "asg")
    discard clean(sutAddrSeqGlobal, "asg_dead", sxUnsat)

  test "a module-level seq a callee may resize":
    let r = symexFind(sutAddrSeqCallee, tLabel("asc"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feUnsupportedOp and "may resize" in e.msg: named = true
    check named

# ---- 3. a partial write into an unwritten part ---------------------------------
#
# RFC-0005 S8bz item 3. The written-ness of a global is per part: a symbolic
# element write copies the element's other parts (it does not observe them), a
# case object global's entry value is modelled as any other's, and a `var` or
# `addr` actual is copied in without being read; the callee's read of it is the
# observation.

type
  O3 = object
    x, y: int
  VK3 = enum vkA, vkB
  V3 = object
    n: int
    case k: VK3
    of vkA: a: int
    of vkB: b: int

var gAA3: array[3, O3]
var gAAu3: array[3, O3]
var gAAr3: array[3, O3]
var gV3: V3
var gVw3: V3
var gU3: tuple[a, b: int]
var gUr3: tuple[a, b: int]
var gUa3: tuple[a, b: int]
var gArr3: array[4, int]
var gArrR3: array[4, int]

proc setI3(v: var int; x: int) = v = x
proc readI3(v: var int; x: int) =
  if v == x: symexTarget("vr")
proc setP3(p: ptr int; x: int) = p[] = x
proc readP3(p: ptr int; x: int) =
  if p[] == x: symexTarget("ar")

proc sutSymElem(k: int) =
  if k < 0 or k > 2: return
  gAA3[k].x = 5
  if gAA3[k].x == 5: symexTarget("se")
  if gAA3[k].x != 5: symexTarget("se_dead")

proc sutSymElemOther(k: int) =
  ## The part no write reached, through the same element.
  if k < 0 or k > 2: return
  gAAu3[k].x = 5
  if gAAu3[k].y == 5: symexTarget("seu")

proc sutSymElemRead(k: int) =
  ## A read at another index may meet an element no write reached.
  if k < 0 or k > 1: return
  gAAr3[k].x = 5
  if gAAr3[k + 1].x == 5: symexTarget("ser")

proc sutVariantPlain(k: int) =
  gV3.n = k
  if gV3.n == 5: symexTarget("vp")
  if gV3.n != k: symexTarget("vp_dead")

proc sutVariantArm(k: int) =
  ## Nim checks the branch of the entry value, so the write observes it.
  gVw3.a = k
  if gVw3.a == 5: symexTarget("va")
  if gVw3.a != k: symexTarget("va_dead")

proc sutVarActual(k: int) =
  setI3(gU3.a, k)
  if gU3.a == 5: symexTarget("vw")
  if gU3.a != k: symexTarget("vw_dead")

proc sutVarActualRead(k: int) =
  ## The callee reads the part no write reached.
  readI3(gUr3.a, k)

proc sutVarActualOther(k: int) =
  setI3(gUa3.a, k)
  if gUa3.b == 5: symexTarget("vo")

proc sutAddrActual(k: int) =
  setP3(addr gArr3[3], k)
  if gArr3[3] == 5: symexTarget("aw")
  if gArr3[3] != k: symexTarget("aw_dead")

proc sutAddrActualRead(k: int) =
  readP3(addr gArrR3[3], k)

suite "S8bz (3): a partial write into an unwritten part":

  test "nim":
    sutSymElem(1)
    check gAA3[1].x == 5
    sutVarActual(5)
    check gU3.a == 5
    sutAddrActual(5)
    check gArr3[3] == 5
    sutVariantPlain(5)
    check gV3.n == 5
    sutVariantArm(5)
    check gVw3.a == 5

  test "a symbolic index write into an element of an array of aggregates":
    ## RED: sxSat with `feGlobalHavoc` on `gAA3[0].y`, a part the write only
    ## copies; `se_dead` the same.
    confirmed(sutSymElem, "se")
    discard clean(sutSymElem, "se_dead", sxUnsat)
    candidate(sutSymElemOther, "seu")
    candidate(sutSymElemRead, "ser")

  test "a partial write of a case object global":
    ## RED: sxUnknown, `feGlobalReadUnmodelled`: a case object's entry value
    ## was not modelled.
    confirmed(sutVariantPlain, "vp")
    discard clean(sutVariantPlain, "vp_dead", sxUnsat)
    candidate(sutVariantArm, "va", {sxRaised})
    candidate(sutVariantArm, "va_dead", {sxUnsat, sxRaised})

  test "a `var` or `addr` actual whose part is unwritten":
    ## RED: sxSat with `feGlobalHavoc` on the actual: its copy-in observed it.
    confirmed(sutVarActual, "vw")
    discard clean(sutVarActual, "vw_dead", sxUnsat)
    confirmed(sutAddrActual, "aw")
    discard clean(sutAddrActual, "aw_dead", sxUnsat)
    candidate(sutVarActualOther, "vo")
    # The callee's read is the observation.
    candidate(sutVarActualRead, "vr")
    candidate(sutAddrActualRead, "ar")

# ---- 4. a dereference onto an unwritten candidate ------------------------------
#
# RFC-0005 S8bz item 4. The pointer may address a part no write reached; only
# that sub-path observes it. A scalar part of a global whose entry value is not
# modelled (a `ref` beside it) holds some value of its type all the same.

type NE4 = object
  r: ref int
  n: int

var gD4: tuple[a, b: int]
var gDw4: tuple[a, b: int]
var gNE4: NE4

proc sutDeref(p: ptr int) =
  if p == nil: return
  gD4.a = 0
  if p[] == 9 and gD4.a == 0: symexTarget("d")
  if p[] == 9 and p[] != 9: symexTarget("d_dead")

proc sutDerefWritten(p: ptr int) =
  ## Every candidate written: no sub-path observes anything.
  if p == nil: return
  gDw4.a = 1
  gDw4.b = 1
  if p[] == 9: symexTarget("dw")

proc sutDerefRefSibling(p: ptr int) =
  if p == nil: return
  gNE4.r = nil
  if p[] == 9: symexTarget("dr")

suite "S8bz (4): a dereference onto an unwritten candidate":

  test "only the sub-path that names the part observes it":
    ## RED: every path carried `feGlobalHavoc` (the whole dereference), so
    ## a hit through the pointer's own cell did too.
    block:
      let r = symexFind(sutDeref, tLabel("d"))
      checkpoint show(r.errors)
      check r.status == sxSat
      check replayedOrNotMarshallable(replayWitness(sutDeref, r.witness, tLabel("d"), {}), roConfirmed)
    block:
      let r = symexFind(sutDeref, tLabel("d_dead"))
      checkpoint show(r.errors)
      check r.status == sxUnsat

  test "no candidate unwritten":
    confirmed(sutDerefWritten, "dw")

  test "a scalar part beside a `ref`":
    ## RED: sxUnknown, `feGlobalReadUnmodelled` on `gNE4.n`.
    candidate(sutDerefRefSibling, "dr")

# ---- 7. `{.noinit.}` locals ----------------------------------------------------
#
# RFC-0005 S8bz item 7. S8be modelled `{.global.}` (`isRoutineGlobal`); a
# `{.noinit.}` local with no initialiser declined. It is unwritten: any value
# of its type, per part, and a read of a part no write reached taints the path.

template noinitRead(fn: typed, lbl: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status in {sxSat, sxUnknown}
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feGlobalHavoc and "{.noinit.}" in e.msg: named = true
    check named

proc sutNoinitWrite(k: int) =
  var c {.noinit.}: int
  c = k
  if c == 5: symexTarget("nw")
  if c != k: symexTarget("nw_dead")

proc sutNoinitRead(k: int) =
  var c {.noinit.}: int
  if k == 5 and c == 3: symexTarget("nr")
  if k == 5 and c != c: symexTarget("nr_dead")

proc sutNoinitArr(k: int) =
  var a {.noinit.}: array[3, int]
  a[1] = k
  if a[1] == 5: symexTarget("na")
  if a[1] != k: symexTarget("na_dead")

proc sutNoinitArrOther(k: int) =
  var a {.noinit.}: array[3, int]
  a[1] = k
  if a[0] == 5: symexTarget("nao")

proc sutNoinitTuple(k: int) =
  var t {.noinit.}: tuple[a, b: int]
  t.a = k
  if t.a == 5: symexTarget("nt")

proc sutNoinitTupleOther(k: int) =
  var t {.noinit.}: tuple[a, b: int]
  t.a = k
  if t.b == 5: symexTarget("nto")

proc sutNoinitLoop(k: int) =
  ## Each evaluation of the declaration is its own value.
  for i in 0 .. 1:
    var c {.noinit.}: int
    c = i + k
    if i == 1 and c == 6: symexTarget("nl")

proc sutNoinitString(k: int) =
  var s {.noinit.}: string
  s = "a"
  if k == 5 and s == "a": symexTarget("ns")

proc sutGlobalLocal(k: int) =
  var c {.global.}: int
  c = k
  if c == 5: symexTarget("gl")

suite "S8bz (7): {.global.} and {.noinit.} locals":

  test "nim":
    sutNoinitWrite(5)
    sutNoinitArr(5)
    sutNoinitTuple(5)
    sutNoinitLoop(5)

  test "written before any read":
    ## RED: sxUnknown, `feUnsupportedStmtKind` ("its value is undefined").
    confirmed(sutNoinitWrite, "nw")
    discard clean(sutNoinitWrite, "nw_dead", sxUnsat)
    confirmed(sutNoinitArr, "na")
    discard clean(sutNoinitArr, "na_dead", sxUnsat)
    confirmed(sutNoinitTuple, "nt")
    confirmed(sutNoinitLoop, "nl")

  test "a read of a part no write reached":
    ## RED: sxUnknown, `feUnsupportedStmtKind`, and the name unbound.
    noinitRead(sutNoinitRead, "nr")
    block:
      let r = symexFind(sutNoinitRead, tLabel("nr_dead"))
      checkpoint show(r.errors)
      check r.status == sxUnsat
    noinitRead(sutNoinitArrOther, "nao")
    noinitRead(sutNoinitTupleOther, "nto")

  test "a managed type stays a decline":
    ## Nim destroys the garbage a `{.noinit.}` string holds at its first
    ## assignment (never run here), which no value of the type stands for.
    let r = symexFind(sutNoinitString, tLabel("ns"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      check e.kind != weInternalWalkerFault
      if e.kind == feUnsupportedStmtKind and "managed" in e.msg: named = true
    check named

  test "a {.global.} local":
    confirmed(sutGlobalLocal, "gl")

suite "S8bz: walker version":

  test "the walker version is at least S8bz's":
    check parseInt(symexWalkerVersion) >= 249
