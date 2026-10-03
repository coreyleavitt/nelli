## RFC-0005 S8bk -- the address-of-argument timing suite's fixture: its
## types, globals, routines and functions under test. Included by
## `tsymex_rfc0005_s8bk_argtiming` and its two siblings (`_addr`,
## `_checks`), split by RFC-0005 S8br so each file compiles and runs under
## 60 s on each backend.
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
    check replayWitness(fn, r.witness, tLabel(lbl), {}) == roConfirmed

template declines(fn: typed, lbl: string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    check r.errors.hasKind(feEvalOrderUnmodelled)
    check "never checked" in show(r.errors)
    check not r.errors.hasKind(weInternalWalkerFault)

type Box = ref object
  x: int
type Outer = ref object
  inner: Box
type Holder = ref object
  s: seq[int]

var gP: Box
var gO: Outer
var gA: array[3, Box]
var gArr: array[3, int]
var gs: seq[int]
var gi: int
var gSeen: int
var gCalls: int
var gH: Holder

proc moveP(): int =
  gP = Box(x: 100)
  0

proc writeOld(): int =
  ## Writes the object `gP` holds, then rebinds `gP`.
  gP.x = 50
  gP = Box(x: 100)
  0

proc moveInner(): int =
  gO.inner = Box(x: 100)
  0

proc moveA0(): int =
  gA[0] = Box(x: 100)
  0

proc incI(): int =
  inc gi
  0

proc bumpArr(): int =
  gArr[0] = 50
  0

proc bumpS(): int =
  gs[0] = 50
  0

proc shrinkS(): int =
  gs = @[gs[0]]
  0

proc moveH(): int =
  gH = Holder(s: @[1])
  0

proc getB(): Box =
  inc gCalls
  gP

proc touch(v: var int; k: int) = v = v + 5 + k

proc touchG(v: var int; k: int) =
  ## Reads `gP` too: a heap actual is passed by reference (S8ba).
  v = v + 5 + k
  gSeen = gP.x

proc touchP(v: ptr int; k: int) = v[] = v[] + 5 + k

proc touchPG(v: ptr int; k: int) =
  ## Reads `gP` too: an `addr` heap actual is passed by reference (S8ba).
  v[] = v[] + 5 + k
  gSeen = gP.x

proc touchB(v: var int; k: int): bool =
  v = v + 5 + k
  true

proc fwd(v: var int) =
  ## A `var` formal forwarded on: its address was taken by `fwd`'s caller.
  touch(v, moveP())

# ---- copy-in / copy-out ------------------------------------------------------

proc sutCopy(k: int) =
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  touch(gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 3: symexTarget("cp")
  if gP.x != 105 or old.x != k: symexTarget("cp_dead")

proc sutCopyOld(k: int) =
  ## The later call writes the object first: the callee still sees the new.
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  touch(gP.x, writeOld())
  if gP.x == 105 and old.x == 50 and k == 4: symexTarget("co")
  if gP.x != 105 or old.x != 50: symexTarget("co_dead")

proc sutGuard(k: int) =
  ## The call is an `if` condition.
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  if touchB(gP.x, moveP()):
    if gP.x == 105 and old.x == k and k == 3: symexTarget("gd")
    if gP.x != 105 or old.x != k: symexTarget("gd_dead")

proc sutChain(k: int) =
  ## A field-of-field chain rebound partway (`gO.inner`).
  if k < 0 or k > 1000: return
  gO = Outer(inner: Box(x: k))
  let old = gO.inner
  touch(gO.inner.x, moveInner())
  if gO.inner.x == 105 and old.x == k and k == 5: symexTarget("ch")
  if gO.inner.x != 105 or old.x != k: symexTarget("ch_dead")

proc sutArr(k: int) =
  ## The later call writes the element: the callee reads it after.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  touch(gArr[0], bumpArr())
  if gArr[0] == 55 and k == 6: symexTarget("ar")
  if gArr[0] != 55: symexTarget("ar_dead")

proc sutSeq(k: int) =
  if k < 0 or k > 1000: return
  gs = @[k, 20, 30]
  touch(gs[0], bumpS())
  if gs[0] == 55 and k == 7: symexTarget("sq")
  if gs[0] != 55: symexTarget("sq_dead")

proc sutFwd(k: int) =
  ## Already right: the address was taken at `fwd(gP.x)`.
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  fwd(gP.x)
  if old.x == k + 5 and gP.x == 100 and k == 8: symexTarget("fw")
  if old.x != k + 5 or gP.x != 100: symexTarget("fw_dead")

# ---- an `addr` actual (S8an's cell) ------------------------------------------

proc sutAddr(k: int) =
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  touchP(addr gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 9: symexTarget("ad")
  if gP.x != 105 or old.x != k: symexTarget("ad_dead")

proc sutAddrRef(k: int) =
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  touchPG(addr gP.x, moveP())
  if gP.x == 105 and old.x == k and gSeen == 105 and k == 9: symexTarget("ar2")
  if gP.x != 105 or old.x != k: symexTarget("ar2_dead")

proc sutAddrIdx(k: int) =
  ## The later call writes the element of an `addr` actual's cell.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gi = 0
  touchP(addr gArr[gi], bumpArr())
  if gArr[0] == 55 and k == 2: symexTarget("ai")
  if gArr[0] != 55: symexTarget("ai_dead")

proc sutAddrIdxMoved(k: int) =
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gi = 0
  touchP(addr gArr[gi], incI())
  if gArr[1] == 25 and k == 1: symexTarget("am")

# ---- by reference (S8ba / S8bd) ------------------------------------------------

proc sutRefSym(k: int) =
  ## A symbol base is read at the call: already right.
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  touchG(gP.x, moveP())
  if gP.x == 105 and old.x == k and gSeen == 105 and k == 2: symexTarget("rs")
  if gP.x != 105 or old.x != k: symexTarget("rs_dead")

proc sutRefElem(k: int) =
  ## An element base whose index the later call leaves alone, while it
  ## rebinds the element: the callee writes the new box.
  if k < 0 or k > 1000: return
  gA = [Box(x: k), Box(x: 20), Box(x: 30)]
  gP = gA[1]
  let old = gA[0]
  gi = 0
  touchG(gA[gi].x, moveA0())
  if gA[0].x == 105 and old.x == k and k == 1: symexTarget("re")
  if gA[0].x != 105 or old.x != k: symexTarget("re_dead")

proc sutRefCall(k: int) =
  ## A call base is evaluated where it stands, once: the OLD box.
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  gCalls = 0
  touchG(getB().x, moveP())
  if old.x == k + 5 and gP.x == 100 and gCalls == 1 and k == 3:
    symexTarget("rc")
  if old.x != k + 5 or gP.x != 100 or gCalls != 1: symexTarget("rc_dead")

# ---- a later call changes what an address check read -------------------------

proc sutIdxMoved(k: int) =
  ## Nim checks `gi == 0` and writes `gArr[1]`, an index it never checked.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gi = 0
  touch(gArr[gi], incI())
  if gArr[1] == 25 and k == 1: symexTarget("im")

proc sutIdxKept(k: int) =
  ## The index is unchanged: exact.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gi = 0
  touch(gArr[gi], bumpArr())
  if gArr[0] == 55 and k == 1: symexTarget("ik")
  if gArr[0] != 55: symexTarget("ik_dead")

proc sutSeqShrunk(k: int) =
  ## The seq is shortened after its bound check passed.
  if k < 0 or k > 1000: return
  gs = @[k, 20, 30]
  gi = 2
  touch(gs[gi], shrinkS())
  if k == 1: symexTarget("ss")

proc sutRefElemMoved(k: int) =
  ## S8bd's element base: the later call moves the index.
  if k < 0 or k > 1000: return
  gA = [Box(x: k), Box(x: 20), Box(x: 30)]
  gP = gA[2]
  gi = 0
  touchG(gA[gi].x, incI())
  if gA[1].x == 25 and k == 1: symexTarget("rm")

proc sutHeapIdx(k: int) =
  ## The check reads a seq through a ref (`gH.s`), itself moved to the
  ## call: no snapshot carries it, so the call declines.
  if k < 0 or k > 1000: return
  gH = Holder(s: @[k, 20, 30])
  gi = 2
  touch(gH.s[gi], moveH())
  if k == 1: symexTarget("hx")

# ---- through a proc value (S8bh's `closureCallIR`) ---------------------------

proc sutClosure(k: int) =
  ## RFC-0005 batch 5: a call through a proc value takes the address at the
  ## call too (`let f = touch; f(gP.x, moveP())`).
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  let f = touch
  f(gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 3: symexTarget("cl")
  if gP.x != 105 or old.x != k: symexTarget("cl_dead")

proc sutClosureAddr(k: int) =
  if k < 0 or k > 1000: return
  gP = Box(x: k)
  let old = gP
  let f = touchP
  f(addr gP.x, moveP())
  if gP.x == 105 and old.x == k and k == 4: symexTarget("ca")
  if gP.x != 105 or old.x != k: symexTarget("ca_dead")

proc sutClosureIdxMoved(k: int) =
  ## Nim checks `gi == 0` and writes `gArr[1]`, an index it never checked.
  if k < 0 or k > 1000: return
  gArr = [k, 20, 30]
  gi = 0
  let f = touch
  f(gArr[gi], incI())
  if gArr[1] == 25 and k == 1: symexTarget("cm")
