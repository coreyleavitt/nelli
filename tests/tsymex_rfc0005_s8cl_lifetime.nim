## RFC-0005 (soundness channels) slice S8cl -- S8ca's remainder, items 1c, 2 and
## 3: the lifetime magics pinned against Nim, what cannot be read declines, and
## `setLen`. Split from `tsymex_rfc0005_s8cl_magics` for the per-file budget.
##
##   (1c) the lifetime magics S8bl models, pinned against Nim.
##   (2)  a routine whose formals cannot be read (a compiler-generated hook, a
##        generic instance's formal typed by its default), or an object member
##        the type bridge cannot read (`when`), declines instead of failing the
##        build; `wasMoved` is modelled.
##   (3)  `setLen`: its length is evaluated before the old value is read, so a
##        call there that writes the seq is seen (a false sxUnsat before); a
##        `mitems` body that resizes with it decides as `add` and `pop` do.
##
## Every expectation below is Nim's (each "nim" test runs the SUTs natively
## under a capture frame and checks which labels they hit).
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

template declines(fn: typed, lbl, why: string): untyped =
  ## A shape the walk does not model: `sxUnknown`, with the decline named.
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if why in e.msg: named = true
    check named

proc nativeHits(fn: proc (k: int) {.nimcall.}; ks: openArray[int]): HashSet[string] =
  symexCaptureBegin()
  for k in ks: fn(k)
  symexCaptureEnd()

const ks = [-3, 0, 1, 2, 3, 4, 5, 7, 8]

type
  Pt = object
    x, y: int
  HasRef = object
    r: ref int
  Base = ref object of RootObj
    v: int

var gi = 0

# --- (1c) the rest of the audit, against Nim.
proc sutReset(k: int) =
  var x = k
  reset(x)
  if x == 0 and k == 3: symexTarget("rs")
  if x == 3: symexTarget("rs_dead")

proc sutMove(k: int) =
  var a = @[k]
  let b = move(a)
  if a.len == 0 and b[0] == 3: symexTarget("mv")
  if a.len == 1: symexTarget("mv_dead")

proc sutNew(k: int) =
  var o: HasRef
  new(o.r)
  o.r[] = k
  if o.r[] == 3: symexTarget("nw")
  if o.r == nil: symexTarget("nw_dead")

proc sutNewExpr(k: int) =
  let p = new(int)
  p[] = k
  if p[] == 3: symexTarget("ne")
  if p == nil: symexTarget("ne_dead")

type Finalized = ref object
  v: int
proc fin(x: Finalized) {.nimcall.} = discard
proc sutNewFinalizer(k: int) =
  ## The finalizer runs when the cell is collected: not modelled, so declined.
  var b: Finalized
  new(b, fin)
  b.v = k
  if b.v == 3: symexTarget("nf")

type ObjRef = ref object of RootObj
  v: int
proc sutNewObject(k: int) =
  var p: ObjRef
  new(p)
  p.v = k
  if p.v == 3: symexTarget("no")
  if p == nil: symexTarget("no_dead")

type HasSeq = object
  a: int
  s: seq[int]
proc sutResetField(k: int) =
  var o = HasSeq(a: k, s: @[k])
  reset(o.s)
  if o.a == 3 and o.s.len == 0: symexTarget("rf")
  if o.s.len == 1: symexTarget("rf_dead")

proc sutMoveElem(k: int) =
  var s = [@[k], @[2]]
  let b = move(s[0])
  if b[0] == 3 and s[0].len == 0: symexTarget("me")
  if s[0].len == 1: symexTarget("me_dead")

proc sutCopyHook(k: int) =
  var a = @[k]
  var b: seq[int]
  `=copy`(b, a)
  if b[0] == 3: symexTarget("ch")
  if b.len == 0: symexTarget("ch_dead")

proc sutSinkHook(k: int) =
  var a = @[k]
  var b: seq[int]
  `=sink`(b, a)
  if b[0] == 3: symexTarget("sh")
  if b[0] != k: symexTarget("sh_dead")

# --- (2) wasMoved; the generated hooks.
proc sutWasMoved(k: int) =
  var s = @[k]
  wasMoved(s)
  if s.len == 0 and k == 3: symexTarget("wm")
  if s.len == 1: symexTarget("wm_dead")

proc sutWasMovedInt(k: int) =
  var x = k
  wasMoved(x)
  if x == 0 and k == 3: symexTarget("wi")
  if x == 3: symexTarget("wi_dead")

proc sutWasMovedPtr(k: int) =
  var x = k
  let p = addr x
  wasMoved(p[])
  if x == 0 and k == 3: symexTarget("wp")
  if x == 3: symexTarget("wp_dead")

proc sutDup(k: int) =
  var a = @[k]
  var b = `=dup`(a)
  b[0] = 7
  if a[0] == 3: symexTarget("du")
  if a[0] != k or b[0] != 7: symexTarget("du_dead")

proc sutDestroy(k: int) =
  var s = @[k]
  `=destroy`(s)
  if k == 3: symexTarget("ds")

proc sutCreate(k: int) =
  ## A generic instance's formal typed only by its default (`size = 1.Positive`)
  ## stopped the compile: "node has no type".
  let p = create(int)
  p[] = k
  if p[] == 3: symexTarget("cr")
  dealloc(p)

proc sutGcRef(k: int) =
  ## `GC_ref` reaches `RefHeader`, an object with a `when` member, which
  ## stopped the compile: "Expected nnkIdentDefs, got nnkRecWhen".
  var p: ref int
  new(p)
  GC_ref(p)
  p[] = k
  if p[] == 3: symexTarget("gr")
  GC_unref(p)

type WhenMember = object
  a: int
  when defined(nelliNeverDefined):
    b: int
  else:
    c: int
proc sutWhenMember(k: int) =
  var o: WhenMember
  o.a = k
  if o.a == 3: symexTarget("wn")

# --- (3) setLen.
proc sutSetLen(k: int) =
  var s = @[1, 2, 3]
  s.setLen(1)
  if s.len == 1 and k == 3: symexTarget("sl")
  if s.len == 3: symexTarget("sl_dead")

var gs: seq[int]
proc growG(): int =
  gs.add 5
  2

proc sutSetLenWrites(k: int) =
  ## The length's call adds to the seq; Nim resizes what that left.
  gs = @[1]
  gs.setLen(growG())
  if gs[1] == 5 and k == 3: symexTarget("sw")
  if gs[1] == 0: symexTarget("sw_dead")

proc bumpLen(): int =
  gi = 1
  1

proc sutSetLenLater(k: int) =
  ## The length's call writes the index the lvalue reads.
  gi = 0
  var a = [@[1, 2], @[3, 4]]
  setLen(a[gi], bumpLen())
  if k == 3: symexTarget("sa")

proc sutMitemsSetLen(k: int) =
  var s = @[1, 2, 3]
  var hit = false
  try:
    for x in mitems(s):
      if k == 3: s.setLen(1)
  except AssertionDefect:
    hit = true
  if hit and k == 3: symexTarget("ms")
  if hit and k != 3: symexTarget("ms_dead")

suite "S8cl (1c): the audit of the lifetime magics":
  test "nim":
    let h = nativeHits(sutReset, ks) + nativeHits(sutMove, ks) +
            nativeHits(sutNew, ks) + nativeHits(sutNewExpr, ks) +
            nativeHits(sutNewFinalizer, ks) + nativeHits(sutNewObject, ks) +
            nativeHits(sutResetField, ks) + nativeHits(sutMoveElem, ks) +
            nativeHits(sutCopyHook, ks) + nativeHits(sutSinkHook, ks)
    for l in ["rs", "mv", "nw", "ne", "nf", "no", "rf", "me", "ch", "sh"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "reset, move, new":
    clean(sutReset, "rs", sxSat)
    clean(sutReset, "rs_dead", sxUnsat)
    clean(sutMove, "mv", sxSat)
    clean(sutMove, "mv_dead", sxUnsat)
    clean(sutNew, "nw", sxSat)
    clean(sutNew, "nw_dead", sxUnsat)
    clean(sutNewExpr, "ne", sxSat)
    clean(sutNewExpr, "ne_dead", sxUnsat)
    declines(sutNewFinalizer, "nf", "magic \"NewFinalize\"")

  test "a field, an element, an object, the hooks called by name":
    clean(sutNewObject, "no", sxSat)
    clean(sutNewObject, "no_dead", sxUnsat)
    clean(sutResetField, "rf", sxSat)
    clean(sutResetField, "rf_dead", sxUnsat)
    clean(sutMoveElem, "me", sxSat)
    clean(sutMoveElem, "me_dead", sxUnsat)
    clean(sutCopyHook, "ch", sxSat)
    clean(sutCopyHook, "ch_dead", sxUnsat)
    # Batch 10: S8cb models `=sink` on a type with no user hook as the assignment
    # (`nnkSinkAsgn`), which S8cl declined. The "nim" test above reaches `sh`.
    clean(sutSinkHook, "sh", sxSat)
    clean(sutSinkHook, "sh_dead", sxUnsat)

suite "S8cl (2): wasMoved, and what cannot be read declines":
  test "nim":
    let h = nativeHits(sutWasMoved, ks) + nativeHits(sutWasMovedInt, ks) +
            nativeHits(sutWasMovedPtr, ks)
    for l in ["wm", "wi", "wp"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "wasMoved":
    clean(sutWasMoved, "wm", sxSat)
    clean(sutWasMoved, "wm_dead", sxUnsat)
    clean(sutWasMovedInt, "wi", sxSat)
    clean(sutWasMovedInt, "wi_dead", sxUnsat)
    clean(sutWasMovedPtr, "wp", sxSat)
    clean(sutWasMovedPtr, "wp_dead", sxUnsat)

  test "a generated hook's formals are not read: this file compiles":
    # Batch 10: S8cb models `=dup` of a plain value, a seq among them, which S8cl
    # declined. The native run below reaches `du`, and the copy is not an alias.
    let h = nativeHits(sutDup, ks)
    check "du" in h
    check "du_dead" notin h
    clean(sutDup, "du", sxSat)
    clean(sutDup, "du_dead", sxUnsat)
    declines(sutDestroy, "ds", "=destroy")

  test "what stopped the compile declines: create, GC_ref, a when member":
    let h = nativeHits(sutCreate, ks) + nativeHits(sutGcRef, ks) +
            nativeHits(sutWhenMember, ks)
    for l in ["cr", "gr", "wn"]:
      checkpoint l
      check l in h
    declines(sutCreate, "cr", "create")
    declines(sutGcRef, "gr", "nnkCast")
    declines(sutWhenMember, "wn", "WhenMember")

suite "S8cl (3): setLen":
  test "nim":
    let h = nativeHits(sutSetLen, ks) + nativeHits(sutSetLenWrites, ks) +
            nativeHits(sutMitemsSetLen, ks)
    for l in ["sl", "sw", "ms"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "setLen decides, and sees what its length's call wrote":
    clean(sutSetLen, "sl", sxSat)
    clean(sutSetLen, "sl_dead", sxUnsat)
    clean(sutSetLenWrites, "sw", sxSat)
    clean(sutSetLenWrites, "sw_dead", sxUnsat)
    declines(sutSetLenLater, "sa", "feEvalOrderUnmodelled")

  test "a mitems body that resizes with setLen decides":
    clean(sutMitemsSetLen, "ms", sxSat)
    clean(sutMitemsSetLen, "ms_dead", sxUnsat)

suite "S8cl: walker version":
  test "symexWalkerVersion >= 248":
    check parseInt(symexWalkerVersion) >= 248
