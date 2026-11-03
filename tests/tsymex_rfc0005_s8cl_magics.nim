## RFC-0005 (soundness channels) slice S8cl -- S8ca's remainder, items 1a and 1b:
## a bodiless magic is never a silent no-op. It is modelled, or it declines.
## `tsymex_rfc0005_s8cl_lifetime` has items 1c, 2 and 3.
##
##   (1a) `unsafeNew(p, n)` allocates: a fresh zeroed cell, `RangeDefect` on a
##        negative size, a decline when the size is under the pointee's or
##        above the modelled bound. S8bl declined it; before S8bl it was a
##        no-op, `p` stayed nil.
##   (1b) a magic with no body to walk and no `var` formal declines:
##        `ensureMove` and `procCall` returned the zero value, a clean false
##        sxUnsat (`ensureMove`) and a clean false sxSat (`procCall`). Batch 10:
##        S8cb models `ensureMove` (its value is `x`'s), so its labels are
##        decided, and the native run below confirms them; `procCall` declines.
##
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

# --- (1a) unsafeNew.
proc sutUnsafeNew(k: int) =
  var p: ref int
  unsafeNew(p, 8)
  p[] = k
  if p[] == 3: symexTarget("un")
  if p[] == 3 and k != 3: symexTarget("un_dead")

proc sutUnsafeNotNil(k: int) =
  ## The false sxUnsat the October notes record: `p` stayed nil.
  var p: ref int
  unsafeNew(p, 8)
  if p != nil and k == 3: symexTarget("unn")
  if p == nil: symexTarget("unn_dead")

proc sutUnsafeZero(k: int) =
  var p: ref Pt
  unsafeNew(p, sizeof(Pt) + 16)   # room beyond the pointee: unobservable
  if p.x == 0 and p.y == 0 and k == 3: symexTarget("uz")
  if p.x != 0 or p.y != 0: symexTarget("uz_dead")

proc sutUnsafeNegative(k: int) =
  var hit = false
  var p: ref int
  if k < 0 or (k >= 8 and k < 1000):   # the sizes that neither raise nor decline
    try:
      unsafeNew(p, k)
    except RangeDefect:
      hit = true
  if hit and k == -3: symexTarget("ug")
  if hit and k >= 0: symexTarget("ug_dead")

proc sutUnsafeSymbolic(k: int) =
  ## A symbolic size at least the pointee's is the allocation; under it the
  ## allocation is too small for the pointee, and that path declines.
  var p: ref int
  if k >= 8:
    unsafeNew(p, k)
    p[] = k
    if p[] == 8: symexTarget("uy")
    if p[] == 7: symexTarget("uy_dead")

proc sutUnsafeTooSmall(k: int) =
  var p: ref Pt
  unsafeNew(p, 8)
  if k == 3: symexTarget("us")

proc sutUnsafeHuge(k: int) =
  if k > 0 and k < 1000:
    var p: ref int
    unsafeNew(p, k + 100_000_000)
    if k == 3: symexTarget("uh")

proc sutUnsafeField(k: int) =
  var o: HasRef
  unsafeNew(o.r, 8)
  o.r[] = k
  if o.r[] == 3: symexTarget("uf")
  if o.r == nil: symexTarget("uf_dead")

proc sutUnsafeElem(k: int) =
  var a: array[2, ref int]
  unsafeNew(a[1], 8)
  a[1][] = k
  if a[1][] == 3 and a[0] == nil: symexTarget("ue")
  if a[1] == nil: symexTarget("ue_dead")

proc sutUnsafeTwoCells(k: int) =
  var p, q: ref int
  unsafeNew(p, 8)
  unsafeNew(q, 8)
  p[] = k
  q[] = 1
  if p != q and p[] == 3: symexTarget("ut")
  if p == q: symexTarget("ut_dead")

proc sutUnsafeRootObj(k: int) =
  var b: Base
  unsafeNew(b, sizeof(Base()[]))
  b.v = k
  if b.v == 3: symexTarget("ur")
  if b.v == 3 and k != 3: symexTarget("ur_dead")

var gi = 0
proc bumpSize(): int =
  gi = 1
  8

proc sutUnsafeLater(k: int) =
  ## The size's call writes the index the lvalue reads.
  gi = 0
  var a: array[2, ref int]
  unsafeNew(a[gi], bumpSize())
  if k == 3: symexTarget("ul")

# --- (1b) a magic with no body and no `var` formal.
proc sutEnsureMove(k: int) =
  var a = @[k]
  let b = ensureMove(a)
  if b.len == 1 and k == 3: symexTarget("em")
  if b.len == 0: symexTarget("em_dead")

proc idf(x: int): int = x

proc sutProcCall(k: int) =
  let r = procCall(idf(k))
  if r == 3: symexTarget("pc")
  if r == 3 and k != 3: symexTarget("pc_dead")

suite "S8cl (1a): unsafeNew is an allocation":
  test "nim":
    let h = nativeHits(sutUnsafeNew, ks) + nativeHits(sutUnsafeNotNil, ks) +
            nativeHits(sutUnsafeZero, ks) + nativeHits(sutUnsafeNegative, ks) +
            nativeHits(sutUnsafeSymbolic, ks) + nativeHits(sutUnsafeField, ks) +
            nativeHits(sutUnsafeElem, ks) + nativeHits(sutUnsafeTwoCells, ks) +
            nativeHits(sutUnsafeRootObj, ks)
    for l in ["un", "unn", "uz", "ug", "uy", "uf", "ue", "ut", "ur"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "a fresh zeroed cell of a variable":
    clean(sutUnsafeNew, "un", sxSat)
    clean(sutUnsafeNew, "un_dead", sxUnsat)
    clean(sutUnsafeNotNil, "unn", sxSat)
    clean(sutUnsafeNotNil, "unn_dead", sxUnsat)
    clean(sutUnsafeZero, "uz", sxSat)
    clean(sutUnsafeZero, "uz_dead", sxUnsat)
    clean(sutUnsafeTwoCells, "ut", sxSat)
    clean(sutUnsafeTwoCells, "ut_dead", sxUnsat)
    clean(sutUnsafeRootObj, "ur", sxSat)
    clean(sutUnsafeRootObj, "ur_dead", sxUnsat)

  test "of a field and of an array element":
    clean(sutUnsafeField, "uf", sxSat)
    clean(sutUnsafeField, "uf_dead", sxUnsat)
    clean(sutUnsafeElem, "ue", sxSat)
    clean(sutUnsafeElem, "ue_dead", sxUnsat)

  test "the size":
    clean(sutUnsafeNegative, "ug", sxSat)
    clean(sutUnsafeNegative, "ug_dead", sxUnsat)
    declines(sutUnsafeSymbolic, "uy_dead", "under its pointee")
    declines(sutUnsafeTooSmall, "us", "under its pointee")
    declines(sutUnsafeHuge, "uh", "is not modelled")
    declines(sutUnsafeLater, "ul", "feEvalOrderUnmodelled")

suite "S8cl (1b): a magic with no body declines":
  test "nim":
    let h = nativeHits(sutEnsureMove, ks) + nativeHits(sutProcCall, ks)
    for l in ["em", "pc"]:
      checkpoint l
      check l in h
      check (l & "_dead") notin h

  test "ensureMove is decided, as the native run has it":
    clean(sutEnsureMove, "em", sxSat)
    clean(sutEnsureMove, "em_dead", sxUnsat)

  test "procCall declines, each label":
    declines(sutProcCall, "pc", "ProcCall")
    declines(sutProcCall, "pc_dead", "ProcCall")

suite "S8cl: walker version":
  test "symexWalkerVersion >= 248":
    check parseInt(symexWalkerVersion) >= 248
