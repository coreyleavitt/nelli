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
##
## RFC-0005 S8cm: part 1 of 2 of this suite, with
## `tsymex_rfc0005_s8cl_lifetime_b`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 65 s).

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

from ./s8cu_helpers import nativeHits

const ks = [-3, 0, 1, 2, 3, 4, 5, 7, 8]

type
  Pt = object
    x, y: int
  HasRef = object
    r: ref int
  Base = ref object of RootObj
    v: int

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

type WhenMember = object
  a: int
  when defined(nelliNeverDefined):
    b: int
  else:
    c: int
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
