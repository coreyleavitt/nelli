## RFC-0016 K6b (W-09) -- the hook copy-proof.
##
## The walk models an assignment of a value whose type has a user `=copy` as the
## plain field-by-field copy. `routeHookCopies` proves a hook makes exactly that
## copy, and a hook it cannot prove declines every read of a value
## (`feGlobalRouteUnproved`, "does not make the plain copy"). Before K6b its
## `check` defaulted to "copied": any field copy it saw anywhere in the body, at
## any depth, counted, and a statement it did not recognise counted as no write.
## So a copy under an `if`, behind an early `return`, or undone by a callee that
## writes the destination (`zap(a)` passes the `var` parameter with no
## `nnkHiddenAddr`) or by foreign code (`emit`) was proved a plain copy.
##
## K6b: a field copy counts only as a top-level statement of the body; every
## other statement must not mention the destination, must not leave the hook
## (`return`, `raise`) and must not `mayWrite` (K6a). Each pin has a native run
## that shows the hook's copy is not the plain one, then the walker's verdict.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

const ns = [-5, -1, 1, 3, 4, 7, 12, 49, 51]

template nativeDiffers(fn: typed; live: static string) =
  ## For some input the hook's copy is not the plain one. The declined shapes
  ## are not decided, so this native run is checked here; the plain ones are
  ## checked by `pinExact`'s witness and domain.
  block:
    var l = false
    for n in ns:
      if live in nativeRun(fn(n)).hits: l = true
    check l

template declinesCopy(fn: typed; lbl: static string; cell: static string;
                      why = "does not make the plain copy") =
  pinDecline(fn, cellKey(axReadOnly, cell), feGlobalRouteUnproved,
             tLabel(lbl), needle = why)

template decidesCopy(fn: typed; live, dead: static string;
                     cell: static string) =
  block:
    let a = pinExact(fn, cellKey(axReadOnly, cell), tLabel(live))
    check a.status == sxSat
    let b = pinExact(fn, cellKey(axReadOnly, cell), tLabel(dead))
    check b.status == sxUnsat

var gq: int

type
  CondC = object
    v: int
  EarlyC = object
    v: int
  ZapC = object
    v: int
  EmitC = object
    v: int
  LoopC = object
    v: int
  PlainC = object
    v: int
  WorkC = object
    v: int
  PureC = object
    v: int

proc pureAdd(a, b: int): int = a + b
proc zap(x: var ZapC) = x.v = 0

# ---- hooks the old check proved "copied" although they are not ---------------
proc `=copy`(a: var CondC; b: CondC) =
  if b.v > 0: a.v = b.v
proc `=copy`(a: var EarlyC; b: EarlyC) =
  if b.v < 0: return
  a.v = b.v
proc `=copy`(a: var ZapC; b: ZapC) =
  a.v = b.v
  zap(a)
proc `=copy`(a: var EmitC; b: EmitC) =
  a.v = b.v
  {.emit: "`a`->v = 0;".}
proc `=copy`(a: var LoopC; b: LoopC) =
  for i in 0 ..< 2:
    a.v = b.v
    if i == 1: a.v = 0

# ---- hooks that are the plain copy, with work that writes nothing shared -----
proc `=copy`(a: var PlainC; b: PlainC) =
  a.v = b.v
proc `=copy`(a: var WorkC; b: WorkC) =
  var t = b.v + 1
  if t > 3: t = t - 1
  a.v = b.v
  discard t
proc `=copy`(a: var PureC; b: PureC) =
  discard pureAdd(b.v, 1)
  a.v = b.v

template copyShape(name: untyped; T: typedesc; lbl: static string) =
  proc name(k: int) =
    var x = T(v: k)
    var y = x
    x.v = 0
    y.v = y.v
    if y.v != k: symexTarget(lbl & "_changed")
    if y.v == k: symexTarget(lbl & "_same")

copyShape(cond1, CondC, "cond1")
copyShape(early1, EarlyC, "early1")
copyShape(zap1, ZapC, "zap1")
copyShape(emit1, EmitC, "emit1")
copyShape(loop1, LoopC, "loop1")
copyShape(plain1, PlainC, "plain1")
copyShape(work1, WorkC, "work1")
copyShape(pure1, PureC, "pure1")

suite "K6b: version floor":
  test "K6b changed the decline set: walker 299 or later":
    check parseInt(symexWalkerVersion) >= 299

suite "K6b: a hook that is not the plain copy declines":
  test "native: the hook's copy differs from the plain one":
    nativeDiffers(cond1, "cond1_changed")
    nativeDiffers(early1, "early1_changed")
    nativeDiffers(zap1, "zap1_changed")
    nativeDiffers(emit1, "emit1_changed")
    nativeDiffers(loop1, "loop1_changed")
  test "a field copy under an `if`":
    declinesCopy(cond1, "cond1_changed", "hookcopy/conditional")
  test "a field copy behind an early `return`":
    declinesCopy(early1, "early1_changed", "hookcopy/early-return")
  test "a callee writes the destination after the copy":
    declinesCopy(zap1, "zap1_changed", "hookcopy/callee-write")
  test "foreign code writes the destination after the copy":
    # declined before K6b too (the hook's effect summary reads the `emit`)
    declinesCopy(emit1, "emit1_changed", "hookcopy/foreign-write", "")
  test "a field copy in a loop is not a top-level copy":
    declinesCopy(loop1, "loop1_changed", "hookcopy/loop")

suite "K6b: a hook proved the plain copy decides":
  test "the bare copy":
    decidesCopy(plain1, "plain1_same", "plain1_changed", "hookcopy/plain")
  test "local work around the copy that writes nothing shared":
    decidesCopy(work1, "work1_same", "work1_changed", "hookcopy/local-work")
  test "a walked pure callee around the copy":
    decidesCopy(pure1, "pure1_same", "pure1_changed", "hookcopy/walked-pure")
