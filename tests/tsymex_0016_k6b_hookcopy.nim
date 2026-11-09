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

proc show(errs: seq[SymexErrorInfo]): string =
  for e in errs:
    if e.severity == sevError: result.add $e.kind & ": " & e.msg & "\n"

const ns = [-5, -1, 1, 3, 4, 7, 12, 49, 51]

template hits(call: untyped): untyped =
  block:
    symexCaptureBegin()
    try:
      call
    except Defect, CatchableError:
      discard
    symexCaptureEnd()

template nativeSees(fn: typed; live, dead: static string) =
  block:
    var l = false
    var d = false
    for n in ns:
      let h = hits(fn(n))
      if live in h: l = true
      if dead in h: d = true
    check l
    check not d

template nativeDiffers(fn: typed; live: static string) =
  ## For some input the hook's copy is not the plain one.
  block:
    var l = false
    for n in ns:
      if live in hits(fn(n)): l = true
    check l

template declinesCopy(fn: typed; lbl: static string) =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & "\n" & show(r.errors)
    check r.status == sxUnknown
    check "does not make the plain copy" in show(r.errors)

template decides(fn: typed; live, dead: static string) =
  block:
    let a = symexFind(fn, tLabel(live))
    checkpoint live & " " & $a.status & "\n" & show(a.errors)
    check a.status == sxSat
    let b = symexFind(fn, tLabel(dead))
    checkpoint dead & " " & $b.status & "\n" & show(b.errors)
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
  test "K6b changed the decline set: walker 293 or later":
    check parseInt(symexWalkerVersion) >= 293

suite "K6b: a hook that is not the plain copy declines":
  test "native: the hook's copy differs from the plain one":
    nativeDiffers(cond1, "cond1_changed")
    nativeDiffers(early1, "early1_changed")
    nativeDiffers(zap1, "zap1_changed")
    nativeDiffers(emit1, "emit1_changed")
    nativeDiffers(loop1, "loop1_changed")
  test "a field copy under an `if`":
    declinesCopy(cond1, "cond1_changed")
  test "a field copy behind an early `return`":
    declinesCopy(early1, "early1_changed")
  test "a callee writes the destination after the copy":
    declinesCopy(zap1, "zap1_changed")
  test "foreign code writes the destination after the copy":
    # declined before K6b too (the hook's effect summary reads the `emit`)
    let r = symexFind(emit1, tLabel("emit1_changed"))
    check r.status == sxUnknown
    check "feGlobalRouteUnproved" in show(r.errors)
  test "a field copy in a loop is not a top-level copy":
    declinesCopy(loop1, "loop1_changed")

suite "K6b: a hook proved the plain copy decides":
  test "native: the hook's copy is the plain one":
    nativeSees(plain1, "plain1_same", "plain1_changed")
    nativeSees(work1, "work1_same", "work1_changed")
    nativeSees(pure1, "pure1_same", "pure1_changed")
  test "the bare copy":
    decides(plain1, "plain1_same", "plain1_changed")
  test "local work around the copy that writes nothing shared":
    decides(work1, "work1_same", "work1_changed")
  test "a walked pure callee around the copy":
    decides(pure1, "pure1_same", "pure1_changed")
