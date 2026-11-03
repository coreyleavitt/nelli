## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 4 of 6 of this suite, with
## `tsymex_rfc0005_s8bn_remainder`, `tsymex_rfc0005_s8bn_remainder_b`,
## `tsymex_rfc0005_s8bn_remainder_c`, `tsymex_rfc0005_s8bn_remainder_e`,
## `tsymex_rfc0005_s8bn_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 121 s).

import std/[unittest, strutils, options, macros, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser

macro progOf(fn: typed): untyped =
  ## The `SymexProgram` `symexFind` would build for `fn`, so a test can read
  ## the raw `RawResult` (its `candidates`), which `symexFind` folds away.
  let parsed = parseEntryImpl(fn, "progOf",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  let b = parsed.bodyNimNode
  let p = parsed.paramsNimNode
  let pr = parsed.procsNimNode
  let u = parsed.userExnHierarchyNimNode
  let pe = parsed.parseErrorsNimNode
  result = quote do:
    SymexProgram(params: `p`, body: `b`, procs: `pr`,
                 userExnHierarchy: `u`, parseErrors: `pe`)

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template clean(fn: typed, lbl: string, want: SymexStatusKind,
               st: SymexSettings = SymexSettings()): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl), st)
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == want
    # A hint (`hePtrFamily` on a witness through a `ptr`) is not a decline.
    for e in r.errors: check e.severity == sevHint
    r

template declines(fn: typed, lbl: string, ek: SymexErrorKind,
                  needle: string): untyped =
  block:
    let r = symexFind(fn, tLabel(lbl))
    checkpoint lbl & " " & $r.status & " " & show(r.errors)
    check r.status == sxUnknown
    var named = false
    for e in r.errors:
      if e.kind == ek and needle in e.msg: named = true
    check named

# ---- 1-2. ptr alias witnesses ------------------------------------------------
#
# RFC-0005 S8bn items 1 and 2. S8bh aimed a `ptr` of unknown origin at a
# ref object's field, a global or a `var` parameter, and the `sxSat` was
# sound; but its witness replayed only when the field's object was built
# before the pointer (parameter order), and never for a global or a `var`
# parameter (the snapshot held no cell for either).

type PQ = ref object
  x: int
  s: string

type VQ = ref object
  x: int

# ---- 6b. S8bk's late address on a call through a proc value -----------------
#
# RFC-0005 S8bn item 6 (S8bk's integration note). Nim takes a `var` / `addr`
# actual's address AT THE CALL, after every later argument: `let f = touch;
# f(gB.x, moveB())` compiles to `T1_ = moveB(); f(&(*gB).x, T1_)`, so when
# `moveB` rebinds `gB` the callee reads and writes the new object. S8bh's
# call through a proc value copied the value in (or filled the `addr` cell)
# where the argument stood and wrote it back through the late address. Only
# the address's checks (an index's bound) run where the argument stands; a
# later call that changes what one read declines.

type LBox = ref object
  x: int

# ---- 9. a parameter's run-type tags follow its static type ------------------
#
# RFC-0005 S8bn item 9. S8bh stored a hierarchy object's run-type tag per
# depth at allocation, but a parameter's tags were free: a `Mid9` parameter
# could carry a tag no `Mid9` has. When it aliases a `Base9` parameter, a
# down-conversion of the `Base9` one could then fail although the object is
# a `Mid9` (a `sxSat` no Nim value reaches).

type
  Base9 = ref object of RootObj
    x: int
  Mid9 = ref object of Base9
    y: int
  Leaf9 = ref object of Mid9
  Side9 = ref object of Base9

proc sutTagAlias(b: Base9; d: Mid9) =
  if b == nil or d == nil: return
  if Base9(d) == b:
    try:
      let m = Mid9(b)
      if m.y == d.y: symexTarget("ta")
    except ObjectConversionDefect:
      symexTarget("ta_dead")

proc sutTagSide(b: Base9; s: Side9) =
  ## A `Side9` is never a `Mid9`.
  if s == nil: return
  if Base9(s) == b:
    try:
      discard Mid9(b)
      symexTarget("ts_dead")
    except ObjectConversionDefect:
      symexTarget("ts")

proc sutTagFree(b: Base9) =
  ## Control: a `Base9` parameter may be any descendant.
  if b == nil: return
  try:
    discard Leaf9(b)
    symexTarget("tf_leaf")
  except ObjectConversionDefect:
    symexTarget("tf_raise")

suite "S8bn (9): a parameter's run-type tags follow its static type":

  test "nim":
    let m = Mid9(x: 1, y: 2)
    sutTagAlias(m, m)
    let s = Side9()
    sutTagSide(s, s)

  test "a parameter aliasing another of a deeper static type":
    ## RED: `ta_dead` / `ts_dead` `sxSat` (false): the tags were free.
    discard clean(sutTagAlias, "ta", sxSat)
    discard clean(sutTagAlias, "ta_dead", sxUnsat)
    discard clean(sutTagSide, "ts", sxSat)
    discard clean(sutTagSide, "ts_dead", sxUnsat)
    discard clean(sutTagFree, "tf_leaf", sxSat)
    discard clean(sutTagFree, "tf_raise", sxSat)

# ---- 6. proc fields and methods ----------------------------------------------
#
# RFC-0005 S8bn item 6. A call through a proc field (`o.f(x)`) and a method
# call declined (S8bh's audit). A proc field is a call through a proc value
# (S8bh's path, `var` effects included); a method call dispatches over the
# overrides on the run-type tag. A target the walk cannot resolve havocs
# what the callee could write: its `var` actuals, the heap and the globals.

proc setBoth6(a, b: var int) =
  b = 2
  a = 1

proc setOne6(a, b: var int) =
  a = 7

type Ops6 = object
  f: proc (a, b: var int) {.nimcall.}
  k: int

type ROps6 = ref object
  f: proc (a, b: var int) {.nimcall.}

proc sutProcField(k: int) =
  let o = Ops6(f: setBoth6, k: k)
  var x = k
  var y = k
  o.f(x, y)
  if x != 1 or y != 2: symexTarget("pf_dead")
  if x == 1 and y == 2 and k == 3: symexTarget("pf")

proc sutProcFieldPick(k: int) =
  var o = Ops6(f: setBoth6)
  if k > 0: o.f = setOne6
  var x = 0
  var y = 0
  o.f(x, y)
  if k > 0 and x != 7: symexTarget("pp_dead")
  if k <= 0 and x != 1: symexTarget("pp2_dead")
  if x == 7: symexTarget("pp")

proc sutProcFieldRef(k: int) =
  ## A proc field of a heap object: the assignments to it are its targets.
  let o = ROps6(f: setBoth6)
  if k > 5: o.f = setOne6
  var x = 0
  var y = 0
  o.f(x, y)
  if k > 5 and x != 7: symexTarget("pr_dead")
  if k <= 5 and (x != 1 or y != 2): symexTarget("pr2_dead")
  if x == 7: symexTarget("pr")

proc sutProcFieldIn(o: ROps6) =
  ## An input's proc field: no assignment the walk sees names its proc.
  if o == nil: return
  var x = 0
  var y = 0
  o.f(x, y)
  if x == 1: symexTarget("pin")

proc sutProcFieldNilRef(k: int) =
  ## A field `new` left nil, never called: the nil code is not dispatched.
  let o = ROps6()
  var x = 0
  var y = 0
  if k > 0: o.f = setBoth6
  if k > 0: o.f(x, y)
  if x == 1 and k <= 0: symexTarget("pn_dead")
  if x == 1: symexTarget("pn")

proc sutProcFieldExpr(k: int) =
  ## In an expression position.
  let o = Ops6(f: setBoth6, k: k)
  var x = k
  var y = k
  o.f(x, y)
  let s = x + y
  if s != 3: symexTarget("pe_dead")

type
  Shape6 = ref object of RootObj
    w: int
  Square6 = ref object of Shape6
  Disc6 = ref object of Shape6

method setM6(o: Shape6; a: var int) {.base.} = a = 5
method setM6(o: Square6; a: var int) = a = 6

proc sutMethod(k: int) =
  let o: Shape6 = Square6()
  var x = k
  o.setM6(x)
  if x != 6: symexTarget("m_dead")
  if x == 6 and k == 2: symexTarget("m")

proc sutMethodParam(o: Shape6; k: int) =
  ## The dynamic type picks the override: a `Disc6` has none of its own.
  if o == nil: return
  var x = k
  o.setM6(x)
  if x == 6: symexTarget("mp6")
  if x == 5: symexTarget("mp5")
  if x != 5 and x != 6: symexTarget("mp_dead")

var gHav: int

proc sutUnknownGlobal(f: proc (a: var int) {.nimcall.}; k: int) =
  ## An unknown target may write any global it can reach.
  gHav = 3
  var x = 0
  f(x)
  if gHav != 3: symexTarget("ug_moved")

suite "S8bn (6): proc fields and methods":

  test "nim":
    var x = 3
    var y = 3
    let o = Ops6(f: setBoth6)
    o.f(x, y)
    check x == 1 and y == 2
    let s: Shape6 = Square6()
    s.setM6(x)
    check x == 6
    let d: Shape6 = Disc6()
    d.setM6(x)
    check x == 5

  test "a call through a proc field":
    ## RED: `sxUnknown` (`feUnsupportedStmtKind`, `o.f`).
    discard clean(sutProcField, "pf", sxSat)
    discard clean(sutProcField, "pf_dead", sxUnsat)
    discard clean(sutProcFieldPick, "pp", sxSat)
    discard clean(sutProcFieldPick, "pp_dead", sxUnsat)
    discard clean(sutProcFieldPick, "pp2_dead", sxUnsat)
    discard clean(sutProcFieldExpr, "pe_dead", sxUnsat)

  test "a proc field of a heap object":
    discard clean(sutProcFieldRef, "pr", sxSat)
    discard clean(sutProcFieldRef, "pr_dead", sxUnsat)
    discard clean(sutProcFieldRef, "pr2_dead", sxUnsat)
    discard clean(sutProcFieldNilRef, "pn", sxSat)
    discard clean(sutProcFieldNilRef, "pn_dead", sxUnsat)

  test "a heap proc field no assignment names declines":
    declines(sutProcFieldIn, "pin", feUnsupportedOp, "no assignment")

  test "a method call dispatches on the run-type tag":
    ## RED: `sxUnknown` (`feUnsupportedOp`, `setM6`).
    discard clean(sutMethod, "m", sxSat)
    discard clean(sutMethod, "m_dead", sxUnsat)
    discard clean(sutMethodParam, "mp6", sxSat)
    discard clean(sutMethodParam, "mp5", sxSat)
    discard clean(sutMethodParam, "mp_dead", sxUnsat)

  test "an unknown target havocs the globals it may write":
    declines(sutUnknownGlobal, "ug_moved", ceClosureUnknownCallee, "`f`")
    ## RED: no candidate -- the global kept its value past the call, and
    ## only the path's taint stood for the havoc.
    let r = runSymex(progOf(sutUnknownGlobal), tLabel("ug_moved"))
    checkpoint $r.status & " " & show(r.errors)
    check r.candidates.len > 0
