## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 6 of 6 of this suite, with
## `tsymex_rfc0005_s8bn_remainder`, `tsymex_rfc0005_s8bn_remainder_b`,
## `tsymex_rfc0005_s8bn_remainder_c`, `tsymex_rfc0005_s8bn_remainder_d`,
## `tsymex_rfc0005_s8bn_remainder_e`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 121 s).

import std/[unittest, strutils, options, macros, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser
import s8ct_platform   ## RFC-0005 S8ct

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

template confirmed(fn: typed, lbl: string): untyped =
  ## A sound `sxSat` whose witness replays `roConfirmed` against Nim.
  block:
    let r = clean(fn, lbl, sxSat)
    if r.status == sxSat:
      checkpoint $r.heapSnapshot
      check replayedOrNotMarshallable(replayWitness(fn, r.witness, tLabel(lbl), {}), roConfirmed)

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

type Ops6 = object
  f: proc (a, b: var int) {.nimcall.}
  k: int

type ROps6 = ref object
  f: proc (a, b: var int) {.nimcall.}

# ---- 8b. generic hierarchies ----------------------------------------------------
#
# RFC-0005 S8bn item 8. A generic object type was not classified at all
# (`G[int]`, by value or by ref, was `feUnsupportedParamType`), so a generic
# hierarchy had no address space to join. An instance is now classified
# with its arguments substituted into the body, keyed on the instance, and a
# generic parent (`of GBase8[T]`) joins the chain as a plain parent does.

type
  GBase8[T] = ref object of RootObj
    x: T
  GMid8[T] = ref object of GBase8[T]
    y: T
  GPair8[A, B] = object
    a: A
    b: seq[B]
  GNode8[T] = ref object
    v: T
    next: GNode8[T]

proc sutGenAlias(b: GBase8[int]; d: GMid8[int]) =
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2 and GBase8[int](d) == b: symexTarget("ga")
  if d.x != 2 and GBase8[int](d) == b: symexTarget("ga_dead")

proc sutGenDown(k: int) =
  let b: GBase8[int] = GMid8[int](x: k, y: 4)
  let d = GMid8[int](b)
  if d.y != 4: symexTarget("gd_dead")
  if d.x == 3: symexTarget("gd")
  try:
    discard GMid8[int](GBase8[int](x: 1))
    symexTarget("gd2_dead")
  except ObjectConversionDefect:
    discard

proc sutGenValue(p: GPair8[int, int]) =
  if p.a == 5 and p.b.len == 1 and p.b[0] == 2: symexTarget("gv")

proc sutGenList(n: GNode8[int]) =
  if n != nil and n.next != nil and n.next.v == 4: symexTarget("gl")

suite "S8bn (8b): generic hierarchies":

  test "nim":
    let g = GMid8[int]()
    sutGenAlias(g, g)
    check g.x == 2
    expect ObjectConversionDefect:
      discard GMid8[int](GBase8[int](x: 1))

  test "a generic hierarchy shares one address space":
    ## RED: sxUnknown, `feUnsupportedParamType` "GBase8[int]".
    confirmed(sutGenAlias, "ga")
    discard clean(sutGenAlias, "ga_dead", sxUnsat)
    discard clean(sutGenDown, "gd", sxSat)
    discard clean(sutGenDown, "gd_dead", sxUnsat)
    discard clean(sutGenDown, "gd2_dead", sxUnsat)

  test "a generic object, by value and recursive":
    ## RED: sxUnknown, `feUnsupportedParamType`.
    confirmed(sutGenValue, "gv")
    confirmed(sutGenList, "gl")

suite "S8bn: walker version":

  test "the walker version is at least S8bn's":
    check parseInt(symexWalkerVersion) >= 215
