## RFC-0005 (soundness channels) slice S8bn -- S8bh's remainder.
##
## Every item is a PRECISION finding S8bh reported and did not fix: a sound
## verdict whose witness did not replay, or a decline (`sxUnknown`) where a
## finite model exists.
##
## Every expectation below is Nim's (the "nim" tests run the same code).
##
## RFC-0005 S8cm: part 5 of 6 of this suite, with
## `tsymex_rfc0005_s8bn_remainder`, `tsymex_rfc0005_s8bn_remainder_b`,
## `tsymex_rfc0005_s8bn_remainder_c`, `tsymex_rfc0005_s8bn_remainder_d`,
## `tsymex_rfc0005_s8bn_remainder_f`. Split so that each part compiles and runs
## in under 60 s on the Windows legs (the whole file took 121 s).

import std/[unittest, strutils, options, macros, tables, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize
import nelli/smt/runtime
import nelli/smt/dsl_parser

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

# ---- 7. the `of` operator and `nil` literals ----------------------------------
#
# RFC-0005 S8bn item 7. `x of T` was unsupported, and a `nil` literal parsed
# only in a comparison and a ref field's constructor value: `let b: Base =
# nil` declined. `of` is a test of the run-type tag (S8bh's per-depth tags,
# `inheritTagKey`); a `nil` literal is the type's nil in every typed position.

type
  Base7 = ref object of RootObj
    x: int
  Mid7 = ref object of Base7
  Leaf7 = ref object of Mid7
  Side7 = ref object of Base7

proc sutOf(b: Base7) =
  if b of Mid7: symexTarget("of_mid")
  elif b of Side7: symexTarget("of_side")
  elif b != nil: symexTarget("of_base")
  else: symexTarget("of_nil")

proc sutOfLocal(k: int) =
  var b: Base7 = Side7(x: k)
  if k > 0: b = Leaf7(x: k)
  if b of Mid7 and k <= 0: symexTarget("ofl_dead")
  if not (b of Mid7) and k > 0: symexTarget("ofl2_dead")
  if not (b of Base7): symexTarget("ofl3_dead")
  if b of Leaf7 and k == 2: symexTarget("ofl")

proc sutOfStatic(m: Mid7) =
  ## Statically true for a non-nil ref of the type or a subtype.
  if m != nil and not (m of Base7): symexTarget("ofs_dead")
  if m != nil and m of Mid7: symexTarget("ofs")

proc takes7(b: Base7): int =
  if b == nil: 0 else: 1

proc sutNil(k: int) =
  let b: Base7 = nil
  var p: ptr int = nil
  var c = Mid7(x: k)
  if k > 0: c = nil
  let n = takes7(nil)
  if b != nil or p != nil or n != 0: symexTarget("nl_dead")
  if k > 0 and c != nil: symexTarget("nl2_dead")
  if c == nil and k == 1: symexTarget("nl")

proc retNil(k: int): Base7 =
  if k > 0: return nil
  Base7(x: k)

proc sutNilRet(k: int) =
  let r = retNil(k)
  if k > 0 and r != nil: symexTarget("nr_dead")
  if r == nil and k == 4: symexTarget("nr")

suite "S8bn (7): the `of` operator and nil literals":

  test "nim":
    check not (Base7(nil) of Mid7)
    let l: Base7 = Leaf7()
    check l of Mid7 and l of Leaf7 and not (l of Side7)
    sutOfLocal(2)
    sutNil(1)

  test "`of` tests the run-type tag":
    ## RED: `sxUnknown` (`of` unsupported).
    discard clean(sutOf, "of_mid", sxSat)
    discard clean(sutOf, "of_side", sxSat)
    discard clean(sutOf, "of_base", sxSat)
    discard clean(sutOf, "of_nil", sxSat)
    discard clean(sutOfLocal, "ofl", sxSat)
    discard clean(sutOfLocal, "ofl_dead", sxUnsat)
    discard clean(sutOfLocal, "ofl2_dead", sxUnsat)
    discard clean(sutOfLocal, "ofl3_dead", sxUnsat)
    discard clean(sutOfStatic, "ofs", sxSat)
    discard clean(sutOfStatic, "ofs_dead", sxUnsat)

  test "a nil literal in every typed position":
    ## RED: `sxUnknown` (the literal did not parse).
    discard clean(sutNil, "nl", sxSat)
    discard clean(sutNil, "nl_dead", sxUnsat)
    discard clean(sutNil, "nl2_dead", sxUnsat)
    discard clean(sutNilRet, "nr", sxSat)
    discard clean(sutNilRet, "nr_dead", sxUnsat)

# ---- 8. generic, inheritable and case-object hierarchies ----------------------
#
# RFC-0005 S8bn item 8. S8bh's shared address space (one `Ref_<root>` sort,
# a field's heap keyed on its declaring type) covered a chain of plain
# objects under `RootObj`. A `{.inheritable.}` root, `of RootRef`, a generic
# hierarchy and one whose root is a case object kept per-type keying: a
# conversion among them was ill-sorted, and two parameters of two static
# types never aliased.

type
  IBase8 {.inheritable.} = ref object
    x: int
  IMid8 = ref object of IBase8
    y: int
  RBase8 = ref object of RootRef
    x: int
  RMid8 = ref object of RBase8
  CKind8 = enum ckA, ckB
  CBase8 = ref object of RootObj
    case k: CKind8
    of ckA: a: int
    of ckB: b: int
  CMid8 = ref object of CBase8
    z: int

proc sutInhAlias(b: IBase8; d: IMid8) =
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2 and IBase8(d) == b: symexTarget("ia")
  if d.x != 2 and IBase8(d) == b: symexTarget("ia_dead")

proc sutRootRefAlias(b: RBase8; d: RMid8) =
  if b == nil or d == nil: return
  d.x = 1
  b.x = 2
  if d.x == 2: symexTarget("ra")
  if d.x != 1 and d.x != 2: symexTarget("ra_dead")

proc sutCaseAlias(b: CBase8; d: CMid8) =
  if b == nil or d == nil: return
  d.z = 1
  if CBase8(d) == b and b.k == ckA:
    b.a = 2
    if d.a == 2: symexTarget("ca")
    if d.a != 2: symexTarget("ca_dead")

proc sutCaseDown(k: int) =
  let b: CBase8 = CMid8(k: ckB, b: k, z: 3)
  let d = CMid8(b)
  if d.z != 3 or d.b != k: symexTarget("cd_dead")
  if d.z == 3 and k == 5: symexTarget("cd")

suite "S8bn (8): generic, inheritable and case-object hierarchies":

  test "nim":
    let d = IMid8()
    sutInhAlias(d, d)
    check d.x == 2
    let c = CMid8(k: ckA)
    sutCaseAlias(c, c)
    check c.a == 2

  test "an inheritable root and `of RootRef`":
    discard clean(sutInhAlias, "ia", sxSat)
    discard clean(sutInhAlias, "ia_dead", sxUnsat)
    discard clean(sutRootRefAlias, "ra", sxSat)
    discard clean(sutRootRefAlias, "ra_dead", sxUnsat)

  test "a hierarchy rooted at a case object":
    discard clean(sutCaseAlias, "ca", sxSat)
    discard clean(sutCaseAlias, "ca_dead", sxUnsat)
    discard clean(sutCaseDown, "cd", sxSat)
    discard clean(sutCaseDown, "cd_dead", sxUnsat)
