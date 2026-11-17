## RFC-0016 S8cp-r, PRC-34 (S8cp item 7): shapes that declined.
##
##   * `==` on two tuples or two plain objects whose fields are all builtin
##     atoms (integers, `bool`, `char`, floats, `string`): system's generic
##     `==` compares field by field, which the walker now lowers to the
##     conjunction of the fields' own `==` (was `eqBV` on a tuple, declined).
##     A field whose `==` may be a user's (a `distinct`, an enum, a nested
##     record) keeps the decline: system's `==` reaches it through `mixin`;
##   * a `type` section in a routine body declares, and runs nothing (was
##     `feUnsupportedStmtKind`);
##   * the shapes S8cp listed that later slices modelled, each pinned with its
##     native run: a `let b = addr o.y` alias across a whole assignment, a
##     parameter pragma `x {.inject.}: int`, a nested `addr t[1][0]`, and
##     `s[1].b = 7`.
## Each symbolic pin has the compiled program's run beside it.
import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize
import ./s8cu_helpers

type
  Obj = object
    x, y: int
  Mixed = object
    a: int8
    b: uint16
    c: bool
    d: char
    e: float
    s: string
  Meters = distinct int
  WithDistinct = object
    m: Meters
    k: int
  Inner = object
    v: int
  Outer = object
    i: Inner
  Pt = object
    b: int

proc `==`(a, b: Meters): bool = int(a) div 10 == int(b) div 10

proc tupEq(a, b: int) =
  let t = (a, b)
  let u = (b, 3)
  if t == u: symexTarget("hit")

proc tupNe(a, b: int) =
  if (a, b) != (3, 4): discard
  else: symexTarget("hit")

proc tupEqDead(a: int) =
  if (a, a) == (5, 6): symexTarget("hit")

proc objEq(a, b: int) =
  if Obj(x: a, y: 1) == Obj(x: 2, y: b): symexTarget("hit")

proc mixedEq(a: int8; c: char; s: string) =
  let l = Mixed(a: a, b: 7, c: true, d: c, e: 0.5, s: s)
  let r = Mixed(a: -3, b: 7, c: true, d: 'q', e: 0.5, s: "ab")
  if l == r: symexTarget("hit")

proc nanEq(f: float) =
  if (f, 1) == (f, 1): discard
  else: symexTarget("hit")

proc distinctField(a, b: int) =
  # The user's `==` on `Meters` makes 12 and 15 equal; system's `==` on the
  # object reaches it, so the field-by-field model must not decide this.
  let l = WithDistinct(m: Meters(a), k: 0)
  let r = WithDistinct(m: Meters(b), k: 0)
  if l == r and a != b: symexTarget("hit")

proc nestedRecord(a: int) =
  if Outer(i: Inner(v: a)) == Outer(i: Inner(v: 4)): symexTarget("hit")

proc typeSection(v: int) =
  type L = object
    a: int
  var l = L(a: v)
  if l.a == 5: symexTarget("hit")

proc typeSectionDead(v: int) =
  type L = object
    a: int
  var l = L(a: v)
  if l.a == 5 and v != 5: symexTarget("hit")

proc aliasWhole(v: int) =
  var o = Obj(x: 1, y: 2)
  let b = addr o.y
  o = Obj(x: 0, y: v)
  if b[] == 7: symexTarget("hit")

proc injectParam(x {.inject.}: int) =
  if x == 5: symexTarget("hit")

proc nestedAddr(v: int) =
  var t = [[0, 0], [0, 0]]
  let p = addr t[1][0]
  p[] = v
  if t[1][0] == 7: symexTarget("hit")

proc seqFieldWrite(v: int) =
  var s = @[Pt(b: 0), Pt(b: 0)]
  s[1].b = 7
  if s[1].b == v: symexTarget("hit")

suite "RFC-0016 PRC-34: record ==":
  test "native":
    check native(tupEq(3, 3)) == "hit"
    check native(tupEq(3, 4)) == "ran"
    for v in [low(int), 5, 6, high(int)]:
      check native(tupEqDead(v)) == "ran"
    check native(tupNe(3, 4)) == "hit"
    check native(objEq(2, 1)) == "hit"
    check native(mixedEq(-3, 'q', "ab")) == "hit"
    check native(mixedEq(-3, 'q', "abc")) == "ran"
    check native(nanEq(NaN)) == "hit"
    check native(nanEq(1.0)) == "ran"
    check native(distinctField(12, 15)) == "hit"
    check native(nestedRecord(4)) == "hit"
  test "a tuple: reached":
    decides(tupEq, sxSat)
  test "a tuple, `!=`: reached":
    decides(tupNe, sxSat)
  test "a tuple: unreachable":
    decides(tupEqDead, sxUnsat)
  test "a plain object: reached":
    decides(objEq, sxSat)
  test "every atom kind: reached":
    decides(mixedEq, sxSat)
  test "a NaN field: unequal to itself":
    decides(nanEq, sxSat)
  test "a field with a user `==` still declines":
    let r = symexFind(distinctField, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown
    check r.errors.named(feUnsupportedOp)
  test "a nested record still declines":
    let r = symexFind(nestedRecord, tLabel("hit"))
    checkpoint show(r.errors)
    check r.status == sxUnknown

suite "RFC-0016 PRC-34: a type section in a routine body":
  test "native":
    check native(typeSection(5)) == "hit"
    check native(typeSectionDead(5)) == "ran"
  test "reached":
    decides(typeSection, sxSat)
  test "unreachable":
    decides(typeSectionDead, sxUnsat)

suite "RFC-0016 PRC-34: shapes later slices modelled":
  test "native":
    check native(aliasWhole(7)) == "hit"
    check native(injectParam(5)) == "hit"
    check native(nestedAddr(7)) == "hit"
    check native(seqFieldWrite(7)) == "hit"
  test "an alias across a whole assignment":
    decides(aliasWhole, sxSat)
  test "a parameter pragma":
    decides(injectParam, sxSat)
  test "a nested address":
    decides(nestedAddr, sxSat)
  test "a field write through a seq element":
    decides(seqFieldWrite, sxSat)

suite "RFC-0016 S8cp-r: walker version":
  test "symexWalkerVersion is at least 391":
    check parseInt(symexWalkerVersion) >= 391
