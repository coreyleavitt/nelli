## RFC-0016 0.10.0 review, finding H6. Built with `--fieldChecks:off` (its
## `.nim.cfg`): a variant's arm fields are views of one union, and the walker
## reads a field outside the active arm from the union's bytes
## (`variant_layout`). An enum field was sized by the width of its ordinal
## range (`enumOrdBitsNeeded`), but Nim sizes an enum whose first ordinal is
## negative as 4 bytes (`sizealignoffsetimpl`, `tyEnum`), and honours
## `{.size: N.}`. So `ord(o.e)` over the bytes of `b0..b3` read one byte,
## sign-extended: native 255, and the engine proved 255 UNSAT, trusted.
##
## Now an enum's C size is Nim's rule (a negative first ordinal: 4 bytes;
## else by its last ordinal), and a field whose size the compiler
## (`macros.getSize`) gives differently from the layout's (`{.size.}`, a
## `char` range) declines the layout. A 4-byte enum whose ordinal range is
## narrower than 32 bits reads foreign bytes only as a value its own write
## stored (`pkEnumWide`): foreign bytes may be no value of it, so that read
## declines; its own bytes, read through another arm, are exact.
import std/[unittest, strutils, macros]
import nelli
import nelli/symex
import nelli/smt/dsl_typebridge
import nelli/smt/variant_layout
import ./s8cu_helpers

type
  En = enum enM = -1, en0, en1
  Pn = object
    case k: bool
    of false: e: En
    of true: b0, b1, b2, b3: int8
  Es {.size: 4.} = enum es0, es1, es2
  Ps = object
    case k: bool
    of false: e: Es
    of true: b0, b1, b2, b3: int8
  Eb = enum eb0, eb1, eb2
  Pb = object            ## a non-negative enum: one byte, as before
    case k: bool
    of false: e: Eb
    of true: b0, b1: int8
  Pc = object            ## a char range: Nim's size is its base's (1 byte)
    case k: bool
    of false: c: range['a'..'z']
    of true: d: int8

proc innerTypeSym(T: NimNode): NimNode =
  let inst = T.getTypeInst
  if inst.kind == nnkBracketExpr and inst.len == 2 and
     inst[0].kind in {nnkSym, nnkIdent} and inst[0].strVal == "typeDesc":
    inst[1]
  else:
    inst

macro layoutPins(T: typedesc; v: untyped): untyped =
  ## (walker's layout, native layout), as `tsymex_0016_fieldoff` builds it.
  let lay = variantLayout(classifyType(innerTypeSym(T)).ty)
  var nat = newCall(ident"&", newLit("size="),
                    newCall(ident"$", newCall(ident"sizeof", T)))
  for f in layoutFieldNames(lay):
    let off = newCall(ident"-",
      newTree(nnkCast, ident"int", newCall(ident"addr", newDotExpr(v, ident f))),
      newTree(nnkCast, ident"int", newCall(ident"addr", v)))
    nat = newCall(ident"&", nat, newCall(ident"&", newLit(";" & f & "@"),
                                         newCall(ident"$", off)))
  result = newTree(nnkTupleConstr, newLit(layoutDump(lay)), nat)

proc sutReadNeg(x: int8) =
  let o = Pn(k: true, b0: x, b1: 0, b2: 0, b3: 0)
  if ord(o.e) == 255: symexTarget("hit")

proc sutWriteNeg(e: En) =
  let o = Pn(k: false, e: e)
  if o.b1 == -1: symexTarget("hit")

proc sutWriteNegZero(e: En) =
  let o = Pn(k: false, e: e)
  if o.b0 == 1 and o.b1 != 0: symexTarget("hit")

proc sutReadSized(x: int8) =
  let o = Ps(k: true, b0: 0, b1: x, b2: 0, b3: 0)
  if ord(o.e) == 256: symexTarget("hit")

proc sutReadByte(x: int8) =
  let o = Pb(k: true, b0: x, b1: 0)
  if o.e == eb2: symexTarget("hit")

proc nativeReadNeg(x: int8): int =
  let o = Pn(k: true, b0: x, b1: 0, b2: 0, b3: 0)
  ord(o.e)

proc nativeWriteNeg(e: En): int8 =
  let o = Pn(k: false, e: e)
  o.b1

suite "CR-4 H6: an enum's C size in a variant layout is Nim's":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 357

  test "the layout of a negative-ordinal enum arm matches native":
    var n = Pn(k: false, e: en0)
    let p = layoutPins(Pn, n)
    checkpoint "walker " & p[0] & " native " & p[1]
    check p[0] == p[1]
    var b = Pb(k: false, e: eb1)
    let q = layoutPins(Pb, b)
    checkpoint "walker " & q[0] & " native " & q[1]
    check q[0] == q[1]

  test "a {.size.} enum and a char range: the layout declines or matches":
    var s = Ps(k: false, e: es1)
    let p = layoutPins(Ps, s)
    checkpoint "walker " & p[0] & " native " & p[1]
    check p[0] == p[1] or p[0].startsWith("declined")
    var c = Pc(k: false, c: 'b')
    let q = layoutPins(Pc, c)
    checkpoint "walker " & q[0] & " native " & q[1]
    check q[0] == q[1] or q[0].startsWith("declined")

  test "foreign bytes read as a negative-ordinal enum: no trusted UNSAT":
    check nativeReadNeg(-1) == 255   # the native answer
    let r = symexFind(sutReadNeg, tLabel("hit"))
    checkpoint show(r.errors) & " " & $r.status
    check not (r.status == sxUnsat and r.trusted)

  test "foreign bytes read as a {.size: 4.} enum: no trusted UNSAT":
    let o = Ps(k: true, b0: 0, b1: 1, b2: 0, b3: 0)
    check ord(o.e) == 256            # the native answer
    let r = symexFind(sutReadSized, tLabel("hit"))
    checkpoint show(r.errors) & " " & $r.status
    check not (r.status == sxUnsat and r.trusted)

  test "a negative-ordinal enum's own bytes through another arm are exact":
    check nativeWriteNeg(enM) == -1
    check nativeWriteNeg(en1) == 0
    let r = symexFind(sutWriteNeg, tLabel("hit"))
    checkpoint show(r.errors) & " " & $r.status
    check r.status == sxSat
    check r.trusted
    if r.status == sxSat:
      check r.witness[0] == enM
      check nativeWriteNeg(r.witness[0]) == -1
    let r2 = symexFind(sutWriteNegZero, tLabel("hit"))
    checkpoint show(r2.errors) & " " & $r2.status
    check r2.status == sxUnsat
    check r2.trusted

  test "a one-byte enum keeps its exact read":
    let r = symexFind(sutReadByte, tLabel("hit"))
    checkpoint show(r.errors) & " " & $r.status
    check r.status == sxSat
    check r.trusted
    if r.status == sxSat: check r.witness[0] == 2
