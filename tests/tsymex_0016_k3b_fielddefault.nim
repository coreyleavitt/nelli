## RFC-0016 K3b -- object field defaults exact, and `wasMoved` stays bitwise
## zero.
##
## Natively `default(T)`, `T()`, an omitted constructor field and `new` apply a
## field's `= default`; `var o: T`, a `result`, an aggregate's zero fields,
## `wasMoved`, `reset` and `move` leave the BITWISE ZERO. The walker agreed in
## every shape since W1-f, with no table behind it: the zero side was
## `zeroValueForType`'s own `case`. K3b makes that `case` read the type x
## memory-op axis (`typeop:fieldDefault/<IR kind>`): the row says how a value
## of the kind is zeroed, and a kind with no model declines.
import std/[unittest, strutils, options, tables, sets]
import nelli
import nelli/symex
import nelli/smt/admission
import nelli/smt/errorkind
import nelli/smt/types
import nelli/smt/typeaxes
import nelli/smt/canonicalize
import ./s8cu_helpers

type
  W = object
    x: int = 5
    f: float = 2.5
    s: seq[int] = @[1, 2]
    str: string = "ab"
    t: (int, int) = (1, 2)

proc wmInt(k: int) =
  var o = W()
  wasMoved(o)
  if o.x == 0: symexTarget("h")
proc wmIntKeepsDefault(k: int) =
  var o = W()
  wasMoved(o)
  if o.x == 5: symexTarget("h")
proc wmFloat(k: int) =
  var o = W()
  wasMoved(o)
  if o.f == 0.0: symexTarget("h")
proc wmSeq(k: int) =
  var o = W()
  wasMoved(o)
  if o.s.len == 0: symexTarget("h")
proc wmString(k: int) =
  var o = W()
  wasMoved(o)
  if o.str.len == 0: symexTarget("h")
proc wmTuple(k: int) =
  var o = W()
  wasMoved(o)
  if o.t[0] == 0: symexTarget("h")
proc resetInt(k: int) =
  var o = W()
  reset(o)
  if o.x == 0: symexTarget("h")
proc moveInt(k: int) =
  var o = W()
  let p = move(o)
  if o.x == 0 and p.x == 5: symexTarget("h")

const dom = sampled([-1, 0, 1])

suite "RFC-0016 K3b: the field-default row":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 291

  test "every IRTypeKind has a fieldDefault row":
    for k in IRTypeKind:
      let a = admitTypeOp(k, moFieldDefault, toZeroValue)
      check a.cell.scope == axTypeOp
      check render(a.cell) == "typeop:fieldDefault/" & irKey(k)
      if not a.admitted:
        check "no row" notin a.decline[1]

  test "an uninterpreted sort has no zero: a refused iModel row":
    let a = admitTypeOp(itUninterp, moFieldDefault, toZeroValue)
    check not a.admitted
    check "typeop:fieldDefault/uninterp" in a.decline[1]

  test "the row says how the kind is zeroed":
    check admitTypeOp(itInt, moFieldDefault, toZeroValue).payload.zero == zmLiteral
    check admitTypeOp(itString, moFieldDefault, toZeroValue).payload.zero == zmLiteral
    check admitTypeOp(itRef, moFieldDefault, toZeroValue).payload.zero == zmLiteral
    check admitTypeOp(itSeq, moFieldDefault, toZeroValue).payload.zero == zmZeroValue
    check admitTypeOp(itTuple, moFieldDefault, toZeroValue).payload.zero == zmZeroValue
    check admitTypeOp(itDistinct, moFieldDefault, toZeroValue).payload.zero == zmBase

  test "the letCursor rows are untouched by the new payload":
    check admitTypeOp(itSeq, moLetCursor).payload.share == msShared
    check admitTypeOp(itInt, moLetCursor).payload.share == msValue

suite "RFC-0016 K3b: wasMoved, reset and move leave the bitwise zero":
  test "native: the zero, not the default":
    check "h" in nativeRun(wmInt(0)).hits
    check "h" notin nativeRun(wmIntKeepsDefault(0)).hits
    check "h" in nativeRun(wmFloat(0)).hits
    check "h" in nativeRun(wmSeq(0)).hits
    check "h" in nativeRun(wmString(0)).hits
    check "h" in nativeRun(wmTuple(0)).hits
    check "h" in nativeRun(resetInt(0)).hits
    check "h" in nativeRun(moveInt(0)).hits

  test "wasMoved zeroes every field kind (sat)":
    template sat(fn, nm: untyped) =
      check pinExact(fn, cellKey(axTypeOp, "fieldDefault/" & nm),
                     target = tLabel("h"), domain = dom).status == sxSat
    sat(wmInt, "int")
    sat(wmFloat, "float64")
    sat(wmSeq, "seq")
    sat(wmString, "string")
    sat(wmTuple, "tuple")
    sat(resetInt, "int")
    sat(moveInt, "int")

  test "wasMoved does not restore the default (unsat)":
    check pinExact(wmIntKeepsDefault, cellKey(axTypeOp, "fieldDefault/int"),
                   target = tLabel("h"), domain = dom).status == sxUnsat

proc topSeq(k: int) =
  var s: seq[int]
  if s.len == 0: symexTarget("h")
proc topSeqNonEmpty(k: int) =
  var s: seq[int]
  if s.len > 0: symexTarget("h")
proc topString(k: int) =
  var s: string
  if s.len == 0: symexTarget("h")
proc topStringNonEmpty(k: int) =
  var s: string
  if s.len > 0: symexTarget("h")

suite "RFC-0016 K3b: zeroValueForType reads the row (an uninitialised var)":
  test "a seq and a string start empty":
    check "h" in nativeRun(topSeq(0)).hits
    check "h" notin nativeRun(topSeqNonEmpty(0)).hits
    check pinExact(topSeq, cellKey(axTypeOp, "fieldDefault/seq"),
                   target = tLabel("h"), domain = dom).status == sxSat
    check pinExact(topSeqNonEmpty, cellKey(axTypeOp, "fieldDefault/seq"),
                   target = tLabel("h"), domain = dom).status == sxUnsat
    check pinExact(topString, cellKey(axTypeOp, "fieldDefault/string"),
                   target = tLabel("h"), domain = dom).status == sxSat
    check pinExact(topStringNonEmpty, cellKey(axTypeOp, "fieldDefault/string"),
                   target = tLabel("h"), domain = dom).status == sxUnsat

# Every other modelled kind's row, reached through an uninitialised `var`: the
# row says how the kind is zeroed, and each pin below is that zero observed
# natively and by the walker. `itUninterp` is the one refused row.
type
  Meters = distinct int
  VK = enum vkA, vkB
  Var1 = object
    n: int
    case k: VK
    of vkA: a: int
    of vkB: b: bool
  Multi = object
    case p: bool
    of true: pa: int
    of false: pb: bool
    case q: VK
    of vkA: qa: int
    of vkB: discard

proc zBool(k: int) =
  var b: bool
  if not b: symexTarget("h")
proc zBoolSet(k: int) =
  var b: bool
  if b: symexTarget("h")
proc zFloat32(k: int) =
  var f: float32
  if f == 0.0'f32: symexTarget("h")
proc zFloat32Non(k: int) =
  var f: float32
  if f != 0.0'f32: symexTarget("h")
proc zArray(k: int) =
  var a: array[3, int]
  if a[1] == 0: symexTarget("h")
proc zArrayNon(k: int) =
  var a: array[3, int]
  if a[1] != 0: symexTarget("h")
proc zBitSet(k: int) =
  var s: set[char]
  if 'a' notin s: symexTarget("h")
proc zBitSetNon(k: int) =
  var s: set[char]
  if 'a' in s: symexTarget("h")
proc zSet(k: int) =
  var s: HashSet[int]
  if s.len == 0: symexTarget("h")
proc zSetNon(k: int) =
  var s: HashSet[int]
  if s.len > 0: symexTarget("h")
proc zTable(k: int) =
  var t: Table[int, int]
  if t.len == 0: symexTarget("h")
proc zTableNon(k: int) =
  var t: Table[int, int]
  if t.len > 0: symexTarget("h")
proc zRef(k: int) =
  var p: ref int
  if p == nil: symexTarget("h")
proc zRefNon(k: int) =
  var p: ref int
  if p != nil: symexTarget("h")
proc zPtr(k: int) =
  var p: ptr int
  if p == nil: symexTarget("h")
proc zPtrNon(k: int) =
  var p: ptr int
  if p != nil: symexTarget("h")
proc zDistinct(k: int) =
  var m: Meters
  if int(m) == 0: symexTarget("h")
proc zDistinctNon(k: int) =
  var m: Meters
  if int(m) != 0: symexTarget("h")
proc zVariant(k: int) =
  var v: Var1
  if v.k == vkA and v.a == 0 and v.n == 0: symexTarget("h")
proc zVariantNon(k: int) =
  var v: Var1
  if v.k != vkA or v.a != 0 or v.n != 0: symexTarget("h")
proc zMulti(k: int) =
  var m: Multi
  if m.p == false and m.pb == false and m.q == vkA and m.qa == 0:
    symexTarget("h")
proc zMultiNon(k: int) =
  var m: Multi
  if m.p or m.pb or m.q != vkA or m.qa != 0: symexTarget("h")
proc zClosure(k: int) =
  var f: proc (x: int): int
  if f == nil: symexTarget("h")

suite "RFC-0016 K3b: each modelled kind's zero, and the refused row":
  test "an uninitialised var is its kind's zero (native)":
    for (fn, want) in [(nativeRun(zBool(0)), true), (nativeRun(zBoolSet(0)), false),
                       (nativeRun(zFloat32(0)), true), (nativeRun(zFloat32Non(0)), false),
                       (nativeRun(zArray(0)), true), (nativeRun(zArrayNon(0)), false),
                       (nativeRun(zBitSet(0)), true), (nativeRun(zBitSetNon(0)), false),
                       (nativeRun(zSet(0)), true), (nativeRun(zSetNon(0)), false),
                       (nativeRun(zTable(0)), true), (nativeRun(zTableNon(0)), false),
                       (nativeRun(zRef(0)), true), (nativeRun(zRefNon(0)), false),
                       (nativeRun(zPtr(0)), true), (nativeRun(zPtrNon(0)), false),
                       (nativeRun(zDistinct(0)), true), (nativeRun(zDistinctNon(0)), false),
                       (nativeRun(zVariant(0)), true), (nativeRun(zVariantNon(0)), false),
                       (nativeRun(zMulti(0)), true), (nativeRun(zMultiNon(0)), false)]:
      check ("h" in fn.hits) == want

  test "the zero of each modelled kind (sat, and its negation unsat)":
    template both(pos, neg: untyped; kind: string) =
      check pinExact(pos, cellKey(axTypeOp, "fieldDefault/" & kind),
                     target = tLabel("h"), domain = dom).status == sxSat
      check pinExact(neg, cellKey(axTypeOp, "fieldDefault/" & kind),
                     target = tLabel("h"), domain = dom).status == sxUnsat
    both(zBool, zBoolSet, "bool")
    both(zFloat32, zFloat32Non, "float32")
    both(zArray, zArrayNon, "array")
    both(zBitSet, zBitSetNon, "bitSet")
    both(zSet, zSetNon, "set")
    both(zTable, zTableNon, "table")
    both(zRef, zRefNon, "ref")
    both(zPtr, zPtrNon, "ptr")
    both(zDistinct, zDistinctNon, "distinct")
    both(zVariant, zVariantNon, "variant")
    both(zMulti, zMultiNon, "multiVariant")

  test "a placeholder sort has no zero: a pinned decline":
    pinDecline(zClosure, cellKey(axTypeOp, "fieldDefault/uninterp"),
               ceUnsupportedHof)
