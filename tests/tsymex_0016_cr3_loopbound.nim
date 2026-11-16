## RFC-0016 code review (0.10.0), finding H4: a `..` / `..<` / `countup` /
## `countdown` bound read the way Nim's inliner reads it.
##
## These iterators are inline: `transf.transformFor` maps each argument to its
## formal by `putArgInto`. A symbol, a field path (`o.n`, `r.n`, `p[]`), a
## `var` formal (`nnkHiddenDeref`) and a conversion between types equal up to
## range and distinctness are substituted for the formal, so the bound is read
## on every iteration and a body that writes it moves it. `s[k]` is bound
## through its address, taken once: the element is re-read, the index is not.
## Anything else (a call, an arithmetic expression, a widening conversion, a
## variant-object field, `nnkCheckedFieldExpr`) is copied to a temporary once.
##
## Before the fix the P17 guard copied every non-symbol bound: a field path or
## a `var` formal written by the body kept its first value, a trusted wrong
## trip count. Where the address Nim keeps is not stable across the body (a
## seq the body may resize, an index the body moves while it also writes the
## container) the loop declines.
import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/symex
import nelli/smt/admission
import ./s8cu_helpers

type
  O = object
    n: int
    u: uint
  R = ref object
    n: int
  ON = object
    n: Natural
  O32 = object
    n: int32
  K = enum kA, kB
  V = object
    case k: K
    of kA: n: int
    of kB: b: int

proc gVar(n: var int): int =
  for i in 0 ..< n:
    n = 0
    inc result

proc gVarUp(n: var int): int =
  for i in countup(0, n):
    n = 0
    inc result

proc hVarParam(a: int) =
  var n = 5
  if gVar(n) == 1 and a == 1: symexTarget("hit")

proc hVarParamUp(a: int) =
  var n = 3
  if gVarUp(n) == 1 and a == 1: symexTarget("hit")

proc hField(a: int) =
  var o = O(n: 5)
  var c = 0
  for i in 0 ..< o.n:
    o.n = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hFieldUp(a: int) =
  var o = O(n: 3)
  var c = 0
  for i in countup(0, o.n):
    o.n = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")
  if c == 4 and a == 1: symexTarget("four")

proc hFieldDownU(a: int) =
  # `countdown` over `uint` reads `b` again in its `if res == b: break`.
  var o = O(u: 0)
  var c = 0
  for i in countdown(5'u, o.u):
    o.u = 4
    inc c
  if c == 2 and a == 1: symexTarget("hit")

proc hRefField(a: int) =
  var r = R(n: 5)
  var c = 0
  for i in 0 .. r.n:
    r.n = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hDeref(a: int) =
  var x = 5
  let p = addr x
  var c = 0
  for i in 0 ..< p[]:
    x = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hNatural(a: int) =
  # `m` is converted `Natural -> int` (`nnkHiddenStdConv`), equal up to range:
  # substituted, so re-read.
  var m: Natural = 5
  var c = 0
  for i in 0 ..< m:
    m = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hNaturalField(a: int) =
  # The same through a `Natural` field. The walk declines its assignment
  # `o.n = 0` (`feUnsupportedStmtKind`), loop or no loop: an assignment to a
  # subrange-typed field is not lowered, before and after this fix.
  var o = ON(n: 5)
  var c = 0
  for i in 0 ..< o.n:
    o.n = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hWiden(a: int) =
  # int32 -> int64 is not the same type: copied once.
  var o = O32(n: 3)
  var c = 0
  for i in 0'i64 ..< o.n:
    o.n = 0
    inc c
  if c == 3 and a == 1: symexTarget("hit")

proc hVariant(a: int) =
  # a variant field is `nnkCheckedFieldExpr`: copied once.
  var o = V(k: kA, n: 3)
  var c = 0
  for i in 0 ..< o.n:
    o.n = 0
    inc c
  if c == 3 and a == 1: symexTarget("hit")

proc hArr(a: int) =
  var arr = [5, 7]
  var c = 0
  for i in 0 ..< arr[0]:
    arr[0] = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hArrIdxMoved(a: int) =
  # the index is read once (the address is), and the array is not written.
  var arr = [3, 1]
  var k = 0
  var c = 0
  for i in 0 ..< arr[k]:
    k = 1
    inc c
  if c == 3 and a == 1: symexTarget("hit")

proc hSeq(a: int) =
  var s = @[5, 7]
  var c = 0
  for i in 0 ..< s[0]:
    s[0] = 0
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hArrBothMoved(a: int) =
  var arr = [5, 1]
  var k = 0
  var c = 0
  for i in 0 ..< arr[k]:
    arr[0] = 0
    k = 1
    inc c
  if c == 1 and a == 1: symexTarget("hit")

proc hSeqGrow(a: int) =
  var s = @[5]
  var c = 0
  for i in 0 ..< s[0]:
    s.add 0
    inc c
    if c >= 3: break
  if c == 3 and a == 1: symexTarget("hit")

proc hCallOnce(a: int) =
  # precision: a call is copied once, unchanged by the fix.
  var o = O(n: 3)
  var c = 0
  for i in 0 ..< o.n + 0:
    o.n = 0
    inc c
  if c == 3 and a == 1: symexTarget("hit")

suite "CR3 H4: the walker version":
  test "floor":
    check parseInt(symexWalkerVersion) >= 356

const rr = cellKey(axConstruct, "for/dotdot/boundReread")
const dd = cellKey(axConstruct, "for/dotdot/boundOnce")
const un = cellKey(axConstruct, "for/dotdot/boundUnstable")

suite "CR3 H4: a bound Nim substitutes is re-read":
  test "var formal, ..<": discard pinExact(hVarParam, rr)
  test "var formal, countup": discard pinExact(hVarParamUp, rr)
  test "field, ..<": discard pinExact(hField, rr)
  test "field, countup: c == 1":
    discard pinExact(hFieldUp, rr)
  test "field, countup: c == 4 is unreachable":
    discard pinExact(hFieldUp, rr, target = tLabel("four"))
  test "field, uint countdown (its stop test reads b)":
    discard pinExact(hFieldDownU, rr)
  test "ref field": discard pinExact(hRefField, rr)
  test "p[] stays modelled": discard pinExact(hDeref, rr)
  test "Natural variable (a same-type conversion)": discard pinExact(hNatural, rr)
  test "Natural field: its assignment is declined, never decided wrong":
    let r = symexFind(hNaturalField, tLabel("hit"))
    var msgs = ""
    for e in r.errors: msgs.add $e.kind & ": " & e.msg & "\n"
    checkpoint $r.status & "\n" & msgs
    check r.status == sxUnknown
    check "feUnsupportedStmtKind" in msgs
  test "array element": discard pinExact(hArr, rr)
  test "seq element, body writes only elements": discard pinExact(hSeq, rr)

suite "CR3 H4: a bound Nim copies is read once":
  test "widening conversion": discard pinExact(hWiden, dd)
  test "variant field": discard pinExact(hVariant, dd)
  test "index moved, array unwritten": discard pinExact(hArrIdxMoved, dd)
  test "arithmetic": discard pinExact(hCallOnce, dd)

suite "CR3 H4: an address the body may move declines":
  test "index and array both written":
    pinDecline(hArrBothMoved, un, feUnsupportedOp, needle = "bound")
  test "seq the body may resize":
    pinDecline(hSeqGrow, un, feUnsupportedOp, needle = "bound")
