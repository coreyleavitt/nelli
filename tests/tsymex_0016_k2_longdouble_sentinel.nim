## RFC-0016 INT-76 / K2: a `c_longdouble` value reaching a node kind
## `isLongDoubleTyped` does not read (its `else` returns false) declines
## downstream and never yields a trusted verdict or a walker fault.
##
## `isLongDoubleTyped` reads a type off symbols only: a symbol, a field, a
## conversion head, a call's callee. A value of the type from another node
## kind (an element, a dereference, a `var` parameter's hidden dereference, an
## `if` expression, a statement-list expression) is left to the
## `__unsupported:c_longdouble` placeholder sort, which has no arithmetic: each
## probe below reaches the target past such a value and must not be trusted.
import std/[unittest, strutils]
import nelli
import nelli/symex
import nelli/smt/errorkind
import ./s8cu_helpers

var gArr: array[2, c_longdouble]
var gTup: (c_longdouble, int)
var gA: c_longdouble
var gB: c_longdouble

proc ldElem(k: int) =
  if gArr[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldTupleIdx(k: int) =
  if gTup[0] == 0.0 and k == 1: symexTarget("hit")

proc ldPtrDeref(p: ptr c_longdouble; k: int) =
  if p[] == 0.0 and k == 1: symexTarget("hit")

proc ldVarParam(p: var c_longdouble; k: int) =
  if p == 0.0 and k == 1: symexTarget("hit")

proc ldSeqElem(s: seq[c_longdouble]; k: int) =
  if s.len > 0 and s[0] == 0.0 and k == 1: symexTarget("hit")

proc ldIfExpr(k: int) =
  if (if k == 2: gA else: gB) == 0.0 and k == 1: symexTarget("hit")

proc ldBlockExpr(k: int) =
  if (block: gA) == 0.0 and k == 1: symexTarget("hit")

proc ldCaseExpr(k: int) =
  let v = case k
    of 2: gA
    else: gB
  if v == 0.0 and k == 1: symexTarget("hit")

proc ldCast(k: int) =
  if cast[c_longdouble](float64(k)) == 0.0 and k == 1: symexTarget("hit")

proc ldToFloat(k: int) =
  let f: float = gA
  if f == 0.0 and k == 1: symexTarget("hit")

proc judge[T](res: SymexResult[T]; what: string) =
  checkpoint("c_longdouble sentinel " & what)
  check not res.trusted
  for e in res.errors:
    check e.kind != weInternalWalkerFault

suite "K2: the walker's version":
  test "version floor: the sentinel fix bumped the walker to 460":
    check parseInt(symexWalkerVersion) >= 460

suite "K2: a c_longdouble value from a node kind the type probe skips declines":
  test "an array element":
    judge(symexFind(ldElem, tLabel("hit"), pinSettingsConst), "array element")
  test "a tuple field by index":
    judge(symexFind(ldTupleIdx, tLabel("hit"), pinSettingsConst), "tuple index")
  test "a pointer dereference":
    judge(symexFind(ldPtrDeref, tLabel("hit"), pinSettingsConst), "deref")
  test "a var parameter":
    judge(symexFind(ldVarParam, tLabel("hit"), pinSettingsConst), "var param")
  test "a seq element":
    judge(symexFind(ldSeqElem, tLabel("hit"), pinSettingsConst), "seq element")
  test "an if expression":
    judge(symexFind(ldIfExpr, tLabel("hit"), pinSettingsConst), "if expr")
  test "a block expression":
    judge(symexFind(ldBlockExpr, tLabel("hit"), pinSettingsConst), "block expr")
  test "a case expression":
    judge(symexFind(ldCaseExpr, tLabel("hit"), pinSettingsConst), "case expr")
  test "a cast":
    judge(symexFind(ldCast, tLabel("hit"), pinSettingsConst), "cast")
  test "a value stored into a float":
    judge(symexFind(ldToFloat, tLabel("hit"), pinSettingsConst), "to float")
