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
##
## int6: an element or dereference whose container is not a symbol (an `if`,
## `block`, `case` or statement-list expression, a named container type, a
## field) was read as no `c_longdouble` and reached `weInternalWalkerFault`
## (probed before the fix: ten of the fourteen shapes below). Each now declines
## with the parameter-type kind the declared sites use.
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

# --- a container whose root is not a symbol (int6) --------------------------

type
  LdPair = array[2, c_longdouble]
  LdBox = object
    xs: array[2, c_longdouble]
  LdHolder = object
    p: LdPair

var gArr2: array[2, c_longdouble]
var gNamed: LdPair
var gBox: LdBox
var gHolder: LdHolder

proc mkArr(): array[2, c_longdouble] = gArr
proc mkTup(): (c_longdouble, int) = gTup
proc mkPtr(): ptr c_longdouble = addr gA
proc mkNamed(): LdPair = gNamed
proc mkBox(): LdBox = gBox

proc ldIfRoot(k: int) =
  if (if k == 2: gArr else: gArr2)[k and 1] == 0.0 and k == 1:
    symexTarget("hit")

proc ldBlockRoot(k: int) =
  if (block: gArr)[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldCaseRoot(k: int) =
  if (case k
      of 2: gArr
      else: gArr2)[k and 1] == 0.0 and k == 1:
    symexTarget("hit")

proc ldStmtListRoot(k: int) =
  if (discard k; gArr)[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldIfDeref(k: int) =
  if (if k == 2: addr gA else: addr gB)[] == 0.0 and k == 1:
    symexTarget("hit")

proc ldCallRoot(k: int) =
  if mkArr()[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldCallTupRoot(k: int) =
  if mkTup()[0] == 0.0 and k == 1: symexTarget("hit")

proc ldCallDeref(k: int) =
  if mkPtr()[] == 0.0 and k == 1: symexTarget("hit")

proc ldNamedRoot(k: int) =
  if gNamed[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldNamedCallRoot(k: int) =
  if mkNamed()[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldFieldRoot(k: int) =
  if gBox.xs[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldCallFieldRoot(k: int) =
  if mkBox().xs[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldNamedFieldRoot(k: int) =
  if gHolder.p[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc ldClosureRoot(k: int) =
  let f = mkArr
  if f()[k and 1] == 0.0 and k == 1: symexTarget("hit")

proc judge[T](res: SymexResult[T]; what: string) =
  checkpoint("c_longdouble sentinel " & what)
  check not res.trusted
  for e in res.errors:
    check e.kind != weInternalWalkerFault

proc judgeKind[T](res: SymexResult[T]; what: string) =
  ## int6: the decline is the c_longdouble one (`declineLongDouble`,
  ## `feUnsupportedParamType`), not another that happened to fire first
  judge(res, what)
  checkpoint show(res.errors)
  check named(res.errors, feUnsupportedParamType)

suite "K2: the walker's version":
  test "version floor: int6's container probe bumped the walker to 463":
    check parseInt(symexWalkerVersion) >= 463
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

suite "K2 int6: a container whose root is no symbol declines":
  test "an if expression's element":
    judgeKind(symexFind(ldIfRoot, tLabel("hit"), pinSettingsConst), "if root")
  test "a block expression's element":
    judgeKind(symexFind(ldBlockRoot, tLabel("hit"), pinSettingsConst), "block root")
  test "a case expression's element":
    judgeKind(symexFind(ldCaseRoot, tLabel("hit"), pinSettingsConst), "case root")
  test "a statement-list expression's element":
    judgeKind(symexFind(ldStmtListRoot, tLabel("hit"), pinSettingsConst), "stmtlist root")
  test "an if expression dereferenced":
    judgeKind(symexFind(ldIfDeref, tLabel("hit"), pinSettingsConst), "if deref")
  test "a call's element":
    judgeKind(symexFind(ldCallRoot, tLabel("hit"), pinSettingsConst), "call root")
  test "a call's tuple slot":
    judgeKind(symexFind(ldCallTupRoot, tLabel("hit"), pinSettingsConst), "call tuple")
  test "a call's dereference":
    judgeKind(symexFind(ldCallDeref, tLabel("hit"), pinSettingsConst), "call deref")
  test "a named container type's element":
    judgeKind(symexFind(ldNamedRoot, tLabel("hit"), pinSettingsConst), "named root")
  test "a call returning a named container type":
    judgeKind(symexFind(ldNamedCallRoot, tLabel("hit"), pinSettingsConst), "named call")
  test "a field's element":
    judgeKind(symexFind(ldFieldRoot, tLabel("hit"), pinSettingsConst), "field root")
  test "a call's field's element":
    judgeKind(symexFind(ldCallFieldRoot, tLabel("hit"), pinSettingsConst), "call field")
  test "a named-type field's element":
    judgeKind(symexFind(ldNamedFieldRoot, tLabel("hit"), pinSettingsConst), "named field")
  test "a closure call's element":
    judge(symexFind(ldClosureRoot, tLabel("hit"), pinSettingsConst), "closure root")
