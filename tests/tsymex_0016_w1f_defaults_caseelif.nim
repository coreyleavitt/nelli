## RFC-0016 W1-f -- object field defaults agree with the native run (W-20; the
## decline the slice planned is not needed, see the suite note), and
## `case` takes `elif` arms in all three forms (W-21), checked against the
## native run.
import std/[unittest, strutils, sequtils]
import nelli
import nelli/symex
import ./s8cu_helpers

# --- field defaults ----------------------------------------------------------

type
  O = object
    x: int = 5
  P = object                # a defaulted field and a plain one
    a: int
    b: int = 7
  Q = ref object
    x: int = 5
  Wrap = object             # holds an O by value
    o: O
    n: int
  Tup = tuple[a: int, b: int]

proc sutVar(k: int) =
  var o: O
  if o.x == 5: symexTarget("h")

proc sutDefault(k: int) =
  let o = default(O)
  if o.x == 5: symexTarget("h")

proc sutEmptyCtor(k: int) =
  let o = O()
  if o.x == 5: symexTarget("h")

proc sutOmitOne(k: int) =
  let p = P(a: k)
  if p.b == 7: symexTarget("h")

proc sutNew(k: int) =
  var q: Q
  new(q)
  if q.x == 5: symexTarget("h")

proc sutRefCtorOmit(k: int) =
  let q = Q()
  if q.x == 5: symexTarget("h")

proc mkO(k: int): O =
  discard

proc sutResult(k: int) =
  let o = mkO(k)
  if o.x == 5: symexTarget("h")

proc sutNested(k: int) =
  var w: Wrap
  if w.o.x == 5: symexTarget("h")

proc sutArray(k: int) =
  var a: array[2, O]
  if a[1].x == 5: symexTarget("h")

# controls: no defaulted field is zero-initialised
proc sutExplicit(k: int) =
  let o = O(x: k)
  if o.x == 1: symexTarget("h")

proc sutExplicitAll(k: int) =
  let p = P(a: k, b: 9)
  if p.b == 9: symexTarget("h")

proc sutExplicitRef(k: int) =
  let q = Q(x: k)
  if q.x == 1: symexTarget("h")

proc sutPlainTuple(k: int) =
  var t: Tup
  if t.a == 0: symexTarget("h")

proc tag(fn: proc (k: int)): bool =
  "h" in nativeRun(fn(1)).hits

const dom = sampled([-1, 0, 1, 2, 5, 6, 7])

# Probed on this build (Nim 2.2.10): `default(O)`, `O()`, a constructor omitting
# a defaulted field and `new` apply the default (the compiler writes it into the
# typed AST); `var o: O`, a `result` and an aggregate's zero fields read ZERO.
# The walker agrees with the native run in every shape, so none declines.
suite "W1-f field defaults agree with the native run":
  test "version floor":
    check parseInt(symexWalkerVersion) >= 278

  test "native: the default is applied by default(O), O(), omission and new":
    check "h" in nativeRun(sutDefault(0)).hits
    check "h" in nativeRun(sutEmptyCtor(0)).hits
    check "h" in nativeRun(sutOmitOne(0)).hits
    check "h" in nativeRun(sutNew(0)).hits
    check "h" in nativeRun(sutRefCtorOmit(0)).hits

  test "native: var, result, nested and array fields read zero":
    check "h" notin nativeRun(sutVar(0)).hits
    check "h" notin nativeRun(sutResult(0)).hits
    check "h" notin nativeRun(sutNested(0)).hits
    check "h" notin nativeRun(sutArray(0)).hits

  test "default(O), O(), omission, new and ref omission are exact (sat)":
    template sat(fn, nm: untyped) =
      check pinExact(fn, cellKey(axTypeOp, "fieldDefault/int"),
                     target = tLabel("h"), domain = dom).status == sxSat
    sat(sutDefault, "default")
    sat(sutEmptyCtor, "emptyCtor")
    sat(sutOmitOne, "omitOne")
    sat(sutNew, "new")
    sat(sutRefCtorOmit, "refOmit")

  test "var, result, nested and array zero fields are exact (unsat)":
    template unsat(fn, nm: untyped) =
      check pinExact(fn, cellKey(axTypeOp, "fieldDefault/int"),
                     target = tLabel("h"), domain = dom).status == sxUnsat
    unsat(sutVar, "var")
    unsat(sutResult, "result")
    unsat(sutNested, "nested")
    unsat(sutArray, "array")

  test "explicit construction stays exact":
    check pinExact(sutExplicit, cellKey(axTypeOp, "fieldDefault/int"),
                   target = tLabel("h"), domain = dom).status == sxSat
    check pinExact(sutExplicitAll,
                   cellKey(axTypeOp, "fieldDefault/int"),
                   target = tLabel("h"), domain = dom).status == sxSat
    check pinExact(sutExplicitRef,
                   cellKey(axTypeOp, "fieldDefault/int"),
                   target = tLabel("h"), domain = dom).status == sxSat
    check pinExact(sutPlainTuple, cellKey(axTypeOp, "fieldDefault/int"),
                   target = tLabel("h"), domain = dom).status == sxSat

# --- case with elif ------------------------------------------------------------

proc caseStmt(x: int) =
  case x
  of 1: discard
  elif x > 5: symexTarget("big")
  else: discard

proc caseStmtOrder(x: int) =
  case x
  of 1: symexTarget("one")
  elif x == 1: symexTarget("dup")
  else: discard

proc caseStmtLast(x: int) =
  case x
  of 1: discard
  elif x > 5: discard
  elif x < -5: symexTarget("neg")
  else: symexTarget("mid")

proc caseExprLet(x: int) =
  let y = case x
    of 1: 10
    elif x > 5: 20
    else: 30
  if y == 20: symexTarget("big")

proc caseExprCond(x: int) =
  if (case x
      of 1: 10
      elif x > 5: 20
      else: 30) == 20:
    symexTarget("big")

proc caseVal(x: int): int =           # the case is the proc's implicit result
  case x
  of 1: 10
  elif x > 5: 20
  else: 30

proc caseHoisted(x: int) =
  if caseVal(x) == 20: symexTarget("big")

proc caseExprOrder(x: int) =
  let y = case x
    of 1: 10
    elif x == 1: 11
    else: 30
  if y == 11: symexTarget("big")

proc caseExprOrderOf(x: int) =
  let y = case x
    of 1: 10
    elif x == 1: 11
    else: 30
  if y == 10: symexTarget("of")

const domC = sampled([-7, -1, 0, 1, 2, 5, 6, 7, 100])

suite "W1-f case with elif":
  test "native: x = 6 reaches big in every form":
    check "big" in nativeRun(caseStmt(6)).hits
    check "big" in nativeRun(caseExprLet(6)).hits
    check "big" in nativeRun(caseExprCond(6)).hits
    check "big" in nativeRun(caseHoisted(6)).hits

  test "statement form":
    let r = pinExact(caseStmt, cellKey(axConstruct, "case/elif/stmt"),
                     target = tLabel("big"), domain = domC)
    check r.status == sxSat
    check r.witness[0] > 5

  test "expression form (let-bound)":
    let r = pinExact(caseExprLet, cellKey(axConstruct, "case/elif/expr"),
                     target = tLabel("big"), domain = domC)
    check r.status == sxSat
    check r.witness[0] > 5

  test "expression form (in a condition)":
    let r = pinExact(caseExprCond, cellKey(axConstruct, "case/elif/exprCond"),
                     target = tLabel("big"), domain = domC)
    check r.status == sxSat
    check r.witness[0] > 5

  test "hoisted form (a proc whose result is the case)":
    let r = pinExact(caseHoisted, cellKey(axConstruct, "case/elif/hoisted"),
                     target = tLabel("big"), domain = domC)
    check r.status == sxSat
    check r.witness[0] > 5

  test "an elif arm after an of arm never sees that value (statement)":
    let r = pinExact(caseStmtOrder, cellKey(axConstruct, "case/elif/orderStmt"),
                     target = tLabel("dup"), domain = domC)
    check r.status == sxUnsat

  test "an elif arm after an of arm never sees that value (expression)":
    let r = pinExact(caseExprOrder, cellKey(axConstruct, "case/elif/orderExpr"),
                     target = tLabel("big"), domain = domC)
    check r.status == sxUnsat

  test "the of arm wins the value an elif repeats (sat siblings of the order cells)":
    # A sampled unsat classifies no cell; the same construct's sat witness does.
    let s = pinExact(caseStmtOrder, cellKey(axConstruct, "case/elif/orderStmt"),
                     target = tLabel("one"), domain = domC)
    check s.status == sxSat
    check s.witness[0] == 1
    let e = pinExact(caseExprOrderOf, cellKey(axConstruct, "case/elif/orderExpr"),
                     target = tLabel("of"), domain = domC)
    check e.status == sxSat
    check e.witness[0] == 1

  test "elif arms are tried in order, else last":
    let rn = pinExact(caseStmtLast, cellKey(axConstruct, "case/elif/chain"),
                      target = tLabel("neg"), domain = domC)
    check rn.status == sxSat
    check rn.witness[0] < -5
    let rm = pinExact(caseStmtLast, cellKey(axConstruct, "case/elif/chainElse"),
                      target = tLabel("mid"), domain = domC)
    check rm.status == sxSat
    check rm.witness[0] != 1 and rm.witness[0] <= 5 and rm.witness[0] >= -5

# --- field defaults across the other field shapes ------------------------------
# A variant branch, an inherited parent, a generic, an object-typed default, a
# seq/string default (`@[]` was a compile stop: the default arrives as a bare
# empty `[]`; `@[1, 2]` arrived as an array), enum/char/float, a tuple and a
# ref. Each agrees with the native run: default(T), T() and new apply the
# default; `var o: T` reads zero.

type
  Color = enum red, green, blue
  I = object
    a: int
  V = object
    case k: bool
    of true: a: int = 5
    of false: b: int = 6
  PA = object of RootObj
    x: int = 5
  CH = object of PA
    y: int = 6
  G[T] = object
    x: int = 5
    y: T
  N = object
    inner: I = I(a: 3)
  S = object
    s: seq[int] = @[1, 2]
    str: string = "ab"
  E = object
    e: Color = blue
    c: char = 'z'
    f: float = 2.5
  T2 = object
    t: (int, int) = (1, 2)
  R = ref object
    x: int = 5
    n: I = I(a: 3)

# variant
proc vVar(k: int) =
  var o: V
  if o.b == 6: symexTarget("h")
proc vDef(k: int) =
  let o = default(V)
  if o.b == 6: symexTarget("h")
proc vCtor(k: int) =
  let o = V(k: false)
  if o.b == 6: symexTarget("h")
proc vCtorT(k: int) =
  let o = V(k: true)
  if o.a == 5: symexTarget("h")
# inherited
proc iVar(k: int) =
  var o: CH
  if o.x == 5 and o.y == 6: symexTarget("h")
proc iDef(k: int) =
  let o = default(CH)
  if o.x == 5 and o.y == 6: symexTarget("h")
proc iCtor(k: int) =
  let o = CH()
  if o.x == 5 and o.y == 6: symexTarget("h")
# generic
proc gVar(k: int) =
  var o: G[int]
  if o.x == 5: symexTarget("h")
proc gDef(k: int) =
  let o = default(G[int])
  if o.x == 5: symexTarget("h")
proc gCtor(k: int) =
  let o = G[int]()
  if o.x == 5: symexTarget("h")
# nested object default
proc nVar(k: int) =
  var o: N
  if o.inner.a == 3: symexTarget("h")
proc nDef(k: int) =
  let o = default(N)
  if o.inner.a == 3: symexTarget("h")
proc nCtor(k: int) =
  let o = N()
  if o.inner.a == 3: symexTarget("h")
# seq/string
proc sVar(k: int) =
  var o: S
  if o.s.len == 2 and o.str.len == 2: symexTarget("h")
proc sDef(k: int) =
  let o = default(S)
  if o.s.len == 2 and o.str.len == 2: symexTarget("h")
proc sCtor(k: int) =
  let o = S()
  if o.s.len == 2 and o.str.len == 2: symexTarget("h")
type SQ = object
  s: seq[int] = @[1, 2]
type ST = object
  str: string = "ab"
type SE = object
  s: seq[int] = @[]
proc qDef(k: int) =
  let o = default(SQ)
  if o.s.len == 2: symexTarget("h")
proc qIdx(k: int) =
  let o = SQ()
  if o.s[1] == 2: symexTarget("h")
proc tsDef(k: int) =
  let o = default(ST)
  if o.str.len == 2: symexTarget("h")
proc qeDef(k: int) =
  let o = default(SE)
  if o.s.len == 0: symexTarget("h")
# enum/char/float
proc eVar(k: int) =
  var o: E
  if o.e == blue and o.c == 'z' and o.f == 2.5: symexTarget("h")
proc eDef(k: int) =
  let o = default(E)
  if o.e == blue and o.c == 'z' and o.f == 2.5: symexTarget("h")
proc eCtor(k: int) =
  let o = E()
  if o.e == blue and o.c == 'z' and o.f == 2.5: symexTarget("h")
# tuple field
proc tVar(k: int) =
  var o: T2
  if o.t[0] == 1: symexTarget("h")
proc tDef(k: int) =
  let o = default(T2)
  if o.t[0] == 1: symexTarget("h")
proc tCtor(k: int) =
  let o = T2()
  if o.t[0] == 1: symexTarget("h")
# ref
proc rNew(k: int) =
  var o: R
  new(o)
  if o.x == 5 and o.n.a == 3: symexTarget("h")
proc rCtor(k: int) =
  let o = R()
  if o.x == 5 and o.n.a == 3: symexTarget("h")


func shapeKind(fn: string): string =
  ## K3b: the `typeop:fieldDefault/<IR kind>` row of the field the SUT reads.
  case fn
  of "sVar", "sDef", "sCtor", "qDef", "qIdx", "qeDef": "seq"
  of "tsDef": "string"
  of "eVar", "eDef", "eCtor": "float64"
  of "tVar", "tDef", "tCtor": "tuple"
  else: "int"

suite "W1-f field defaults across field shapes":
  test "default(T), T(), new apply the default (sat)":
    template sat(fn: untyped) =
      check pinExact(fn, cellKey(axTypeOp, "fieldDefault/" & shapeKind(astToStr(fn))),
                     target = tLabel("h"), domain = dom).status == sxSat
    sat(vDef)
    sat(vCtor)
    sat(vCtorT)
    sat(iDef)
    sat(iCtor)
    sat(gDef)
    sat(gCtor)
    sat(nDef)
    sat(nCtor)
    sat(sDef)
    sat(sCtor)
    sat(qDef)
    sat(qIdx)
    sat(tsDef)
    sat(qeDef)
    sat(eDef)
    sat(eCtor)
    sat(tDef)
    sat(tCtor)
    sat(rNew)
    sat(rCtor)

  test "var o: T reads zero (unsat)":
    template unsat(fn: untyped) =
      check pinExact(fn, cellKey(axTypeOp, "fieldDefault/" & shapeKind(astToStr(fn))),
                     target = tLabel("h"), domain = dom).status == sxUnsat
    unsat(vVar)
    unsat(iVar)
    unsat(gVar)
    unsat(nVar)
    unsat(sVar)
    unsat(eVar)
    unsat(tVar)
