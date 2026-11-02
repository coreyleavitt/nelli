## RFC-0005 (soundness channels) slice S8ce, item 5 -- every shape of raise
## the walker produces reaches the run boundary on the C backend.
##
## A raise unwinding through the walk crosses destroys of Z3-term-holding
## temporaries: `walkBlock`'s reassigned `seq[Path]` (`result = walk(s,
## result, w)`), an expression's operand `SymVal`s, a query's solver and
## model, an evaluated term. Nim 2.2.10's C backend runs those destroys with
## the error flag set (unsaved for a `{.raises: [].}` hook or a generated
## hook over one), and nim-z3's hooks wrapped their bodies in `try: ...
## except CatchableError: discard`, which took the in-flight exception as
## their own and cleared it: the walk went on as if nothing had raised, to a
## false verdict. S8bx closed extraction alone, with a raise hook; S8ce
## fixes the hooks in nim-z3 (raise-free by construction, `quirky`), so the
## raise survives every destroy whatever raised it.
##
## The companion `.nim.cfg` sets `-d:symexTestInjectWalkerFault`, under
## which dispatch reaching `symexTarget("__inject_s8ce_<shape>__")` arms one
## shape and the shape's next operation raises out of the walker's own code
## with its Z3 temporaries live (`injectShapeFault`):
## - `term`: arithmetic lowering, both operand terms built;
## - `solver`: a query's `check()`, the solver live;
## - `roots`: query assembly, the local `seq[Z3Bool]` of roots held;
## - `conds`: a range conversion, the local `seq[Z3Bool]` of bounds held;
## - `eval`: a model evaluation in witness extraction, the evaluated term
##   live;
## - `dispatch`: the sentinel statement itself.
## Which destroy the raise crosses first depends on the statement around it,
## so a shape is the operation AND its setting: in a loop body (`walkBlock`'s
## `result = walk(s, result, w)` with the iteration's paths in the temporary),
## in an `if` condition (`walk`'s `states` / `next`), in a callee's loop, with
## an `mpairs` view live (`syncViewAliases(walk(...))`), and in the concolic
## walk (`walkIfFollowConcrete`'s `states`). Each must be a named decline
## (`sxUnknown` + `weInternalWalkerFault`), never a verdict.
import std/[unittest, strutils, tables]
import nelli/symex
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

proc namedFault[T](r: SymexResult[T]; text: string): bool =
  ## The run declines with `weInternalWalkerFault` naming the injected raise.
  if r.status != sxUnknown: return false
  for e in r.errors:
    if e.kind == weInternalWalkerFault and e.severity == sevError and
       text in e.msg:
      return true
  false

# Each shape arms its fault in a loop's last iteration or just before an
# `if`, so the raise crosses the destroy its comment names.

# `walkBlock`'s `result = walk(s, result, w)`, the paths held.
proc termInLoop(n: int) =
  if n < 0 or n > 10: return
  var k = 0
  for j in 0 ..< 3:
    if j == 2: symexTarget("__inject_s8ce_term__")
    k = k + j + n
  if k == 12: symexTarget("hit")

proc dispatchInLoop(n: int) =
  if n < 0 or n > 10: return
  var k = 0
  for j in 0 ..< 3:
    if j == 2: symexTarget("__inject_s8ce_dispatch__")
    k = k + j
  if k == 3 and n > 2: symexTarget("hit")

proc solverInLoop(n: int) =
  if n < 0 or n > 10: return
  for j in 0 ..< 3:
    if j == 2: symexTarget("__inject_s8ce_solver__")
    if n == j + 100: symexTarget("miss")
  if n == 7: symexTarget("hit")

proc rootsInLoop(n: int) =
  if n < 0 or n > 10: return
  for j in 0 ..< 3:
    if j == 2: symexTarget("__inject_s8ce_roots__")
    if n == j + 100: symexTarget("miss")
  if n == 7: symexTarget("hit")

proc condsInLoop(n: int) =
  if n < 0 or n > 10: return
  var k = 0
  for j in 0 ..< 3:
    if j == 2: symexTarget("__inject_s8ce_conds__")
    k = k + int(Natural(n))
  if k == 21: symexTarget("hit")

# A call's frame between the raise and the loop.
proc faultingCallee(x: int): int =
  symexTarget("__inject_s8ce_term__")
  x + 1

proc termInCallee(n: int) =
  if n < 0 or n > 10: return
  var k = 0
  for j in 0 ..< 3:
    if j == 2: k = faultingCallee(k)
    else: k = k + n
  if k == 15: symexTarget("hit")

# `lowerBoolInExpr` over a path that has a live arm beside it.
proc termInCond(n: int) =
  if n < 0 or n > 10: return
  var k = 0
  for j in 0 ..< 3:
    if j == 2: symexTarget("__inject_s8ce_term__")
    if k + n == 100: symexTarget("miss")
    k = k + 1
  if n == 1: symexTarget("hit")

# Witness extraction, at a target hit in a loop's walk.
proc evalInLoop(s: string, n: int) =
  if n < 0 or n > 10: return
  var k = 0
  for j in 0 ..< 3:
    k = k + j
    if j == 2:
      symexTarget("__inject_s8ce_eval__")
      if n == 7 and s.len == 2: symexTarget("hit")
  if k == 100: symexTarget("miss")

# `syncViewAliases(walk(...))`: an `mpairs` view passed with its Table.
proc viewCallee(v: var int; t: var Table[string, int]; k: string): int =
  symexTarget("__inject_s8ce_term__")
  v = v + 1
  t[k]

proc termUnderView(t0: Table[string, int]) =
  if t0.len != 1 or "a" notin t0: return
  var t = t0
  for k, v in t.mpairs:
    if v > 1000 or v < -1000: return
    discard viewCallee(v, t, k)
  if t["a"] == 3: symexTarget("hit")

# The concolic walk: `walkIfFollowConcrete`'s own `states` and facts.
proc followShape(x: int) =
  var k = 0
  for j in 0 ..< 3:
    if j == 2: symexTarget("__inject_s8ce_term__")
    if k + x > 3: k = k + 1
    else: k = k + 2
  if k > 100: symexTarget("hit")

proc cleanShape(n: int) =
  if n < 0 or n > 10: return
  var k = 0
  for j in 0 ..< 3:
    k = k + j + n
  if k == 12: symexTarget("hit")

proc fault(shape: string): string = "S8ce synthetic " & shape & " fault"

template faultCase(name, fn, shape: untyped) =
  test name:
    let r = symexFind(fn, tLabel("hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status notin {sxSat, sxUnsat}
    check namedFault(r, fault(shape))

suite "S8ce (5): each raise shape reaches the run boundary":

  faultCase("term construction in a loop body", termInLoop, "term")
  faultCase("statement dispatch in a loop body", dispatchInLoop, "dispatch")
  faultCase("a solver call in a loop body", solverInLoop, "solver")
  faultCase("query assembly, its roots held", rootsInLoop, "roots")
  faultCase("a range conversion, its bounds held", condsInLoop, "conds")
  faultCase("term construction in a callee", termInCallee, "term")
  faultCase("an `if` condition beside a live arm", termInCond, "term")
  faultCase("a model evaluation in extraction", evalInLoop, "eval")
  faultCase("term construction with an `mpairs` view live", termUnderView,
            "term")

  test "term construction in the concolic walk":
    let trace = @[integerChoice(7, 0, 100, 0)]
    let bindings = @[ConcolicParamBinding(kind: cbDrawLinked, drawIndex: 0)]
    var reached = false
    try:
      discard concolicCollect(followShape, trace, bindings)
    except ValueError as e:
      reached = fault("term") in e.msg
    check reached

  test "control: the same shape with no sentinel decides":
    let r = symexFind(cleanShape, tLabel("hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat

  test "a later run is not declined by an earlier run's armed shape":
    discard symexFind(dispatchInLoop, tLabel("hit"))
    let r = symexFind(cleanShape, tLabel("hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat

suite "S8ce: walker version":

  test "walker version floor >= 238 (S8ce)":
    check parseInt(symexWalkerVersion) >= 238
