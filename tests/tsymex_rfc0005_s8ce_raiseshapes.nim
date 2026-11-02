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
## shape and the SECOND operation of that shape raises out of the walker's
## own code with its Z3 temporaries live (`injectShapeFault`), the first
## operation's path already built, so its terms are on the unwind:
## - `solver`: a query's `check()` (the target hit's solve);
## - `term`: arithmetic lowering, both operand terms built;
## - `eval`: a model evaluation in witness extraction;
## - `dispatch`: the sentinel statement itself, in the walked proc or in a
##   callee.
## Each sits after a branch, so two paths reach it, and after a loop, so the
## raise unwinds through `walkBlock`'s reassignment of the loop's paths.
## Each must be a named decline (`sxUnknown` + `weInternalWalkerFault`),
## never a verdict.
import std/[unittest, strutils]
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

# Each shape: bounded inputs, a loop, the sentinel, then the shape's
# operation in BOTH arms of a branch, so the first arm's paths are built and
# held when the second arm's operation raises.

proc solverShape(n: int) =
  if n < 0 or n > 10: return
  var i = 0
  while i < n and i < 4:
    inc i
  symexTarget("__inject_s8ce_solver__")
  if i == 3:
    if n > 5: symexTarget("solver_hit")
  else:
    if n == 2: symexTarget("solver_hit")

proc termShape(n: int) =
  if n < 0 or n > 10: return
  var i = 0
  while i < n and i < 4:
    inc i
  symexTarget("__inject_s8ce_term__")
  var k = 0
  if n > 5:
    k = i + n
  else:
    k = i + 2 * n
  if k == 7:
    symexTarget("term_hit")

proc evalShape(s, t: string, n: int) =
  if n < 0 or n > 10: return
  var i = 0
  while i < n and i < 4:
    inc i
  symexTarget("__inject_s8ce_eval__")
  if i == 3 and s.len == 2 and t.len == 1:
    symexTarget("eval_hit")

proc dispatchShape(n: int) =
  if n < 0 or n > 10: return
  var i = 0
  while i < n and i < 4:
    inc i
  if i == 3:
    symexTarget("__inject_s8ce_dispatch__")
  else:
    symexTarget("__inject_s8ce_dispatch__")
  if n > 1:
    symexTarget("dispatch_hit")

proc injectingCallee(x: int): int =
  symexTarget("__inject_s8ce_dispatch__")
  x + 1

proc calleeShape(n: int) =
  if n < 0 or n > 10: return
  var i = 0
  while i < n and i < 4:
    inc i
  var k = 0
  if n > 5:
    k = injectingCallee(i)
  else:
    k = injectingCallee(n)
  if k == 4:
    symexTarget("callee_hit")

proc cleanShape(n: int) =
  if n < 0 or n > 10: return
  var i = 0
  while i < n and i < 4:
    inc i
  var k = 0
  if n > 5:
    k = i + n
  else:
    k = i + 2 * n
  if k == 7:
    symexTarget("clean_hit")

proc fault(shape: string): string = "S8ce synthetic " & shape & " fault"

suite "S8ce (5): each raise shape reaches the run boundary":

  test "a raise after a query's check() (solver call)":
    let r = symexFind(solverShape, tLabel("solver_hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check namedFault(r, fault("solver"))

  test "a raise in arithmetic lowering with both operands built (term)":
    let r = symexFind(termShape, tLabel("term_hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check namedFault(r, fault("term"))

  test "a raise after a model evaluation in extraction (eval)":
    let r = symexFind(evalShape, tLabel("eval_hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxSat
    check namedFault(r, fault("eval"))

  test "a raise at statement dispatch after a loop (dispatch)":
    let r = symexFind(dispatchShape, tLabel("dispatch_hit"))
    checkpoint $r.status & " " & show(r.errors)
    check namedFault(r, fault("dispatch"))

  test "a raise at statement dispatch in a callee (callee frame)":
    let r = symexFind(calleeShape, tLabel("callee_hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status != sxUnsat
    check namedFault(r, fault("dispatch"))

  test "control: the same shape with no sentinel decides":
    let r = symexFind(cleanShape, tLabel("clean_hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat

  test "a later run is not declined by an earlier run's armed shape":
    discard symexFind(dispatchShape, tLabel("dispatch_hit"))
    let r = symexFind(cleanShape, tLabel("clean_hit"))
    checkpoint $r.status & " " & show(r.errors)
    check r.status == sxSat

suite "S8ce: walker version":

  test "walker version floor >= 238 (S8ce)":
    check parseInt(symexWalkerVersion) >= 238
