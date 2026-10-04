## RFC-0005 (soundness channels) slice S8ce, item 1 -- a nim-z3 value
## destroyed on the raise path swallowed the in-flight exception on the C
## backend.
##
## Nim 2.2.10's C backend (goto exceptions) runs a call's result
## temporary's destructor on the raise path with the error flag still set:
## `T = f(); if (*nimErr_) { eqdestroy(T); goto BeforeRet_; }` for a
## reassignment, and the scope-exit destroy at the merge label for an
## initialisation. nim-z3's hooks wrapped their bodies in `try: ... except
## CatchableError: discard` (`except Exception` for the context release).
## A `try` entered with the flag set cannot tell the in-flight exception
## from its own: its first checked call jumps to its handler, which matches
## the in-flight exception, clears the flag and pops it. The caller then
## returns as if nothing had been raised. C++ exceptions are native, and the
## destructor's `try` never sees the in-flight one.
##
## The compiler saves and clears the flag around a raise-path destroy only
## when it takes the destroy as able to raise. A `{.raises: [].}` hook, or a
## generated seq hook over one, runs with the flag set, unsaved.
##
## Each test raises out of an expression whose result holds a nim-z3 value,
## and asserts the raise reaches the outer `except`. Each family of hook is
## covered: a value term (`termDestroy`, through a seq), a ref handle
## (`emitRefcountLifecycle`: a solver, a model), and the context's own
## `=destroy` (the last reference to a context dropped on the raise path).
import std/unittest
import z3

type ShapeFault = object of CatchableError

proc fault() =
  raise newException(ShapeFault, "S8ce in-flight raise")

type Bv8 = Z3BitVec[8]

proc bvsThenRaise(ctx: Z3Context; n: int): seq[Bv8] =
  result = @[mkBitVec[8](ctx, n), mkBitVec[8](ctx, n + 1)]
  if n >= 0: fault()

proc solverThenRaise(ctx: Z3Context; n: int): Z3Solver =
  result = newSolver(ctx)
  if n >= 0: fault()

proc modelOf(ctx: Z3Context): Z3Model =
  let s = newSolver(ctx)
  discard s.check()
  s.model()

proc modelThenRaise(ctx: Z3Context; n: int): Z3Model =
  result = modelOf(ctx)
  if n >= 0: fault()

proc ownCtxIntsThenRaise(n: int): seq[Z3Int] =
  # The only references to this context are the elements': dropping the
  # result on the raise path runs `Z3ContextOwn`'s `=destroy`. (A new
  # context becomes the thread's current one, which holds a reference.)
  let prev = currentContext()
  let ctx = newContext()
  setCurrentContext(prev)
  result = @[mkInt(ctx, n)]
  if n >= 0: fault()

# Reassignment from a call: the result temporary is destroyed right after
# the call, on the raise path, with the flag set and not saved.
proc reassignBvs(ctx: Z3Context; n: int): int =
  var r = @[mkBitVec[8](ctx, 0)]
  r = bvsThenRaise(ctx, n)
  r.len

proc reassignSolver(ctx: Z3Context; n: int): int =
  var r = newSolver(ctx)
  r = solverThenRaise(ctx, n)
  1

proc reassignModel(ctx: Z3Context; n: int): int =
  var r = modelOf(ctx)
  r = modelThenRaise(ctx, n)
  1

proc reassignOwnCtx(n: int): int =
  var r = @[mkInt(newContext(), 0)]
  r = ownCtxIntsThenRaise(n)
  r.len

# Initialisation from a call: the local's destroy at the scope's merge
# label is a generated seq hook, which the compiler takes as unable to
# raise, so it runs with the flag set and not saved.
proc initBvs(ctx: Z3Context; n: int): int =
  let r = bvsThenRaise(ctx, n)
  r.len

proc initOwnCtx(n: int): int =
  let r = ownCtxIntsThenRaise(n)
  r.len

proc reaches(body: proc (): int): bool =
  ## True when the raise reaches this outer `except`.
  try:
    discard body()
    false
  except ShapeFault:
    true

suite "RFC-0005 S8ce item 1: a raise survives a nim-z3 value's destroy":
  let ctx = newContext()

  test "a seq of bit-vector terms reassigned from a raising call":
    check reaches(proc (): int = reassignBvs(ctx, 1))

  test "a solver (ref handle) reassigned from a raising call":
    check reaches(proc (): int = reassignSolver(ctx, 1))

  test "a model (ref handle) reassigned from a raising call":
    check reaches(proc (): int = reassignModel(ctx, 1))

  test "terms holding the last reference to their context, reassigned":
    check reaches(proc (): int = reassignOwnCtx(1))

  test "a seq of bit-vector terms initialised from a raising call":
    check reaches(proc (): int = initBvs(ctx, 1))

  test "terms holding the last reference to their context, initialised":
    check reaches(proc (): int = initOwnCtx(1))

  test "control: no raise returns normally":
    check reassignBvs(ctx, -5) == 2
    check initBvs(ctx, -5) == 2
    check reassignSolver(ctx, -5) == 1
    check reassignModel(ctx, -5) == 1
    check reassignOwnCtx(-5) == 1
