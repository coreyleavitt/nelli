## Phase 15 — Cluster C, cycle C3: top-level procs as VALUES (unit-env).
##
## A top-level (module-scope) proc referenced in EXPRESSION (value) position —
## `let g = double` — is a proc-as-value with NO free variables. The parser
## detects the `nnkSym` whose `symKind == nskProc` (not a local var, not a
## `nnkParam`, not a call callee) and encodes it as an `iekLambda` with
## `lambdaCaptures = @[]`. Construction (C2a `buildClosure`) materialises a
## ZERO-field `svTuple` unitEnv; CALLING it (`g(n)`) dispatches through the
## existing C2b `iekClosureCall` path. The witness/verdict MUST equal a SUT
## that calls `double(n)` directly — the encoding is semantically transparent.
##
## C3 is ADDITIVE under walker version "8" (no bump; Cluster C bumps at C6).
import std/unittest
import nelli/symex

# --- SUT 1: top-level proc stored as a value, then called. -------------------
#
#   proc double(x: int): int = x * 2
#   proc sut(n: int): int =
#     let g = double        # `double` in VALUE position → iekLambda (unit-env)
#     g(n)                  # `g(n)` → iekClosureCall (C2b)
#
# Gate the result at 10 ⇒ the witness must be n == 5 (5*2 == 10).
proc double(x: int): int = x * 2

proc sutProcAsValue(n: int) =
  let g = double
  if g(n) == 10:
    symexTarget("proc-as-value")

# --- SUT 2: the SAME proc called DIRECTLY (the reference encoding). -----------
#
#   proc sut(n: int): int = double(n)   # `double` in CALLEE position → isCall
#
# Same gate ⇒ same witness n == 5. The value-vs-callee parser distinction must
# NOT change the result.
proc sutDirectCall(n: int) =
  if double(n) == 10:
    symexTarget("direct")

# --- SUT 3 (optional): a top-level proc passed as a proc-valued ARG. ----------
#
#   proc applyOnce(f: proc(x: int): int, v: int): int = f(v)
#   proc sut(n: int): int = applyOnce(double, n)   # `double` as ARG value
#
# `applyOnce(double, n)` == double(n) == n*2. Same gate ⇒ witness n == 5.
proc applyOnce(f: proc(x: int): int, v: int): int = f(v)

proc sutProcAsArg(n: int) =
  if applyOnce(double, n) == 10:
    symexTarget("as-arg")

suite "symex Phase 15 C3 — top-level procs as values (unit-env)":

  test "C3: top-level proc stored as value and called produces same witness as direct call":
    let viaValue  = symexFind(sutProcAsValue, tLabel("proc-as-value"))
    let viaDirect = symexFind(sutDirectCall, tLabel("direct"))
    check viaValue.status == sxSat
    check viaDirect.status == sxSat
    check viaValue.witness[0] == 5     ## n : n*2 == 10 ⇒ n == 5
    check viaDirect.witness[0] == 5
    # Same verdict AND same witness — the proc-as-value encoding is transparent.
    check viaValue.status == viaDirect.status
    check viaValue.witness[0] == viaDirect.witness[0]

  test "C3: top-level proc passed as a proc-valued argument resolves and is called":
    let r = symexFind(sutProcAsArg, tLabel("as-arg"))
    check r.status == sxSat
    check r.witness[0] == 5             ## n : double(n) == 10 ⇒ n == 5
