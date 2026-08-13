## Phase 15 — Cluster G, cycle G8: multi-parameter generics.
##
## LOCKED DECISION (RFC-phase15-reconciliation.md §F Cluster G): generic procs
## already symex via PARSE-TIME monomorphization. Cluster G adds NO `isGenericCall`
## IR. The multi-param machinery is ALREADY in place:
##   * `gatherTypeSubst` (dsl_parser.nim) iterates the formal params, binding ONE
##     entry per generic-named param from the matching call-site arg's `getType`
##     — so `[T, U]` records both `T` and `U` independently (no conflation, no
##     arg-index off-by-one: `argIx` advances once per formal name).
##   * `instKeyFor` (G1a, ADR-0008 D2/D6) sorts the concrete-type tuple BY
##     formal-param NAME, so the instantiation key is ORDER-INDEPENDENT — but two
##     DIFFERENT type tuples still produce DIFFERENT keys (a `T=int,U=string`
##     instantiation never collides with a `T=string,U=int` one).
##
## G8 is therefore mostly an AUDIT + REGRESSION-GUARD cycle (per RFC §G8: "no
## structural changes beyond any bug fixes the RED test surfaces"). This test
## pins the multi-param behavior:
##   1. `T` and `U` resolve INDEPENDENTLY — int arithmetic on the `T=int` param,
##      string equality on the `U=string` param, in ONE proc, NOT conflated.
##   2. A different type pairing (`T=bool, U=int`) also works — no accidental
##      param-ORDER dependency.
##   3. Two DIFFERENT type tuples that differ only by which param holds which
##      type (`T=bool,U=int` vs `T=int,U=bool`) dispatch to CORRECTLY-typed
##      bodies — i.e. the sorted key does NOT collapse them onto one another (the
##      G1a sorted-key working for multi-param). Asserted via BEHAVIOR: both
##      proc instantiations symex to the right witnesses simultaneously.
import std/unittest
import nelli/symex

# --- 1. T=int, U=string: int arith on `a`, string eq on `b` (not conflated) ---
proc foo[T, U](a: T, b: U): bool = a > 0 and b == "ok"

proc useFoo(a: int, b: string) =
  # T binds int (a > 0 is integer arithmetic); U binds string (b == "ok" is
  # Z3 string equality). If T and U were conflated, one of the two comparisons
  # would be ill-typed / mis-lowered and the target would be unreachable.
  if foo(a, b):
    symexTarget("hit")

# --- 2. T=bool, U=int: param-order independence ---
proc bar[T, U](a: T, b: U): bool = a and b > 5

proc useBar(a: bool, b: int) =
  # T binds bool (`a` used as a boolean), U binds int (`b > 5`). Witness should
  # be a=true, b=6 (smallest int > 5).
  if bar(a, b):
    symexTarget("hit2")

# --- 3. Order-independence WITHOUT collision: the SAME generic `pick` is
# instantiated at TWO type tuples that are reverses of one another. Each must
# dispatch to a correctly-typed body. ---
# pick[T, U](a, b): a is `T`, b is `U`. We gate the int operand on arithmetic
# and the string operand on equality, so the two instantiations exercise the
# params in OPPOSITE positions.
proc pick[T, U](a: T, b: U): bool =
  when T is int and U is string:
    a == 7 and b == "x"
  elif T is string and U is int:
    a == "y" and b == 9
  else:
    false

proc useBothOrders(p: int, q: string, r: string, s: int) =
  # pick(p, q): T=int,  U=string  ⇒ p == 7 and q == "x"
  # pick(r, s): T=string, U=int   ⇒ r == "y" and s == 9
  # If the two instantiations collided on a single key (order-INdependence done
  # WRONG, collapsing distinct tuples), one body would be reused for both calls
  # and the conjunction would be unreachable.
  if pick(p, q) and pick(r, s):
    symexTarget("hit3")

suite "symex Phase 15 G8 — multi-parameter generics":
  test "T=int, U=string resolve independently (int arith + string eq)":
    let r = symexFind(useFoo, tLabel("hit"))
    check r.status == sxSat
    check r.witness[0] > 0        ## a : int, > 0
    check r.witness[1] == "ok"    ## b : string, == "ok"

  test "T=bool, U=int works (no param-order dependency)":
    let r = symexFind(useBar, tLabel("hit2"))
    check r.status == sxSat
    check r.witness[0] == true    ## a : bool
    check r.witness[1] > 5        ## b : int, > 5

  test "reversed type tuples dispatch to distinct, correctly-typed bodies":
    let r = symexFind(useBothOrders, tLabel("hit3"))
    check r.status == sxSat
    check r.witness[0] == 7       ## p : int   (pick[int,string] arg a)
    check r.witness[1] == "x"     ## q : string(pick[int,string] arg b)
    check r.witness[2] == "y"     ## r : string(pick[string,int] arg a)
    check r.witness[3] == 9       ## s : int   (pick[string,int] arg b)
