## Phase 15 — Cluster G, cycle G7: `static[T]` params as instantiation-key
## components.
##
## A `static[T]` generic param is a COMPILE-TIME constant, not a runtime value.
## `proc foo[N: static int](x: array[N, int]): bool` instantiated at `N = 3`
## and `N = 5` must produce TWO DISTINCT instantiations — each with `N` bound to
## its literal, dispatching to its own monomorphized body (so `x[N-1]` is
## `x[2]` for `N = 3` and `x[4]` for `N = 5`).
##
## REAL-AST FINDINGS (probed on the typed AST; the RFC's idealized account is
## simplified):
##   * The static-param CONSTRAINT in the typed generic-params node is an
##     `nnkCommand[Ident "static", Sym "int"]` (NOT `nnkStaticTy`, which the RFC
##     §G7 GREEN guessed).
##   * The static VALUE is NOT a call-site arg: `foo[3]`/`bar[3]` lose their
##     `[3]` brackets in the typed `Call` node. Nim's semchecker has ALREADY
##     monomorphized the static value INTO THE BODY (`x[N-1]` is already baked
##     to `x[2]`; `x > N` already baked to `x > 3`). The un-substituted spot is
##     a FORMAL param's type that mentions `N` (e.g. `array[N, int]`), which
##     `classifyType` cannot size until `N` is substituted.
##   * The two instantiation callee Syms are DISTINCT and `symBodyHash` ALREADY
##     differs between them — so the instantiation key naturally becomes
##     distinct once it stops collapsing to the BARE proc name (a static-only
##     generic produces an empty TYPE subst → pre-G7 `instKeyFor` returned the
##     bare name → COLLISION, exactly the G1a bug class).
##
## BEHAVIOR ASSERTED (not the RFC's idealized `"foo#int;static=3"` key string —
## the real key carries a per-instantiation `bodyHash`, see reconciliation §F-G
## G7): the two `foo` instantiations dispatch correctly to bodies that differ
## by the substituted literal index, and a `static[bool]` generic likewise
## dispatches per-value. Pre-G7 the two calls collide (or the `array[N,int]`
## formal fails to size) → wrong/unknown; post-G7 → distinct + correct.
import std/unittest
import nelli/symex

# Canonical static-param use: `array[N, int]`. `x[N-1]` is the LAST element, so
# the witnessed index DIFFERS per instantiation (x[2] for N=3, x[4] for N=5) —
# direct proof that N was substituted per-instantiation, not shared.
proc lastPos[N: static int](x: array[N, int]): bool = x[N-1] > 0

proc twoArrays(a3: array[3, int], a5: array[5, int]) =
  # Requires a3[2] > 0 AND a5[4] > 0 — the two instantiations must dispatch to
  # DISTINCT bodies (x[2] vs x[4]). Pre-G7: bare-name collision drops the second
  # instantiation (or the array[N,int] formal can't be sized) → not sxSat with
  # both witnessed indices satisfied.
  if lastPos(a3) and lastPos(a5):
    symexTarget("both")

# static[bool]: the body's `B` is baked by the semchecker to the literal, so
# `gate[true]` is `(x > 0) == true` and `gate[false]` is `(x > 0) == false`.
proc gate[B: static bool](x: int): bool = (x > 0) == B

proc twoBools(p: int, q: int) =
  # gate[true](p) ⇒ p > 0 ; gate[false](q) ⇒ not (q > 0) ⇒ q <= 0.
  # Distinct instantiations dispatch to bodies with opposite polarity.
  if gate[true](p) and gate[false](q):
    symexTarget("polar")

suite "symex Phase 15 G7 — static[T] params in the instantiation key":
  test "two static[int] array instantiations dispatch to distinct bodies":
    let r = symexFind(twoArrays, tLabel("both"))
    check r.status == sxSat
    # N=3 ⇒ x[2] is the gated element; N=5 ⇒ x[4]. The witnessed indices differ,
    # proving per-instantiation substitution of N.
    check r.witness[0][2] > 0    ## a3[N-1] = a3[2]
    check r.witness[1][4] > 0    ## a5[N-1] = a5[4]

  test "static[bool] instantiations dispatch per-value (true vs false)":
    let r = symexFind(twoBools, tLabel("polar"))
    check r.status == sxSat
    check r.witness[0] > 0        ## gate[true]:  p > 0
    check r.witness[1] <= 0       ## gate[false]: q <= 0
