## Phase 15 — Cluster C, cycle C6: hermetic C-cluster regression smoke + walker
## version bump "8"→"9" (CLOSES Cluster C).
##
## A single in-process test file that exercises the FULL closure machinery
## (C1–C5) TOGETHER, to catch state-threading bugs introduced by the multi-file
## C1–C5 edits to the closure-lowering path (the per-site `funcSym` memo in the
## `currentClosureSyms` threadvar + `WalkerStatics.closureSyms` mirror, the
## `currentClosureBodies` site→body map, the `currentWalkCtxPtr` descent bridge,
## the GROUND closure-call axiom, the `svTupleEq` structural-env equality, and
## the `seqInlineThreshold`/`maxClosureInlineCount` HOF/inline budgets). It
## composes, in one file:
##   - closure CONSTRUCTION + CALL observing a CAPTURED value (C2a/C2b): a lambda
##     capturing an outer local, called → the captured value flows into the
##     ground axiom and pins the witness.
##   - a proc-valued PARAMETER (C2b): `applyTwice[T](f, v)` resolves `f` as an
##     svClosure (NOT ceClosureUnknownCallee) — also touches Cluster G generics.
##   - a TOP-LEVEL proc as a VALUE (C3): `let g = double; g(n)` (unit-env
##     closure) gives the SAME witness as a direct call.
##   - a bounded `filter`/`map` HOF with a closure (C4): concrete-length seq →
##     the inline path applies the predicate/mapper closure per element.
##   - closure EQUALITY (C5): distinct sites → unequal (sxUnsat on `==`);
##     same-site alias + same env → equal (sxSat via svTupleEq).
##   - the `maxClosureInlineCount` settings override (DoD): a closure SUT under
##     a tightened budget still witnesses.
##   - the walker version pin: `symexWalkerVersion == "9"` (this cycle's bump).
import std/[unittest, sequtils]
import proptest/symex

# === SUTs ====================================================================

# --- C2a/C2b: closure construction + call observing a CAPTURED value ---------
#
#   proc sut(x: int): int =
#     let offset = x * 2
#     let f = proc(y: int): int = y + offset   # captures `offset`
#     f(3)                                      # 3 + x*2
#
# Gate at 13 ⇒ witness x == 5 (3 + 5*2 == 13). The captured `offset` flows
# through the C2a env snapshot into the C2b ground axiom.
proc c6Capture(x: int) =
  let offset = x * 2
  let f = proc(y: int): int = y + offset
  if f(3) == 13:
    symexTarget("captured")

# --- C2b: a proc-valued PARAMETER (also exercises Cluster G generics) ---------
#
#   proc applyTwice[T](f: proc(x: T): T, v: T): T = f(f(v))
#   proc sut(n: int): int = applyTwice(proc(x: int): int = x + 1, n)   # n+2
#
# `applyTwice` is a GENERIC HOF (G instantiation) whose `f` is a proc-valued
# PARAM resolved as an svClosure (C2b) — the C+G composition the C6 RED test
# specifies. Gate at 42 ⇒ witness n == 40.
proc applyTwice[T](f: proc(x: T): T, v: T): T = f(f(v))

proc c6ProcParam(n: int) =
  if applyTwice(proc(x: int): int = x + 1, n) == 42:
    symexTarget("twice")

# --- C3: a TOP-LEVEL proc as a VALUE (unit-env closure) -----------------------
#
#   proc double(x: int): int = x * 2
#   proc sut(n: int): int =
#     let g = double      # proc-as-value → iekLambda, lambdaCaptures = @[]
#     g(n)                # iekClosureCall (unit-env)
#
# Gate at 10 ⇒ witness n == 5 — SAME as a direct `double(n)` call.
proc double(x: int): int = x * 2

proc c6ProcAsValue(n: int) =
  let g = double
  if g(n) == 10:
    symexTarget("proc-as-value")

proc c6DirectCall(n: int) =
  if double(n) == 10:
    symexTarget("direct")

# --- C4: a bounded `filter`/`map` HOF with a closure (inline path) ------------
#
# The seq is built by `.add`, so its length folds to a concrete numeral (3 ≤
# seqInlineThreshold) → the bounded inline path applies the closures per element.
proc c6FilterInline(a: int, b: int, c: int) =
  var xs: seq[int] = @[]
  xs.add a
  xs.add b
  xs.add c
  let kept = xs.filter(proc(x: int): bool = x > 0)
  if kept.len > 0:
    symexTarget("nonempty")

proc c6MapInline(a: int, b: int) =
  var xs: seq[int] = @[]
  xs.add a
  xs.add b
  let ys = xs.map(proc(x: int): int = x + 1)
  if ys.len == 2 and ys[0] == 10:
    symexTarget("mapped")

# --- C5: closure EQUALITY — distinct sites unequal; same-site alias equal -----
#
# Distinct lambda sites ⇒ `f == g` is false for every x (nominal-for-site
# integer-pair short-circuit) ⇒ the target is unreachable ⇒ sxUnsat.
proc c6DistinctSites(x: int) =
  let f = proc(y: int): int = y + x
  let g = proc(y: int): int = y + x
  if f == g:
    symexTarget("distinct-sites-equal")   # provably unreachable

# Same site (alias) + same env ⇒ `f == g` takes the structural-env branch
# (`svTupleEq` over the one-field `{x}` env) ⇒ sxSat.
proc c6SameSiteEqual(x: int) =
  let f = proc(y: int): int = y + x
  let g = f
  if f == g:
    symexTarget("same-site-equal")

# --- DoD: a closure SUT under a tightened maxClosureInlineCount budget --------
# A modest budget (8) still permits the single-level closure call in c6Capture.
const c6Budget = withSymexSettings() do (s: var SymexSettings):
  s.maxClosureInlineCount = 8

suite "symex Phase 15 C6 — Cluster-C regression smoke + walker version 9":

  # ---- C2a/C2b: construction + call observing a captured value ----
  test "C6: closure call observes captured value (f(3) == 3 + x*2)":
    let r = symexFind(c6Capture, tLabel("captured"))
    check r.status == sxSat
    check r.witness[0] == 5             ## x : 3 + x*2 == 13 ⇒ x == 5

  # ---- C2b: proc-valued param (+ Cluster G generic instantiation) ----
  test "C6: proc-valued param resolves via svClosure (applyTwice ⇒ n+2)":
    let r = symexFind(c6ProcParam, tLabel("twice"))
    check r.status == sxSat
    check r.witness[0] == 40            ## n : (n+1)+1 == 42 ⇒ n == 40

  # ---- C3: top-level proc as a value matches the direct call ----
  test "C6: top-level proc as value gives same witness as direct call":
    let viaValue  = symexFind(c6ProcAsValue, tLabel("proc-as-value"))
    let viaDirect = symexFind(c6DirectCall, tLabel("direct"))
    check viaValue.status == sxSat
    check viaDirect.status == sxSat
    check viaValue.witness[0] == 5
    check viaDirect.witness[0] == 5
    check viaValue.status == viaDirect.status
    check viaValue.witness[0] == viaDirect.witness[0]

  # ---- C4: bounded filter/map HOF with a closure (inline path) ----
  test "C6: bounded filter HOF with predicate closure → sat (inline path)":
    let r = symexFind(c6FilterInline, tLabel("nonempty"))
    check r.status == sxSat
    check (r.witness[0] > 0) or (r.witness[1] > 0) or (r.witness[2] > 0)

  test "C6: bounded map HOF with mapper closure (ys[0] == a+1)":
    let r = symexFind(c6MapInline, tLabel("mapped"))
    check r.status == sxSat
    check r.witness[0] == 9             ## a+1 == 10 ⇒ a == 9

  # ---- C5: closure equality — distinct sites unequal; same-site equal ----
  test "C6: distinct lambda sites are ALWAYS unequal (==) ⇒ sxUnsat":
    let r = symexFind(c6DistinctSites, tLabel("distinct-sites-equal"))
    check r.status == sxUnsat

  test "C6: same-site alias + same env → equal (svTupleEq branch) ⇒ sxSat":
    let r = symexFind(c6SameSiteEqual, tLabel("same-site-equal"))
    check r.status == sxSat

  # ---- DoD: maxClosureInlineCount override threads through a closure SUT ----
  test "C6: maxClosureInlineCount override still witnesses the captured closure call":
    let r = symexFind(c6Capture, tLabel("captured"), c6Budget)
    check r.status == sxSat
    check r.witness[0] == 5

  # ---- walker version pin (this cycle's bump 8→9) ----
  test "C6: walker version bumped to 9 (single-sourced in canonicalize.nim)":
    check symexWalkerVersion == "9"
