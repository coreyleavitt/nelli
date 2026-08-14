## RFC-parser-normalization (#146), Cluster C, slice C2 — dedicated pin for
## the descriptor-backed static-param derivation (code-review finding L7).
##
## ----------------------------------------------------------------------------
## Why this file exists
## ----------------------------------------------------------------------------
## C2 (`428d99c`) threaded `resolveGenericDescriptor` into THREE dual-location
## consumers that used to re-walk `nnkIdentDefs` independently:
## `gatherTypeSubst`, `parseCalleeImpl`, and `staticParamNames`
## (`src/nelli/smt/dsl_parser.nim`). The review tally undercounted the third
## — `staticParamNames` already delegated the `impl[2]`-vs-`impl[5][1]`
## LOCATION lookup to `genericParamsNode` pre-C2, but still re-walked
## `nnkIdentDefs` itself to test `isStatic`; C2 rebased that walk onto
## `resolveGenericDescriptor(impl).params` too. Coverage for this rebase was
## only INDIRECT — `tsymex_phase15_g7_static_param.nim` (pre-existing, still
## green) and `tsymex_phase15_g10_smoke.nim` (pre-existing, independently
## known-red per #152) — neither is a dedicated pin for the rebase itself.
## This file is that dedicated pin.
##
## ----------------------------------------------------------------------------
## What's pinned, and what's deliberately not attempted
## ----------------------------------------------------------------------------
## `staticParamNames` filters `resolveGenericDescriptor(impl).params` on
## `isStatic`, keeping only matching NAMEs. A regression that swapped the
## per-param name/isStatic pairing (an off-by-one, or a positional
## assumption reintroduced in some future edit) would misattribute
## `isStatic` to the wrong generic param whenever a routine mixes a static
## and an ordinary (type) generic param. Both cells below pin exactly that:
## a proc with one `static[int]` param and one ordinary type param, in BOTH
## relative orders, driven purely through the PUBLIC `symexFind` entry (no
## internals poked) — mirroring `g7_static_param`'s pattern of proving
## per-instantiation substitution via a WITNESSED, position-dependent array
## index rather than asserting an internal key string.
##
## `genericParamsNode`'s doc comment (dsl_parser.nim :5096) also names a
## SECOND dual location: `impl[5][1]` (a "typed form" shape), alongside the
## primary `impl[2]` ("untyped form") location C2's own coverage
## (`g7_static_param`, this file) exercises. Per RFC-parser-normalization
## round-1/round-2 probing notes and `g7_static_param`'s own REAL-AST
## FINDINGS section, every static-param SUT reachable through the public
## `symexFind`/generic-proc-call entry — there and here — lands on the
## `impl[2]` branch; nothing in this repo's test corpus (including the
## `func`-vs-`proc` layout probe in `tsymex_funcdef_callee.nim`) demonstrates
## a surface construct that lands on `impl[5][1]` instead. Per this cycle's
## instructions, that second branch is covered only if `g7`'s pattern shows
## how to reach it through the public entry — it does not, so this file does
## not attempt a dedicated SUT for it; `genericParamsNode` falling through to
## `impl[5][1]` stays defensive/probed-but-unexercised, same as pre-C2.
##
## ----------------------------------------------------------------------------
## RED-proof
## ----------------------------------------------------------------------------
## Each `check` below is a direct behavioral consequence of a specific
## generic param's `isStatic` bit landing on the right NAME: flip either
## SUT's expected verdict (`sxSat` -> `sxUnsat`) or either witnessed-index
## inequality and the test fails immediately — there is no vacuous
## true/true shape here (both mixed SUTs require BOTH conjuncts, at
## DIFFERENT array sizes, to be satisfied simultaneously). This was run
## once with `check r.status == sxUnsat` (deliberately wrong) in place of
## `check r.status == sxSat` for `twoMixedOrders`, confirmed RED, then
## reverted to the correct assertion below.
##
## Walker version pin: "73". C2 (`428d99c`) is explicitly behavior-identical
## (no `symexWalkerVersion` bump); this file pins a tolerant floor, not the
## bump itself.

import std/[unittest, strutils]
import nelli/symex
import nelli/smt/canonicalize

# ===========================================================================
# SUTs
# ===========================================================================

# Cell 1: static param FIRST, ordinary generic param SECOND.
# `N` is static[int] (position 0); `T` is an ordinary type param (position 1).
# `x[N-1] > y` witnesses N's substituted VALUE via the last array index, same
# proof shape as g7's `lastPos`.
proc mixedFirstStatic[N: static int, T](x: array[N, int], y: T): bool =
  x[N - 1] > y

# Cell 2: ordinary generic param FIRST, static param SECOND — the REVERSED
# relative order from `mixedFirstStatic`. If `staticParamNames` (or its
# `resolveGenericDescriptor` feed) ever mis-paired position with name, this
# proc's `N` would be misread as non-static (breaking the array[N,int]
# dimension substitution `gatherTypeSubst` needs to size the formal) or `T`
# would be misread as static (no such crash mode exists for a plain type
# param, but the name/isStatic pairing would still be provably wrong).
proc mixedSecondStatic[T; N: static int](y: T, x: array[N, int]): bool =
  x[N - 1] > y

# Driver: instantiates `mixedFirstStatic` at N=3 and `mixedSecondStatic` at
# N=5 — DIFFERENT static values in DIFFERENT relative positions — so a
# correct run must witness a3[2] and b5[4] independently. A name/isStatic
# mispairing in EITHER proc would either misclassify the array-dim
# substitution (wrong/unknown verdict) or collapse both instantiations onto
# a shared bare key (G1a-class collision), not this precise pair of
# witnessed indices.
proc twoMixedOrders(a3: array[3, int], b5: array[5, int], t1: int, t2: int) =
  if mixedFirstStatic(a3, t1) and mixedSecondStatic(t2, b5):
    symexTarget("mixed")

# Cell 3: a SCALAR static param (no array-dim formal — the `instKeyFor`
# bodyHash-discrimination branch, `typeSubst.len == 0`) mixed with an
# ordinary generic param, pinning the same name/isStatic derivation on the
# OTHER of the two consumer shapes `staticParamNames` feeds (`instKeyFor`'s
# scalar-static arm vs `gatherTypeSubst`'s array-dim arm above).
proc scalarMixed[B: static bool; T](y: T): bool =
  (y > 0) == B

proc twoScalarMixed(p: int, q: int) =
  # scalarMixed[true, int](p) ⇒ p > 0 ; scalarMixed[false, int](q) ⇒ q <= 0.
  # Opposite polarity per instantiation proves B was substituted
  # per-instantiation (not shared/collapsed), same proof shape as g7's
  # `gate`. Both generic params are given explicitly (Nim requires either
  # all-explicit or all-inferred once any bracket is used).
  if scalarMixed[true, int](p) and scalarMixed[false, int](q):
    symexTarget("scalar_mixed")

suite "symex Phase 15 C2 — descriptor-backed static-param derivation (finding L7)":
  test "static-first / type-second and type-first / static-second both dispatch correctly":
    let r = symexFind(twoMixedOrders, tLabel("mixed"))
    check r.status == sxSat
    check r.witness[0][2] > r.witness[2]   ## a3[N-1] = a3[2] > t1
    check r.witness[1][4] > r.witness[3]   ## b5[N-1] = b5[4] > t2

  test "scalar static[bool] mixed with an ordinary generic param dispatches per-value":
    let r = symexFind(twoScalarMixed, tLabel("scalar_mixed"))
    check r.status == sxSat
    check r.witness[0] > 0     ## scalarMixed[true]:  p > 0
    check r.witness[1] <= 0    ## scalarMixed[false]: q <= 0

  test "walker version pin: symexWalkerVersion floor >= 73 (C2 landed behavior-identical at 73)":
    ## C2 (`428d99c`) is explicitly behavior-identical (no SW bump) — this
    ## pin documents the floor this file was authored against, not a bump.
    check parseInt(symexWalkerVersion) >= 73
