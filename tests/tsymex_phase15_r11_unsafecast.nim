## Phase 15 — Cluster R (FINAL cluster), cycle R11: unsafe cast / addr
## classification. Per RFC §F Cluster R "R11" and RFC §R11 (Open Question 7,
## CLOSED):
##
##   * `cast[ptr T](addr x)` and similar unsafe address-taking patterns
##     (`addr x`, `unsafeAddr x` feeding a pointer materialisation) are NOT
##     modeled — the resulting raw machine address is unmodelable in the
##     logical-heap model (the heap is keyed by an abstract `Ref_T` value, not
##     a numeric address). They are classified as `sxUnknown` with a
##     `SymexErrorInfo{kind: heUnsafeCast, severity: sevError}` — a classified,
##     machine-readable HALT (Invariant 3: no silent fallbacks).
##   * The parser emits an `isUnsafeCast` IR node (`mkUnsafeCast(reason)`); the
##     walker raises the classified `heUnsafeCast` (the established
##     classify→sxUnknown path, identical to R8's `hePtrArith` mechanism).
##   * GUARD: detection keys ONLY on a genuine pointer-materialisation —
##     `cast[ptr T]` (a `nnkCast` to a `ptr` target) and `addr`/`unsafeAddr`
##     (`nnkAddr`). A normal SUT WITHOUT casts must still symex natively and is
##     NEVER spuriously routed to `heUnsafeCast`.
##
## R11 is ADDITIVE under walker version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import nelli/symex

# Canonical R11 SUT: `cast[ptr int](addr x)` then a deref `p[]`. The cast is an
# unmodelable pointer materialisation → heUnsafeCast → sxUnknown.
proc castPtr(x: int) =
  let p = cast[ptr int](addr x)
  if p[] == 1:
    symexTarget("hit")

# Bare `addr` to a ptr binding — same classification (heUnsafeCast).
proc bareAddr(x: int) =
  let p = addr x
  if p[] == 2:
    symexTarget("hit")

# `unsafeAddr` to a ptr binding — same classification. (`unsafeAddr` lowers to
# the same `nnkAddr` node as `addr` in the typed AST.)
proc unsafeAddrSut(x: int) =
  let p = unsafeAddr x
  if p[] == 3:
    symexTarget("hit")

# CONTROL: a normal SUT WITHOUT any cast/addr. Must still symex natively to
# sxSat and carry NO heUnsafeCast — proves the detection does not over-trigger.
proc noCast(x: int) =
  if x == 5:
    symexTarget("hit")

suite "symex Phase 15 R11 — unsafe cast / addr classification (heUnsafeCast)":

  test "R11.1: cast[ptr int](addr x) → sxUnknown + heUnsafeCast (sevError)":
    let r = symexFind(castPtr, tLabel("hit"))
    check r.status == sxUnknown
    check r.errors.len > 0                 # no silent empty-errors sxUnknown
    var sawUnsafeCast = false
    for e in r.errors:
      if e.kind == heUnsafeCast:
        sawUnsafeCast = true
        check e.severity == sevError
    check sawUnsafeCast

  test "R11.2: bare `addr x` to a ptr → sxUnknown + heUnsafeCast":
    let r = symexFind(bareAddr, tLabel("hit"))
    check r.status == sxUnknown
    var sawUnsafeCast = false
    for e in r.errors:
      if e.kind == heUnsafeCast: sawUnsafeCast = true
    check sawUnsafeCast

  test "R11.3: `unsafeAddr x` to a ptr → sxUnknown + heUnsafeCast":
    let r = symexFind(unsafeAddrSut, tLabel("hit"))
    check r.status == sxUnknown
    var sawUnsafeCast = false
    for e in r.errors:
      if e.kind == heUnsafeCast: sawUnsafeCast = true
    check sawUnsafeCast

  test "R11.4: a normal no-cast SUT still works (sxSat, NO heUnsafeCast)":
    let r = symexFind(noCast, tLabel("hit"))
    check r.status == sxSat
    for e in r.errors:
      check e.kind != heUnsafeCast
