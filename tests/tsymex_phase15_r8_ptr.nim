## Phase 15 — Cluster R (FINAL cluster), cycle R8: `ptr T` family + pointer
## arithmetic. Per RFC §F Cluster R "R8":
##
##   * `ptr T` uses the SAME heap model as `ref T` — `svPtr`'s deref/store route
##     through `path.heaps[typeId]` exactly like `svRef` (same `Ref_T` sort,
##     `Z3_mk_select`/`Z3_mk_store`). `ptr int` deref `p[] == 7` works like
##     `ref int`. (Confirmed already-wired since R1/R4 — both deref arms case on
##     `of svPtr: refSV.ptrAst`.)
##   * `hePtrFamily` hint (sevHint, NON-halting): a successfully-modeled `ptr T`
##     witness carries a `SymexErrorInfo{kind: hePtrFamily}` so consumers can
##     distinguish unmanaged ptr from managed ref. A parallel `ref T` SUT
##     produces NO such entry.
##   * Pointer arithmetic. R8 classified `inc(p)`/`dec(p)` on a `ptr` operand
##     `hePtrArith`. RFC-0005 S8c retired that kind: `system.inc` takes an
##     Ordinal, so an `inc(p: ptr T)` exists only as a USER overload, and S8c
##     walks a user routine instead of name-matching it. Real pointer
##     arithmetic goes through `cast` (`cast[ptr T](cast[int](p) + k)`), which
##     records `heUnsafeCast` (R11) -- pinned below through that path.
##     `inc`/`dec` on an INT is UNAFFECTED.
##
## See ADR-0010 (logical-heap model). R8 is ADDITIVE under walker version "9"
## (no bump; Cluster R bumps at R12).
import std/unittest
import nelli/symex

# Canonical R8 SUT 1: a `ptr int` param dereferenced and compared — same heap
# model as `ref int`, so the deref is decidable and the solver picks heap[p]==7.
proc ptrDerefIs7(p: ptr int) =
  if p != nil:
    if p[] == 7:
      symexTarget("hit")

# Parallel `ref int` SUT — same shape, but managed: NO hePtrFamily hint.
proc refDerefIs7(p: ref int) =
  if p != nil:
    if p[] == 7:
      symexTarget("hit")

# R8 SUT 2: a USER `inc` overload on a `ptr` operand. Stock Nim has NO
# `inc(p: ptr T)`, so this no-op proc is ordinary user code; RFC-0005 S8c
# walks it (the retired R8 guard name-matched it as pointer arithmetic and
# never looked at its empty body).
proc inc(p: ptr int) = discard
proc dec(p: ptr int) = discard

proc ptrInc(p: ptr int) =
  inc(p)
  symexTarget("any")

# R8 SUT 3: REAL pointer arithmetic -- an integer offset through `cast`.
proc ptrCastArith(p: ptr int) =
  if p != nil:
    let q = cast[ptr int](cast[int](p) + 8)
    if q[] == 7:
      symexTarget("hit")

suite "symex Phase 15 R8 — ptr T heap model + pointer-arith classification":

  test "R8.1: ptr int deref works like ref int (sxSat) + carries hePtrFamily hint":
    let r = symexFind(ptrDerefIs7, tLabel("hit"))
    check r.status == sxSat
    # The ptr deref routes through the SAME heap as a ref deref.
    var sawPtrFamily = false
    for e in r.errors:
      if e.kind == hePtrFamily:
        sawPtrFamily = true
        check e.severity == sevHint
    check sawPtrFamily

  test "R8.1b: parallel ref int SUT is sxSat with NO hePtrFamily hint":
    let r = symexFind(refDerefIs7, tLabel("hit"))
    check r.status == sxSat
    for e in r.errors:
      check e.kind != hePtrFamily

  test "R8.2: a user no-op inc(p: ptr int) is walked: sxSat, no error recorded":
    let r = symexFind(ptrInc, tLabel("any"))
    check r.status == sxSat
    for e in r.errors:
      check e.severity != sevError
      check e.kind != hePtrArith

  test "R8.2b: real pointer arithmetic (cast offset) → sxUnknown + heUnsafeCast":
    let r = symexFind(ptrCastArith, tLabel("hit"))
    check r.status == sxUnknown
    var sawCast = false
    for e in r.errors:
      check e.kind != hePtrArith
      if e.kind == heUnsafeCast and e.severity == sevError: sawCast = true
    check sawCast

  test "R8.3: inc/dec on an INT is unaffected (no hePtrArith)":
    # The pointer-arith guard must key on a ptr-typed operand ONLY. A normal
    # int `inc`/`dec` must symex exactly as before.
    proc incInt(x: int) =
      var i = x
      inc(i)
      dec(i)
      if i == x:
        symexTarget("back")
    let r = symexFind(incInt, tLabel("back"))
    check r.status == sxSat
    for e in r.errors:
      check e.kind != hePtrArith
