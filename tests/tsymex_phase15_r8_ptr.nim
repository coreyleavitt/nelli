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
##   * Pointer arithmetic `inc(p)`/`dec(p)` with a `ptr`-typed operand →
##     `SymexErrorInfo{kind: hePtrArith, severity: sevError}` (HALTING) →
##     sxUnknown (Invariant 3). The address is NOT modeled. `inc`/`dec` on an
##     INT is UNAFFECTED.
##
## See ADR-0010 (logical-heap model). R8 is ADDITIVE under walker version "9"
## (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

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

# R8 SUT 2: pointer arithmetic via `inc` on a `ptr` operand — unmodelable
# address → hePtrArith (sevError) → sxUnknown. Stock Nim has NO `inc(p: ptr T)`
# (pointer arithmetic is cast-based), so to exercise the name+ptr-operand guard
# with a type-checking SUT we provide a local `inc`/`dec` ptr overload. The
# parser's R8 guard keys on the proc NAME (`inc`/`dec`) + a ptr-typed operand
# and fires BEFORE the user overload is ever registered/walked.
proc inc(p: ptr int) = discard
proc dec(p: ptr int) = discard

proc ptrInc(p: ptr int) =
  inc(p)
  symexTarget("any")

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

  test "R8.2: inc(p) on a ptr operand → sxUnknown + hePtrArith (sevError)":
    let r = symexFind(ptrInc, tLabel("any"))
    check r.status == sxUnknown
    check r.errors.len > 0                   # no silent empty-errors sxUnknown
    check r.errors[0].kind == hePtrArith
    check r.errors[0].severity == sevError

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
