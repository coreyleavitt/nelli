## Phase 15 — Cluster R (FINAL cluster), cycle R5: nil handling (nil-access defect).
##
## `nil` is the per-ref-sort distinguished constant `nilConst(Ref_T)` (allocated
## at R1 and cached in `WalkerStatics.nilConsts`). R5 makes nil OBSERVABLE and
## models the nil-access DEFECT:
##
##   * `p == nil` is a ground Z3 equality on `Ref_T`-sorted terms (decided by
##     path-sat as usual) — `nil` lowers to an svRef carrying the nilConst.
##   * `p[]` (read OR write) of a possibly-nil ref FORKS the deref:
##       - the NON-NIL path asserts `p != nil` and continues normally (the R1/R4
##         select/store);
##       - the NIL path asserts `p == nil`, is a NilAccessDefect finding (a Nim
##         Defect — `sxRaised("NilAccessDefect")` conceptually), and TERMINATES.
##     The nil-path finding is GATED on the new `tNilAccess()` target kind: under
##     `tLabel(...)` only the non-nil path can satisfy the label; under
##     `tNilAccess()` the nil path surfaces the defect witness (`p == nil`).
##   * Nil-fork SHORT-CIRCUIT (Depth-LOW-D4 / path-explosion guard): before
##     emitting the nil sub-path, a SHALLOW AST scan of `path.pc` looks for a
##     constraint implying `p != nil` — either `not(eq(p, nil))` (an explicit
##     `p != nil`, also what `new`/`assertFreshness` asserts) or `eq(p, ref_T_N)`
##     (an alias to a fresh `new`-allocated ref). If found, the nil path is UNSAT
##     by construction and the fork is SKIPPED entirely (sound; no Z3 check-sat).
##     A freshly `new`-allocated ref dereffed therefore NEVER forks a nil path.
##
## DoD (RFC §R5 + reconciliation §F-R5):
##   1. `proc f(p: ref int) = if p[] == 1: symexTarget("hit")`:
##        tLabel("hit")  → sxSat (non-nil path finds p[]==1)
##        tNilAccess()   → sxSat (nil path found the defect; witness p == nil)
##   2. SHORT-CIRCUIT: `proc g() = (let p = new int; if p[] == 1: symexTarget("hit"))`
##        tNilAccess()   → sxUnsat / no nil finding (p is freshly allocated →
##                         provably non-nil → nil fork SKIPPED). PROVES the
##                         short-circuit fires.
##   3. `p == nil` observable: `proc h(p: ref int): bool = p == nil`
##        tLabel reaching a `p == nil` branch → sxSat (p can be nil).
##
## R5 is ADDITIVE under walker version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import proptest/symex

# --- DoD 1: deref of a possibly-nil ref forks --------------------------------
proc f(p: ref int) =
  if p[] == 1:
    symexTarget("hit")

# --- DoD 2: short-circuit — freshly allocated ref is provably non-nil ---------
proc g() =
  let p = new int
  if p[] == 1:
    symexTarget("hit")

# --- DoD 3: `p == nil` is observable -----------------------------------------
proc h(p: ref int) =
  if p == nil:
    symexTarget("isNil")

# A `new`-allocated ref is provably NON-nil, so `p == nil` is unreachable.
proc hFresh() =
  let p = new int
  if p == nil:
    symexTarget("isNil")

suite "symex Phase 15 R5 — nil handling (nil-access defect)":

  test "R5 test 1a: deref non-nil path finds p[]==1 → tLabel sxSat":
    let r = symexFind(f, tLabel("hit"))
    check r.status == sxSat

  test "R5 test 1b: deref nil path is the defect → tNilAccess sxSat (witness p == nil)":
    let r = symexFind(f, tNilAccess())
    check r.status == sxSat

  test "R5 test 2: SHORT-CIRCUIT — freshly new-allocated ref does NOT fork a nil path → tNilAccess sxUnsat":
    let r = symexFind(g, tNilAccess())
    check r.status == sxUnsat

  test "R5 test 3a: `p == nil` observable — p can be nil → sxSat":
    let r = symexFind(h, tLabel("isNil"))
    check r.status == sxSat

  test "R5 test 3b: `p == nil` on a fresh `new` ref is unreachable → sxUnsat":
    let r = symexFind(hFresh, tLabel("isNil"))
    check r.status == sxUnsat
