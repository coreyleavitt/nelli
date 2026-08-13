## Phase 15 — Cluster R (FINAL cluster), cycle R1: ref sort introduction +
## heap deref (the first REAL heap semantics). Promotes R1a's `itRef`/`itPtr`/
## `isDeref` stubs to live Z3 semantics:
##
##   * Per-walker `Ref_T` uninterpreted sort (`mkUninterpretedSort(ctx,
##     "Ref_" & typeId)`), cached in `WalkerStatics.refSorts`.
##   * Per-path `Z3Array[Ref_T, T_sym]` heap variable in `path.heaps[typeId]`.
##   * `p[]` (an `isDeref`) lowers to a GROUND `Z3_mk_select(heap, p)` — a
##     decidable array read over the uninterpreted address sort (NO universal
##     quantifier — the G4 hang lesson). The solver picks `heap[p] == 42`.
##   * `nil_<typeId>` distinguished constant cached in `WalkerStatics.nilConsts`.
##
## See ADR-0010 (logical-heap model) and RFC §R1. R1 is ADDITIVE under walker
## version "9" (no bump; Cluster R bumps at R12).
import std/unittest
import nelli/symex

# The canonical R1 SUT: a `ref int` param, dereferenced and compared. The deref
# `p[]` is the first real heap read. The heap is a free `Z3Array[Ref_T, BV64]`,
# so the solver is free to pick `heap[p] == 42`.
proc derefIs42(p: ref int): bool =
  if p != nil:
    if p[] == 42:
      symexTarget("sat")
  result = true

suite "symex Phase 15 R1 — ref sort + heap deref (Z3Array[Ref_T,T] select)":

  test "R1: SUT with ref int param materialises ref sort and deref returns sat witness":
    # The deref must NOT crash and must NOT degrade to sxUnknown — the ground
    # array select over the uninterpreted Ref_T sort is decidable.
    let r = symexFind(derefIs42, tLabel("sat"))
    check r.status == sxSat
    # The witness reader (emitTyAndReader itRef) reconstructs a `ref int` whose
    # deref equals the value `p[]` took in the model — exactly the satisfying
    # assignment (`p[] == 42`). C7 / Breadth-CRIT-1: not a silent empty reader.
    let p = r.witness[0]
    check not p.isNil
    check p[] == 42

  test "R1: same ref dereffed twice with contradictory values is unsat":
    # `p[] == 42 and p[] == 43` — the SAME ref into the SAME (free) heap array
    # selects the SAME value, so the conjunction is unsatisfiable. This proves
    # the deref is a genuine functional read (not a fresh symbol each time).
    proc contradiction(p: ref int): bool =
      if p != nil:
        if p[] == 42 and p[] == 43:
          symexTarget("both")
      result = true
    let r = symexFind(contradiction, tLabel("both"))
    check r.status == sxUnsat
