## Phase 15 — Cluster R (FINAL cluster), cycle R12: the cluster CLOSE-OUT.
##
## R12 is the final version bump of the entire Phase 15. It is unusual among the
## cluster-closing cycles: it bumps BOTH maintainer-owned version constants in
## ONE cycle —
##
##   * `symexWalkerVersion`     "9" → "10"  (how the WALKER reasons; the Cluster R
##     heap-semantics close-out — the full R1..R11b machinery is now live), and
##   * `renderAsChoicesVersion` "2" → "3"   (how a SAT witness SERIALISES; the
##     heap-snapshot witness FORMAT extension lands here).
##
## Both constants are single-sourced in `smt/canonicalize.nim` (Invariant 6 / M12
## — no duplicate in runtime.nim), re-exported via `proptest/symex`.
##
## R12 also extends the witness with the **heap-snapshot** field (per
## docs/symex/witness-format-v3.md): an `sxSat` result for a SUT with ref/ptr-
## typed params now carries a populated `heapSnapshot` (per-param `{name, sort,
## value, pointsTo, aliasRef?}`). A NON-heap SUT's result has an EMPTY heapSnapshot
## (the key is ABSENT, not null — backward compat for every prior cluster's
## witness).
##
## DoD (RFC §R12 + reconciliation §F-R): three INDEPENDENT sub-tests
## (sub-test independence per Feas-MED-6 — each stands alone, no shared fixture).
import std/unittest
import std/options
import std/strutils
import proptest/symex

# --- sub-test 2 SUT: a `ref int` param dereffed against a target -------------
proc derefHeap(p: ref int): bool =
  if p != nil:
    if p[] == 42:
      symexTarget("heap")
  result = true

# --- sub-test 3 SUT: a plain `int` param (non-heap) --------------------------
proc plainInt(x: int): bool =
  if x == 7:
    symexTarget("plain")
  result = true

suite "symex Phase 15 R12 — walker 9->10 + rendering 2->3 + heap-snapshot witness":

  test "R12 sub-test 1: BOTH version constants bumped from R12 baseline (walker >=10, rendering >=3)":
    # Pure-constant check — independent of any witness serialisation. R12 bumped
    # walker "9"→"10" and rendering "2"→"3". Subsequent CR-2 consolidated bumps
    # advanced both further ("10"→"11", "3"→"4"); the invariant is that both are
    # strictly greater than their pre-R12 values (compared numerically).
    check parseInt(symexWalkerVersion) >= 10       # R12 bumped to 10; CR-2 bumped to 11
    check parseInt(renderAsChoicesVersion) >= 3    # R12 bumped to 3; CR-2 bumped to 4

  test "R12 sub-test 2: a ref-param sat witness carries a POPULATED heapSnapshot":
    let r = symexFind(derefHeap, tLabel("heap"))
    check r.status == sxSat
    # The heap-snapshot witness format (v3): one entry per ref/ptr param.
    check r.heapSnapshot.len == 1
    let e = r.heapSnapshot[0]
    check e.name == "p"
    check e.sort.len > 0          # a non-empty Ref_<typeId> sort name
    # A non-nil ref: value is the abstract address rendering, pointsTo is set to
    # the modelled pointee value (the deref took 42 on the sat path).
    check e.value != "nil"
    check e.pointsTo.isSome
    # And the witness tuple itself still reconstructs a replayable `ref int`.
    check not r.witness[0].isNil
    check r.witness[0][] == 42

  test "R12 sub-test 3: a non-heap (int) sat witness has NO heapSnapshot (absent)":
    let r = symexFind(plainInt, tLabel("plain"))
    check r.status == sxSat
    # Backward compat: every non-ref/ptr SUT's result has an EMPTY heap snapshot
    # (the v3 `heapSnapshot` key is ABSENT, not null) — prior clusters unchanged.
    check r.heapSnapshot.len == 0
