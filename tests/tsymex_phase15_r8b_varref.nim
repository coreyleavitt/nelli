## Phase 15 — Cluster R (FINAL cluster), cycle R8b: `var ref T` parameter handling.
##
## A callee with a `var ref T` parameter that REBINDS it (`p = new int`) must
## write the new binding back to the caller's env after the call returns, so the
## caller's continuation sees the rebound ref (not the ref it passed in).
##
## R8b extends the #140 `isVar` write-back machinery (which already propagates a
## callee's final binding for a `var` formal back into the caller's env at the
## `isCall` return — see `varArgs` in `runtime.nim`) to `svRef`/`svPtr` formals.
## The write-back copies `cp.env[formalName]` (the callee's FINAL svRef binding —
## after the `p = new int` rebind) back to the caller var; the R1b heap return-
## merge (heaps-REPLACE + allocCounters-max) brings the rebound ref's heap entry
## (`p[] = 99`) back out with it. So the caller, reading the rebound `q[]`, sees
## 99.
##
## DoD (RFC §R8b + reconciliation §F-R):
##   `proc rebind(p: var ref int) = (p = new int; p[] = 99)`
##   `proc f() = (var q = new int; q[] = 0; rebind(q); if q[] == 99: target)`
##   → symexFind(f, tLabel("rebound")) → sxSat   (FULL write-back)
##
## R8b is ADDITIVE under walker version "9" (no bump; Cluster R bumps at R12).
## See ADR-0010 (logical-heap model) and RFC §R8b.
import std/unittest
import proptest/symex

# The callee REBINDS its `var ref int` param to a freshly allocated cell and
# writes 99 into it. With full write-back, the caller's `q` ends up pointing at
# THIS new cell (value 99), not the original `q` cell it allocated (value 0).
proc rebind(p: var ref int) =
  p = new int
  p[] = 99

proc f() =
  var q = new int
  q[] = 0
  rebind(q)
  if q[] == 99:
    symexTarget("rebound")

# PROOF the write-back is load-bearing: the caller's ORIGINAL cell had value 0.
# If the rebind did NOT write back (q still pointed at the original cell), `q`
# would read 0 — and the rebound cell's 99 is on a DIFFERENT (fresh, distinct)
# address, so `q[] == 0` would have to hold. The write-back makes `q` point at
# the rebound cell (value 99, distinct from the 0-cell), so AFTER the call
# `q[] == 0` is now UNSAT — it is the rebound 99-cell, provably not the 0-cell.
proc fStale() =
  var q = new int
  q[] = 0
  rebind(q)
  if q[] == 0:
    symexTarget("stale")

suite "symex Phase 15 R8b — var ref T parameter handling (rebind write-back)":

  test "R8b: callee rebinds `var ref int` param; caller sees the rebound cell (q[]==99) → sxSat":
    let r = symexFind(f, tLabel("rebound"))
    check r.status == sxSat

  test "R8b: write-back is load-bearing — q is the rebound cell, not the stale 0-cell (q[]==0 → sxUnsat)":
    # The fresh `new int` inside rebind is distinct (assertFreshness) from the
    # caller's original 0-valued cell. After write-back `q` IS the rebound cell
    # (value 99), so `q[] == 0` is impossible. Had the rebind not propagated,
    # `q` would still be the 0-cell and this would be sxSat — the sxUnsat verdict
    # PROVES the new binding (not just the heap value) crossed back to the caller.
    let r = symexFind(fStale, tLabel("stale"))
    check r.status == sxUnsat
