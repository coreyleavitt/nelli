## Phase 4 — out-of-bounds target via `tIndexError()`.
##
## The walker forks at every `arr[i]` access on a symbolic `i`. The
## in-bounds path adds `0 ≤ i < N` to the path-condition; the OOB
## path adds the negation, and under the `tIndexError` target the
## OOB path's pc is solved for a falsifying witness.
import std/unittest
import nelli/symex

proc unsafeRead(arr: array[5, int], i: int) =
  let v = arr[i]
  discard v   ## suppress unused warning

suite "symex Phase 4 — OOB detection":
  test "tIndexError finds an OOB index":
    ## Phase 16 D1a: sxSat→sxRaised; witness moves to raisedWitness.
    let r = symexFind(unsafeRead, tIndexError())
    check r.status == sxRaised
    check r.raisedTypeId == "IndexDefect"
    let i = r.raisedWitness[1]
    check (i < 0 or i >= 5)
