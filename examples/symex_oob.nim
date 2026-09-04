## examples/symex_oob.nim
##
## Finding an array out-of-bounds access symbolically. This is the
## `tIndexError` target — the second of symex's three target kinds.
##
## Symex forks at every `arr[i]` on a symbolic index. The in-bounds
## branch gets `0 ≤ i < N` added to the path condition; the OOB
## branch gets the negation. Under `tIndexError`, the walker solves
## the OOB branch's path condition for a witness.
##
## Since Phase 15 (E2a/E2b) an out-of-bounds access is modelled as a
## *raise path* rather than a plain satisfying assignment, so the
## verdict is `sxRaised` carrying `raisedTypeId == "IndexDefect"` and
## the input in `raisedWitness` (a distinct field from `sxSat`'s
## `witness`, since Nim forbids repeating a field name across variant
## branches). This file asserted the old `sxSat` shape and had been
## failing at runtime ever since -- it still *compiled*, which is why
## the RFC-0010 review that compiled every example did not catch it.
## `scripts/check-examples.sh` runs them.
##
## What this finds is *automatically*: a value of `i` that drives
## the array access out of bounds. You didn't have to enumerate
## indices or guess.

import std/[strformat]
import nelli/symex

proc readSlot(arr: array[10, int], i: int) =
  # The walker A-normalises this access. The OOB path-condition is
  # `i < 0 or i >= 10` (Nim's array bound). Under tIndexError, that
  # path condition is solved for a witness.
  let v = arr[i]
  discard v

let r = symexFind(readSlot, tIndexError())
doAssert r.status == sxRaised,
  "expected a modelled raise — `i = -1` (or `i >= 10`) drives an OOB access"
doAssert r.raisedTypeId == "IndexDefect",
  "the OOB path raises IndexDefect, not " & r.raisedTypeId

let (_, i) = r.raisedWitness
echo &"symex found OOB witness: i = {i}"
doAssert i < 0 or i >= 10,
  "witness must lie outside [0, 10)"

# Sanity-check the witness raises IndexDefect at runtime.
assertCoveredBy(readSlot, tIndexError())
echo "assertCoveredBy: invoking readSlot on the witness raises IndexDefect — good."
