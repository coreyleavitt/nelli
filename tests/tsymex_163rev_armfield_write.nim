## Issue #163 review finding R17 (High, verified by adversarial verifier) --
## a ranged arm-specific field of a ref-to-variant object that is WRITTEN
## but never READ back still reaches the caller with an out-of-declared-
## -range witness, because the active-arm override at
## `extractFromSymVal`'s `itVariant` arm (`runtime.nim:6657-6668`)
## unconditionally overwrites R3's Part B clamp with a fresh, unclamped
## `heapSelect` of the write-seeded heap.
##
## R3 (commit e5dd226) fixed the READ side (`isArmField` asserts
## `bvRangeConds`, Part A) and clamped every plain/arm field's PROTO
## DEFAULT (Part B) -- but Part B's clamp loop runs BEFORE the active-arm
## override immediately below it, and that override's justifying comment
## ("was actually read via the heap and is therefore already range-safe
## per the D2 fix") is FALSE: `currentVariantHeaps` (`path.heaps`,
## `runtime.nim:7307`) is an unconditional copy of the WHOLE per-path heaps
## table, populated by BOTH the read arm (`runtime_heap.nim:718`, which DOES
## assert `bvRangeConds`, `runtime_heap.nim:740-742`) and the write arm
## (`runtime_heap.nim:1244`/`1252-1254`, which asserts NO range anywhere --
## its own `allocateSym` proto-range conds land in a discarded local
## `scratchPC`, `runtime_heap.nim:1231-1232`, and would bound the proto
## rather than the stored value regardless). The two arms build the
## identical key shape, so the override cannot tell which populated it.
##
## `tsymex_163rev_variant_armfield.nim` (R3's own suite) proves the read
## side and the never-read-anywhere proto-default side. `tsymex_a2_
## refvariant_fields.nim:140-183` (`wrongArmWrite`) proves a WRITE-only arm
## field walks end to end for a plain `int` field. This file is the field
## those two never cover together: a RANGED arm field that is WRITTEN and
## never read back, reached via a disc-only target -- exactly the shape
## the active-arm override clobbers.
##
## The verdict below is genuinely `sxSat` -- "hit" IS reachable for any
## `x, y` with `x + y` in `[1, 100]`. The bug is ONLY that the reported
## witness's `v` field can be reconstructed outside `[1, 100]`, which
## raises a real `RangeDefect` materializing it in the caller's own
## process. The fix is a WITNESS CLAMP at the override site, mirroring
## Part B's loops -- NOT a range constraint at the write site, which would
## falsely tell the solver an out-of-range assignment cannot happen and
## hide the (separate, pre-existing) missing assignment-time `RangeDefect`
## raise fork.
##
## House rule: every symbolic expectation is paired with an ORACLE -- the
## same computation run for real in Nim, in this file -- exactly how
## `tsymex_163rev_table_elem.nim` and R3's own Part B test pin their cases.

import std/unittest
import std/strutils
import nelli/smt/canonicalize
import nelli/symex

type
  # `nkB` declared FIRST so `low(NKind) == nkB`: `new(Node)`'s default
  # zero-init lands on the `discard` arm, which has no field needing a
  # default value. If the ranged arm were `low(NKind)`, Nim would refuse to
  # compile the witness-rendering macro's `new(Node)` call outright (`range
  # [1..100]` has no valid zero default) -- a compile-time artifact of this
  # test's own type, unrelated to the engine defect under test.
  NKind = enum nkB, nkA
  Node = object
    case kind: NKind
    of nkA: v: range[1..100]
    of nkB: discard

proc mkRange1to100(x: int): range[1..100] = range[1..100](x)

# ---- Part 1: the headline -- write-only ranged arm field, disc-only target -
# `p.v` is WRITTEN (`x + y`, unconstrained) but never READ back anywhere on
# any path -- only the discriminator is compared. The write-arm heap key is
# populated (`currentVariantHeaps` gets an entry) but with no range
# assertion anywhere, so the active-arm override's `heapSelect` extracts an
# unclamped value straight from an unconstrained sum -- Z3 commonly
# completes this to 0, outside `[1, 100]`.
proc writeOnlyArmField(p: ref Node, x, y: int) =
  if p != nil:
    case p.kind
    of nkA: p.v = x + y
    of nkB: discard
    if p.kind == nkA:
      symexTarget("hit")

# ---- Part 2: non-regression -- a field that IS read back still reports its
# real solved value, undamaged by the clamp (mirrors A2 Slice 3's
# `writeReadSameRef`, with a ranged field instead of a plain `int`).
proc writeThenReadSameRef(p: ref Node) =
  if p != nil and p.kind == nkA:
    p.v = 55
    if p.v == 55:
      symexTarget("readback")

suite "#163 review R17 -- the oracle":

  test "Nim itself refuses an out-of-declared-range arm-field value":
    expect RangeDefect:
      discard mkRange1to100(0)
    expect RangeDefect:
      discard mkRange1to100(101)
    check mkRange1to100(50) == 50

suite "#163 review R17 -- a write-only ranged arm field's witness stays inside its declared range":

  test "the disc-only target's write-only arm field extracts in range":
    ## The crash class. `p.v` is written but never read back anywhere --
    ## only `p.kind == nkA` is compared -- so the verdict is correctly
    ## `sxSat` (any x, y with x + y in [1, 100] reaches "hit"); only the
    ## WITNESS's `v` field was ever liable to fall outside [1, 100].
    let r = symexFind(writeOnlyArmField, tLabel("hit"))
    check r.status == sxSat
    check not r.witness[0].isNil
    let node = r.witness[0][]
    check node.kind == nkA
    check node.v in 1 .. 100
    discard mkRange1to100(node.v)  ## does not raise -- the point of the fix

suite "#163 review R17 non-regression -- a field that IS read back still solves correctly":

  test "read-after-write on the same ref reports the real observed value":
    let r = symexFind(writeThenReadSameRef, tLabel("readback"))
    check r.status == sxSat
    check not r.witness[0].isNil
    let node = r.witness[0][]
    check node.kind == nkA
    check node.v == 55


suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    ## One bump covers R1/R2/R3/R4/R15 -- every one a verdict change, so a
    ## cache entry written under any one of them can replay a wrong verdict
    ## under the others. R17 is witness-only (no verdict changes and no
    ## walker-semantics change), so it does not add its own bump; this pin
    ## only confirms the floor the round already established.
    check parseInt(symexWalkerVersion) >= 135
