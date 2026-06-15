import std/unittest
import proptest/smt/runtime

# Phase 15 — H1: Path heap-state fields + deep-copy fork contract
# (see docs/symex/RFC-phase15-reconciliation.md §F / Cluster H, ADR-0010).
#
# `Path` is a private `ref object` in runtime.nim, so its three new heap-state
# fields (heaps / heapDepth / allocCounters) and the fork-site deep-copy
# contract are exercised through two exported test hooks. The hooks live in
# runtime.nim (the only module that can name `Path`); they construct a Path,
# read the fields, and run the parent/child fork-isolation scenario.
#
# H1 is pure infrastructure: the fields are inert (empty) until Cluster R fills
# them. This test asserts (1) the fields exist and (2) deepCopyHeapState gives
# fork isolation — mutating a forked child's heap does not bleed into the parent.

suite "symex Phase 15 — H1 Path heap-state fields":

  test "H1: Path carries heaps/heapDepth/allocCounters fields":
    check h1PathHasHeapFields()

  test "H1: fork-site deep-copy: mutating child heaps does not mutate parent":
    check h1ForkIsolation()
