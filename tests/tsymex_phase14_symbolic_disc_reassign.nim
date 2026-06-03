## Phase 14 cycles A4a + A4b — symbolic-RHS discriminator
## reassignment (ADR-0003 D4).
##
## Pre-A4 the parser handled `obj.kind = staticTagLit` (Phase 11
## cycle 6) and errored on any RHS that wasn't a static enum
## constant. A4a adds `isVariantReassignSymbolic` IR; A4b's
## walker fork emits one path per arm-ordinal disjunct of the
## disc enum's domain, constrains each path with `rhsExpr == k`,
## and PRESERVES the existing per-arm field SymVals (the static-
## tag path's zero-init policy does not apply here per ADR-0003 D4).
##
## SUT shape: a variant `Box`. The procedure reads a fresh
## parameter `t: K`, reassigns `b.kind = t`, then reads
## `b.kind` later and targets a label when the kind matches a
## specific arm. The witness pins `t` to the arm-selecting tag.
import std/unittest
import proptest/symex
import proptest/smt/types

type
  K = enum kA, kB, kC
  Box = object
    case kind: K
    of kA: a: int
    of kB: b: int
    of kC: c: int

proc reassignThenCheck(box: var Box, t: K) =
  # The walker reassigns `box.kind` from a symbolic input. The
  # static-tag path can't model this; it requires A4's symbolic
  # fork. Witness pins `t` to the tag that selects the target arm.
  box.kind = t
  if box.kind == kB:
    symexTarget("kB-reached")

suite "symex Phase 14 A4 — symbolic-RHS disc reassignment":
  test "obj.kind = symbolicVar: walker forks across arms, finds witness":
    let r = symexFind(reassignThenCheck, tLabel("kB-reached"))
    check r.status == sxSat
    # witness[0] is the `box: var Box` param; witness[1] is `t: K`,
    # which is the symbolic RHS the walker forked over. Enum params
    # ride as their BV int representation in the witness — cast back.
    check K(r.witness[1]) == kB
