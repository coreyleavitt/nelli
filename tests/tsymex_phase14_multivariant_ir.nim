## Phase 14 cycle A1a — `itMultiVariant` IR extension.
##
## Pre-Phase-14, multi-`nnkRecCase` objects were rejected at parse
## time. ADR-0003 D1 adds a new IR kind `itMultiVariant` that
## represents them as a list of `VariantAxis` entries, one per
## `nnkRecCase` block. The single-`nnkRecCase` case keeps using
## `itVariant`; the new kind exists alongside.
##
## This cycle's slice is the IR addition + stubs. Parsing,
## walking, and witness construction land in A1b–A1d.
##
## The RED test verifies the IR addition is observable through
## the canonical encoding: a hand-built `itMultiVariant` produces
## a key distinct from a flat single-axis `itVariant` carrying the
## same flattened arms.
import std/unittest
import nelli/smt/[types, canonicalize]

suite "symex Phase 14 cycle A1a — itMultiVariant IR":
  test "itMultiVariant canonicalize key differs from flat itVariant":
    # Single-axis itVariant: `case kind: int of 0: a: int; of 1: b: int`.
    let singleAxis = tVariant(
      objectName = "Foo", discName = "kind",
      discTy = tInt(64, true),
      arms = @[
        VariantArm(tagOrdinal: 0, tagName: "A",
                   fieldNames: @["a"], fieldTypes: @[tInt(64, true)]),
        VariantArm(tagOrdinal: 1, tagName: "B",
                   fieldNames: @["b"], fieldTypes: @[tInt(64, true)])],
      plainFieldNames = @[], plainFieldTypes = @[])

    # Two-axis itMultiVariant: same flat arm set, but split into
    # two axes (`case kind1: of A: a`; `case kind2: of B: b`).
    # Per ADR-0003 D1 these are structurally distinct types — same
    # arm names but different discriminator structure.
    let multiAxis = mkMultiVariant(
      objectName = "Foo",
      plainFieldNames = @[], plainFieldTypes = @[],
      axes = @[
        VariantAxis(discName: "kind1", discTy: tInt(64, true),
                    arms: @[VariantArm(tagOrdinal: 0, tagName: "A",
                                       fieldNames: @["a"],
                                       fieldTypes: @[tInt(64, true)])]),
        VariantAxis(discName: "kind2", discTy: tInt(64, true),
                    arms: @[VariantArm(tagOrdinal: 1, tagName: "B",
                                       fieldNames: @["b"],
                                       fieldTypes: @[tInt(64, true)])])])

    # Canonical encodings must differ — otherwise multi-axis SUTs
    # would silently share cache partitions with same-named single-
    # axis SUTs.
    check canonicalize(singleAxis) != canonicalize(multiAxis)

  test "mkMultiVariant asserts axes.len >= 2":
    # Single-axis itMultiVariant is malformed IR per ADR-0003 D1.
    # The parser must emit itVariant for single-recCase objects;
    # the constructor enforces this invariant.
    expect AssertionDefect:
      discard mkMultiVariant(
        objectName = "Bad",
        plainFieldNames = @[], plainFieldTypes = @[],
        axes = @[VariantAxis(discName: "kind",
                             discTy: tInt(64, true),
                             arms: @[VariantArm(tagOrdinal: 0,
                                                tagName: "A",
                                                fieldNames: @[],
                                                fieldTypes: @[])])])
