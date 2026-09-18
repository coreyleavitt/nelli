## Issue #163 review finding R12 (Medium, refactor) -- `nelli/symex` decided a
## variant discriminator's legal domain in TWO independent places:
## `allocateSym`'s `itVariant` arm (the BV-disc disjunction) and
## `runSymexImpl`'s `isOptimised` disc-promotion (the Z3Int bound +
## disjunction). Both re-derived the same `rangeAliasElseDomain` guard by
## hand -- that duplication is not hypothetical: issue #163 W6 (a range-alias
## `else:` arm's domain wrongly narrowed to just the explicit `of N:`
## literals) had to be fixed in BOTH builders.
##
## Extracted `discriminatorDomain` (runtime.nim, beside `allocateSym`) as the
## ONE place that decides this, and routed both builders through it. Being
## pure (no Z3 context) it is unit-testable directly, which neither builder
## was before -- this suite is that direct test, exercising the function
## itself rather than the end-to-end `symexFind` path (already covered,
## end-to-end, by `tsymex_163audit_wave2.nim` for the W6 case specifically,
## and `tsymex_a2_refvariant_fields.nim` / `tsymex_phase14_disc_promotion.nim`
## for the two builders generally -- this file's job is the domain DECISION
## in isolation).
##
## `ordSet.len == 0` is the function's signal for "assert no explicit
## per-ordinal disjunction" -- it means the range-alias-else-domain case
## applies (the discriminator's own declared range, asserted separately,
## already IS the domain) or the variant is degenerate (no arms at all).

import std/[unittest, strutils]
import nelli/smt/canonicalize
import nelli/smt/types
import nelli/smt/runtime

suite "#163 review R12 -- discriminatorDomain, enum discriminator":

  test "no else arm: domain is exactly the explicit arm ordinals":
    let discTy = tUInt(8)
    let arms = @[
      VariantArm(tagOrdinal: 0, tagName: "a", isElse: false),
      VariantArm(tagOrdinal: 1, tagName: "b", isElse: false),
    ]
    # Exhaustive `of` (no else) means vDiscTags need not even be populated
    # for the domain to be complete -- mirroring what dsl_typebridge.nim
    # actually hands the walker for a plain (non-else) enum case.
    let ty = tVariant("Obj", "kind", discTy, arms)
    let (minOrd, maxOrd, ordSet) = discriminatorDomain(ty)
    check minOrd == 0
    check maxOrd == 1
    check ordSet == @[0, 1]

  test "with an else arm: domain expands to the full enum-tag set":
    let discTy = tUInt(8)
    let arms = @[
      VariantArm(tagOrdinal: 0, tagName: "a", isElse: false),
      VariantArm(tagOrdinal: -1, tagName: "else", isElse: true),
    ]
    # Only tag "a" (0) has an explicit `of` arm; tags "b" (1) and "c" (2)
    # are covered ONLY by the else arm. The domain must include them.
    let discTags = @[(name: "a", ord: 0), (name: "b", ord: 1),
                      (name: "c", ord: 2)]
    let ty = tVariant("Obj", "kind", discTy, arms, discTags = discTags)
    let (minOrd, maxOrd, ordSet) = discriminatorDomain(ty)
    check minOrd == 0
    check maxOrd == 2
    check ordSet == @[0, 1, 2]

suite "#163 review R12 -- discriminatorDomain, range-alias discriminator":

  test "W6: an else arm on a range-alias disc takes the disc's OWN range":
    ## The bug this whole finding traces back to: a non-enum discriminator
    ## (e.g. `range[1..5]`) has no `vDiscTags` for an `else:` arm to fan out
    ## over. Narrowing the domain to just the explicit `of N:` ordinals made
    ## every else-covered value unreachable. `discriminatorDomain` must
    ## return the disc's OWN declared range and an EMPTY ordSet (meaning:
    ## assert no per-ordinal disjunction -- the range bound, asserted
    ## separately by the disc's own allocation, already is the domain).
    let discTy = withRange(tInt(width = 64, signed = true), 1, 5)
    let arms = @[
      VariantArm(tagOrdinal: 1, tagName: "one", isElse: false),
      VariantArm(tagOrdinal: -1, tagName: "else", isElse: true),
    ]
    let ty = tVariant("Obj", "kind", discTy, arms)  # no discTags: non-enum
    let (minOrd, maxOrd, ordSet) = discriminatorDomain(ty)
    check minOrd == 1
    check maxOrd == 5
    check ordSet.len == 0

  test "of-literals already exhaust the declared range, but NO else arm":
    ## The case `rangeAliasElseDomain` exists to DISTINGUISH from the W6
    ## case above: even though the explicit `of` ordinals happen to cover
    ## the disc's entire declared range, the range-alias-else-domain
    ## shortcut must NOT fire here -- there is no `else:` arm, so Nim's own
    ## case-exhaustiveness is what makes this legal, and the domain is
    ## still described by the explicit ordinal disjunction (non-empty
    ## ordSet), not silently collapsed to "just trust the range bound".
    let discTy = withRange(tInt(width = 64, signed = true), 0, 2)
    let arms = @[
      VariantArm(tagOrdinal: 0, tagName: "z", isElse: false),
      VariantArm(tagOrdinal: 1, tagName: "o", isElse: false),
      VariantArm(tagOrdinal: 2, tagName: "t", isElse: false),
    ]
    let ty = tVariant("Obj", "kind", discTy, arms)
    let (minOrd, maxOrd, ordSet) = discriminatorDomain(ty)
    check minOrd == 0
    check maxOrd == 2
    check ordSet == @[0, 1, 2]

suite "#163 review R12 -- discriminatorDomain, sparse/holed ordinals":

  test "a holed set of `of` values keeps its holes -- min/max only bound":
    ## No else arm; ordinals 0, 5, 10 with real gaps (1-4, 6-9). The
    ## per-ordinal disjunction must name exactly {0, 5, 10} -- the min/max
    ## bound is a looser envelope around the same set, not a claim that
    ## every value in [0, 10] is legal.
    let discTy = tUInt(8)
    let arms = @[
      VariantArm(tagOrdinal: 0, tagName: "a", isElse: false),
      VariantArm(tagOrdinal: 5, tagName: "b", isElse: false),
      VariantArm(tagOrdinal: 10, tagName: "c", isElse: false),
    ]
    let ty = tVariant("Obj", "kind", discTy, arms)
    let (minOrd, maxOrd, ordSet) = discriminatorDomain(ty)
    check minOrd == 0
    check maxOrd == 10
    check ordSet == @[0, 5, 10]

  test "a holed enum with an else arm folds in the covered-only-by-else holes":
    ## Enum tags {0, 5, 10}; only tag 0 has an explicit `of` arm, the rest
    ## are covered by `else:`. The domain must be the full {0, 5, 10} set,
    ## not just {0}.
    let discTy = tUInt(8)
    let arms = @[
      VariantArm(tagOrdinal: 0, tagName: "a", isElse: false),
      VariantArm(tagOrdinal: -1, tagName: "else", isElse: true),
    ]
    let discTags = @[(name: "a", ord: 0), (name: "b", ord: 5),
                      (name: "c", ord: 10)]
    let ty = tVariant("Obj", "kind", discTy, arms, discTags = discTags)
    let (minOrd, maxOrd, ordSet) = discriminatorDomain(ty)
    check minOrd == 0
    check maxOrd == 10
    check ordSet == @[0, 5, 10]

suite "#163 review round 1 -- walker version pin":

  test "walker version floor >= 135 (the review round's single bump)":
    ## Pure consolidation -- this refactor changes no verdict and owes no
    ## version bump of its own. Pinned at the round's existing floor.
    check parseInt(symexWalkerVersion) >= 135
