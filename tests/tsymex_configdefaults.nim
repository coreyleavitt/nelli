## RFC-0010 — the definition of done, symex half.
##
## `SymexSettings` and `ResourceBudget`: the documented construction idiom run
## through the real entry point (`symexFind`, whose `settings` parameter is a
## `static SymexSettings`), asserting that the fields the caller did not list
## carry the defaults rather than zeros.
##
## Separate from `tests/tconfigdefaults.nim` on purpose. Covering all five
## surfaces in one file would import the SMT stack and make the whole
## definition of done Z3-linked, undoing for it what RFC-0004 made true of
## `import nelli`. This half is the one that legitimately needs Z3.
##
## Named `tsymex_configdefaults` rather than the RFC's `tsymexconfigdefaults`
## because `scripts/derive-ci-suites.ps1` builds the symex-mingw corpus by
## matching `tsymex_*` **with the underscore**. Without it this file would be
## invisible to the only CI leg that runs the symex corpus — which is exactly
## the registration gap slice B1 exists to close for four other files.
##
## Slice ownership: B2 owns the defaults; B3 adds the merge pins.

import std/unittest
import nelli/symex

# ---------------------------------------------------------------------------
# A SUT whose verdict depends on `arithChecks`, which is the field that makes
# the defect observable. `arithChecks` gates whether arithmetic defect forks
# are emitted at all: all-on by default, empty (release-like, wrap/unchecked)
# when zero-filled. So an unconstrained signed add is `sxRaised` under the
# defaults and `sxUnsat` under a zero-filled literal — the ten const literals
# in the symex suite have been running release-like without anybody choosing
# that.
# ---------------------------------------------------------------------------
proc mayOverflow(a, b: int) =
  let c = a + b
  symexTarget("t")
  discard c

suite "RFC-0010 B2 — ResourceBudget: the empty literal IS the default":

  test "ResourceBudget() equals defaultResourceBudget()":
    check ResourceBudget() == defaultResourceBudget()

  test "default(ResourceBudget) equals defaultResourceBudget()":
    check default(ResourceBudget) == defaultResourceBudget()

  test "a partial budget differs from the default only in what it lists":
    # The exact shape all ten in-suite literals use: four fields listed, nine
    # omitted. Before B2 those nine arrived as 0, which this type documents as
    # *unlimited* — so the literals were not merely mis-defaulted, they were
    # asking for unbounded heap depth, freshness assertions, closure inlining,
    # instantiations, split parts, bytes-encoding length, seq inlining and
    # variant-constructor forks.
    let lit = ResourceBudget(queryRLimit: 1'u, maxFrontierSize: 0,
                             maxCallDepth: 3, maxLoopUnwind: 5)
    let want = defaultResourceBudget()
    check lit.queryRLimit == 1'u
    check lit.maxCallDepth == 3
    check lit.maxLoopUnwind == 5
    check lit.maxHeapDepth == want.maxHeapDepth
    check lit.maxFreshnessAssertions == want.maxFreshnessAssertions
    check lit.maxClosureInlineCount == want.maxClosureInlineCount
    check lit.maxInstantiationsPerProc == want.maxInstantiationsPerProc
    check lit.maxSplitParts == want.maxSplitParts
    check lit.maxBytesEncodingLen == want.maxBytesEncodingLen
    check lit.seqInlineThreshold == want.seqInlineThreshold
    check lit.maxVariantConstructorForks == want.maxVariantConstructorForks
    check lit.maxVariantConstructorFieldAllocs ==
          want.maxVariantConstructorFieldAllocs

  test "an explicitly-written zero still means unlimited":
    # `0 = unlimited` is this type's documented contract, so the flip must not
    # take the ability to say it away. This is the assertion that disqualifies
    # every sentinel scheme for this surface.
    let unlimited = ResourceBudget(maxHeapDepth: 0, maxSplitParts: 0)
    check unlimited.maxHeapDepth == 0
    check unlimited.maxSplitParts == 0
    check unlimited.maxCallDepth == defaultResourceBudget().maxCallDepth

suite "RFC-0010 B2 — SymexSettings: the empty literal IS the default":

  test "SymexSettings() equals defaultSymexSettings()":
    check SymexSettings() == defaultSymexSettings()

  test "default(SymexSettings) equals defaultSymexSettings()":
    check default(SymexSettings) == defaultSymexSettings()

  test "a partial literal keeps every unlisted field, including the nested budget":
    let lit = SymexSettings(integerSemantics: isOptimised)
    let want = defaultSymexSettings()
    check lit.integerSemantics == isOptimised
    check lit.budget == want.budget
    check lit.defectExclusions == want.defectExclusions
    check lit.arithChecks == want.arithChecks
    check lit.inlinePolicy == want.inlinePolicy
    check not lit.acceptUnknownAsCovered   # its default genuinely is the zero

  test "inlinePolicy defaults to ipHybrid, not the zero-valued arm":
    # ipAlwaysInline is ordinal 0 and ipHybrid is ordinal 2, so an omitted
    # inlinePolicy silently selected a different call-summary strategy. This
    # is the one flipped field whose zero value is a legal, meaningful setting
    # rather than an obviously-wrong one, which is why it went unnoticed.
    check SymexSettings().inlinePolicy == ipHybrid
    check SymexSettings(integerSemantics: isExact).inlinePolicy == ipHybrid

  test "a nested partial budget defaults at both levels":
    const lit = SymexSettings(
      integerSemantics: isOptimised,
      budget: ResourceBudget(maxLoopUnwind: 2))
    check lit.budget.maxLoopUnwind == 2
    check lit.budget.maxCallDepth == defaultResourceBudget().maxCallDepth
    check lit.budget.maxHeapDepth == defaultResourceBudget().maxHeapDepth
    check lit.arithChecks == defaultSymexSettings().arithChecks

  test "the defaults reach const/VM evaluation":
    # Not optional here: `symexFind`'s settings parameter is a
    # `static SymexSettings`, so every real call site is VM-evaluated. A
    # mechanism that worked at runtime and not in the VM would be useless for
    # this surface.
    const lit = SymexSettings(integerSemantics: isExact)
    check lit.budget.maxCallDepth == 3
    check lit.arithChecks == {acOverflow, acDivByZero, acRange}
    check lit.inlinePolicy == ipHybrid

suite "RFC-0010 B2 — behaviour through the real entry point":

  test "a partial literal finds the overflow the defaults find":
    # The end-to-end assertion. `arithChecks` gates arithmetic defect-fork
    # emission; zero-filled it is empty, so the raise path does not exist and
    # the target is unreachable. Under the defaults the fork is opened and the
    # same query is sxRaised. Structural equality could not have caught this
    # on its own — the settings travel into a macro and become a cache key.
    let viaLiteral = symexFind(mayOverflow, tRaisedExn("OverflowDefect"),
                               SymexSettings(integerSemantics: isOptimised))
    check viaLiteral.status == sxRaised
    # Guarded: `raisedTypeId` lives on the sxRaised arm, so reading it after a
    # failed status check raises FieldDefect and takes the whole suite with it
    # instead of reporting.
    if viaLiteral.status == sxRaised:
      check viaLiteral.raisedTypeId == "OverflowDefect"

  test "the partial literal and defaultSymexSettings() agree":
    let viaLiteral = symexFind(mayOverflow, tRaisedExn("OverflowDefect"),
                               SymexSettings(integerSemantics: isOptimised))
    let viaDefaults = symexFind(mayOverflow, tRaisedExn("OverflowDefect"),
                                defaultSymexSettings())
    check viaLiteral.status == viaDefaults.status
    if viaLiteral.status == sxRaised and viaDefaults.status == sxRaised:
      check viaLiteral.raisedTypeId == viaDefaults.raisedTypeId

# ---------------------------------------------------------------------------
# RFC-0010 B3 — regression pins for the deprecated merge.
#
# `+` is deprecated, not deleted: it is public, and round 2 established it has
# zero production callers (its only calls in the tree are these tests of
# itself). Round 1 proposed replacing both hand-written bodies with a generic
# recursive `merged` plus a generative algebraic-law suite — investment in an
# operator with no users, and a naive `fields()` rewrite would have silently
# broken nested composition. So the bodies stay and two cheap pins stop a
# deprecated-but-live operator from rotting silently.
#
# These are GREEN today by design. They are regression pins, not acceptance
# tests — both bodies currently cover every field.
# ---------------------------------------------------------------------------
{.push warning[Deprecated]: off.}

proc fieldCount[T](): int =
  var v: T
  for _ in v.fields: inc result

suite "RFC-0010 B3 — the deprecated merge still covers every field":

  test "a fully-overriding merge reproduces the override exactly":
    # Every one of ResourceBudget's 13 fields and SymexSettings' 5 non-budget
    # fields set away from its default, so a `+` body missing a line drops that
    # field back and this fails naming it.
    let b = SymexSettings(
      integerSemantics: isExact,
      acceptUnknownAsCovered: true,
      defectExclusions: {dkIndexDefect},
      arithChecks: {acDivByZero},
      inlinePolicy: ipAlwaysAxiomatize,
      budget: ResourceBudget(
        queryRLimit: 111'u, maxFrontierSize: 222, maxCallDepth: 33,
        maxLoopUnwind: 44, maxHeapDepth: 55, maxFreshnessAssertions: 666,
        maxClosureInlineCount: 777, maxInstantiationsPerProc: 888,
        maxSplitParts: 99, maxBytesEncodingLen: 121,
        seqInlineThreshold: 131, maxVariantConstructorForks: 141,
        maxVariantConstructorFieldAllocs: 151))
    check defaultSymexSettings() + b == b

  test "the field counts the merge was written against have not changed":
    # The assertion above cannot catch a NEWLY ADDED field: a field the test
    # does not list arrives at its default on both sides, so the merge agrees
    # and the pin passes while `+` silently ignores it. Pinning the counts is
    # what forces the next person who adds a field to come here, and from here
    # to both `+` bodies.
    check fieldCount[ResourceBudget]() == 13
    check fieldCount[SymexSettings]() == 6   # 5 scalars plus `budget`

  test "composing two different nested budget overrides keeps both":
    # `a` and `b` each change ONE, different, budget subfield. A whole-object
    # merge that took `b.budget` wholesale would drop `a`'s — which is exactly
    # the bug a naive fields()-based rewrite would have introduced, and which
    # round 1's specified test would have passed under.
    let a = SymexSettings(budget: ResourceBudget(maxHeapDepth: 99))
    let b = SymexSettings(budget: ResourceBudget(maxSplitParts: 77))
    let merged = a + b
    check merged.budget.maxHeapDepth == 99
    check merged.budget.maxSplitParts == 77
    check merged.budget.maxCallDepth == defaultResourceBudget().maxCallDepth

{.pop.}
