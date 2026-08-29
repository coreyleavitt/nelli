## nelli — property-based testing for Nim with internal choice-sequence shrinking.
##
## **Public API surface** (this module): the strategy combinators, the
## property runner (`forAll`, `Settings`, `Report`, `ensure`, `assume`,
## `target`), the `property` DSL adapter for `std/unittest`, the
## `arbitrary` macro for auto-derivation, the `ExampleDB`, stateful testing,
## and the *types* a caller meets when writing a custom strategy or
## inspecting a `Report` (`Strategy`, `DataSource`, `ChoiceNode`, `Int128`,
## etc.).
##
## **Internal modules** (`nelli/int128`, `nelli/choice`,
## `nelli/serialize`, `nelli/rng`, `nelli/datasource`,
## `nelli/shrinker`) carry the implementation. Their *constructor*
## helpers — `integerChoice`, `initSplitMix64`, `newDataSource`, `toBytes`,
## `complexity`, `sortKeyLess`, … — are intentionally **not** re-exported
## here. Reach for them via the submodule import only when you have a
## specific reason (test fixtures that hand-craft sequences, custom shrinker
## passes, etc.); they are not part of the stability promise.

const nelliVersion* = "0.7.0"
  ## The package version, and one of THREE sites that must agree
  ## (`nelli.nimble`, `milpa.kdl`, here). They had drifted to 0.6.0 / 0.4.0 /
  ## 0.1.0 respectively by the time RFC-z3-optional bumped them, because the
  ## only test touching this one asserted `nelliVersion.len > 0`. That is
  ## pinned properly now -- see `tests/tfuzzpackaging.nim`.

import nelli/[strategy, engine, dsl, derive, db, stateful, fuzz, fuzzmacro, fuzzworker,
                 parallel, jsonschema, laws, metamorphic, autolabel, symbolic, bmc, mining,
                 bisim, mutation]
export strategy, engine, dsl, derive, db, stateful, fuzz, fuzzmacro, fuzzworker, parallel,
       jsonschema, laws, metamorphic, autolabel, symbolic, bmc, mining, bisim, mutation

# Type-only re-exports from the internal modules. These types appear in the
# public API surface (`Strategy.run` mentions `DataSource`; `Report.choices`
# is `seq[ChoiceNode]`; numeric strategies use `Int128`) so callers need the
# names in scope. The corresponding *helpers* — choice constructors, raw
# RNG, replay source, etc. — stay hidden.
import nelli/[int128, choice, datasource]
export int128.Int128, int128.toInt128, int128.toInt64, int128.fitsInt64,
       int128.`+`, int128.`-`, int128.`<`, int128.`<=`, int128.`==`,
       int128.clamp, int128.hash, int128.`$`
export choice.ChoiceNode, choice.ChoiceKind, choice.ChoiceInt,
       choice.IntConstraints, choice.FloatConstraints, choice.BoolConstraints,
       choice.BytesConstraints, choice.StringConstraints,
       choice.IntervalSet, choice.intervals, choice.permits, choice.contains,
       choice.`==`, choice.hash, choice.`$`
# DataSource is the parameter type passed to every custom strategy proc.
# Without re-exporting the draw methods, `newStrategy(...)` is unusable from
# `import nelli` alone — the documented public escape hatch must work.
export datasource.DataSource, datasource.Span, datasource.Overrun,
       datasource.maxBytesSize, datasource.maxStringRunes,
       datasource.drawBoolean, datasource.drawInteger, datasource.drawFloat,
       datasource.drawBytes, datasource.drawString,
       datasource.startSpan, datasource.endSpan,
       datasource.isReplaying, datasource.nextRoll
