## RFC-0010 — the definition of done, Z3-free half.
##
## Every in-scope configuration surface's *documented construction idiom*, run
## through its *real entry point*, asserting that the fields the caller did not
## list carry that surface's defaults rather than zeros.
##
## Deliberately free of `nelli/symex`: covering all five surfaces in one file
## would import the SMT stack and make the definition of done Z3-linked,
## undoing for this file exactly what RFC-0004 made true of `import nelli`, and
## restricting it to one of the three Windows legs. `SymexSettings` and
## `ResourceBudget` live in `tests/tsymexconfigdefaults.nim` instead.
##
## Slice ownership (RFC-0010 §7): A2 owns `Settings`; C1 owns
## `IntegerBiasConfig` zero-survival; C2 owns `BmcSettings`; C3a owns the
## conforming-by-zeros registry.
##
## Two kinds of assertion appear here and they are not interchangeable.
## Structural equality alone cannot cover this defect class, because an adapter
## can sit between the literal and the engine — `phases.nim:260` applies
## `resolved()` to `integerBias` today, entirely invisible to any `==` on
## `Settings`. So each surface also gets a behavioural assertion through its
## real entry point.

import std/unittest
import std/tables
import std/times
import std/strutils
import nelli

suite "RFC-0010 A2 — Settings: the empty literal IS the documented default":

  test "Settings() equals defaultSettings()":
    # §0's invariant, at its sharpest. Once this holds, `defaultSettings()` is
    # a second name for a thing the type already says.
    check Settings() == defaultSettings()

  test "default(Settings) equals defaultSettings()":
    check default(Settings) == defaultSettings()

  test "a partial literal differs from the default only in what it lists":
    let lit = Settings(maxExamples: 7)
    var want = defaultSettings()
    want.maxExamples = 7
    check lit == want

  test "every field of the README's literal is either listed or defaulted":
    # README.md:33-34 verbatim. Field by field rather than a whole-object `==`
    # so a failure names the field that regressed.
    let lit = Settings(maxExamples: 7, seed: 42,
                       testId: "kdl-keywords", dbPath: ".nelli-db")
    let want = defaultSettings()

    # listed by the caller
    check lit.maxExamples == 7
    check lit.seed == 42'u64
    check lit.testId == "kdl-keywords"
    check lit.dbPath == ".nelli-db"

    # the eight it omits, all of which used to arrive as zero
    check lit.maxRejections == want.maxRejections
    check lit.flakyRetries == want.flakyRetries
    check lit.maxShrinks == want.maxShrinks
    check lit.targetedSAIters == want.targetedSAIters
    check lit.useSA == want.useSA
    check lit.autoLabels == want.autoLabels
    check lit.printEvents == want.printEvents
    check lit.integerBias == want.integerBias

    # and the fields whose default genuinely is the zero value
    check lit.derandomize == false
    check lit.strictDb == false
    check lit.coverageGuided == false
    check lit.deadline == DurationZero
    check lit.forcePhases == {}

  test "explicitly-written zeros survive":
    # The property that disqualifies every sentinel and merge scheme, and the
    # reason field defaults are the mechanism: zero is a documented user intent
    # on four of these fields (maxShrinks 0 = unbounded, targetedSAIters 0 = SA
    # off, flakyRetries 0 = retries off, seed 0 = a legitimate seed), and three
    # more are bools defaulting to true, so `false` IS their zero value.
    let off = Settings(maxShrinks: 0, targetedSAIters: 0, flakyRetries: 0,
                       seed: 0, useSA: false, printEvents: false,
                       autoLabels: false)
    check off.maxShrinks == 0
    check off.targetedSAIters == 0
    check off.flakyRetries == 0
    check off.seed == 0'u64
    check not off.useSA
    check not off.printEvents
    check not off.autoLabels
    # …while the fields it did not list still default
    check off.maxExamples == defaultSettings().maxExamples
    check off.maxRejections == defaultSettings().maxRejections

  test "the defaults reach const/VM evaluation":
    const lit = Settings(maxExamples: 7)
    check lit.maxRejections == 1000
    check lit.autoLabels

  test "the defaults reach newSeq and new":
    var s = newSeq[Settings](2)
    check s[0] == defaultSettings()
    let r = new(ref Settings)
    check r[] == defaultSettings()

  test "a bare var Settings still zero-fills — the recorded residual":
    # §7's residual, asserted rather than left to a downstream reader to
    # discover: `var s: Settings` does NOT pick up field defaults, and stays
    # legal because `{.requiresInit.}` is deferred. A literal and a `var` of
    # the same type now disagree, which is a new reader trap and is why C5's
    # downstream audit has to say so.
    var bare: Settings
    check bare.maxExamples == 0
    check bare.maxRejections == 0
    check not bare.autoLabels
    check bare != defaultSettings()

suite "RFC-0010 A2 — Settings: behaviour through the real entry point":

  test "the README's literal no longer exhausts a filtered property":
    # The headline symptom. Structural equality cannot establish this on its
    # own: `phases.nim:260` applies `resolved()` between the literal and the
    # engine, so an adapter could keep `==` true while behaviour diverged.
    let evens = integers(0, 100).filter(proc(x: int): bool = x mod 2 == 0)
    let holds = proc(x: int) = discard

    let viaLiteral = forAll(evens, holds,
                            Settings(maxExamples: 100, seed: 42))
    check viaLiteral.outcome == otPassed
    check viaLiteral.examples == 100

  test "the README's literal emits distribution labels and event output":
    let holds = proc(x: int) = discard
    let r = forAll(integers(0, 100), holds,
                   Settings(maxExamples: 20, seed: 42,
                            testId: "kdl-keywords"))
    check r.printEvents
    check r.events.categorical.len > 0
    for key in r.events.categorical.keys:
      check key.startsWith("auto.")

  test "the literal and defaultSettings() drive the engine identically":
    # The whole property in one assertion, at the entry point: the same run
    # under the documented idiom and under the constructor agree.
    let s = integers(0, 100)
    let holds = proc(x: int) = discard
    let viaLiteral = forAll(s, holds, Settings(maxExamples: 25, seed: 7))
    var explicitDefaults = defaultSettings()
    explicitDefaults.maxExamples = 25
    explicitDefaults.seed = 7
    let viaDefaults = forAll(s, holds, explicitDefaults)

    check viaLiteral.outcome == viaDefaults.outcome
    check viaLiteral.examples == viaDefaults.examples
    check viaLiteral.printEvents == viaDefaults.printEvents
    check viaLiteral.events.categorical == viaDefaults.events.categorical

  test "the DSL's `with` clause carries the defaults too":
    # `property`/`with` (dsl.nim:36-43) is the other documented entry point for
    # Settings, and it takes an arbitrary expression — so a partial literal
    # written there has to behave the same as one passed to forAll.
    # The binding is filtered, so the run only reaches 12 examples if
    # `maxRejections` arrived as its default — under the zero-filled literal
    # the first rejection ends the run. An unfiltered strategy would pass
    # here before and after the flip and prove nothing.
    var ran = 0
    property "with-clause literal keeps the defaults":
      with Settings(maxExamples: 12, seed: 3)
      given x in integers(0, 100).filter(proc(v: int): bool = v mod 2 == 0)
      inc ran
      ensure x >= 0
    check ran == 12
