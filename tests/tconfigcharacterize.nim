## RFC-0010 slice A1 — characterization of the defect, plus the pin mechanism.
##
## Two jobs, both temporary. **Deleted by A3**, along with `zerofill.nim`.
##
## 1. It characterizes the bug. The documented object-literal idiom builds a
##    materially different engine than `defaultSettings()`, and it does so
##    silently. These assertions are GREEN today and go RED at A2 — that is
##    what a characterization test is for, and it is why the seed's version of
##    this test (which called it "red today") had the direction inverted.
##    A2 flips them; A3 deletes the file.
##
## 2. It pins `zeroFilled`, the macro A1 uses to make today's implicit values
##    explicit at 115 literal sites. The load-bearing assertion is the one
##    against a local type that *already* declares field defaults, because
##    that is the only place the macro's behaviour can be observed before A2
##    lands: `Settings` has no declared defaults yet, so every assertion
##    against it is trivially true today and would stay green against a
##    broken macro.

import std/unittest
import std/times
import std/tables
import nelli
import zerofill

# A local stand-in for post-A2 `Settings`: a type that already declares field
# defaults, so the macro's one interesting property — that it defeats them —
# is observable now rather than only after the flip.
type PinProbe = object
  a: int = 100
  b: bool = true
  c: string = "set"
  d: int

suite "RFC-0010 A1 — zeroFilled defeats declared field defaults":

  test "an unwrapped partial literal picks up declared defaults":
    # This is Nim 2.2.10's behaviour and the whole mechanism RFC-0010 adopts.
    # If this ever fails, the RFC's §3 result has been invalidated and A2 is
    # built on sand.
    let lit = PinProbe(d: 7)
    check lit.a == 100
    check lit.b
    check lit.c == "set"
    check lit.d == 7

  test "zeroFilled zeroes every field the literal did not list":
    let pinned = zeroFilled(PinProbe(d: 7))
    check pinned.a == 0
    check not pinned.b
    check pinned.c == ""
    check pinned.d == 7

  test "zeroFilled preserves explicitly-written values, including zeros":
    let pinned = zeroFilled(PinProbe(a: 0, b: false, c: "", d: 1))
    check pinned.a == 0
    check not pinned.b
    check pinned.c == ""
    check pinned.d == 1

  test "zeroFilled on an empty literal is the all-zero value":
    let pinned = zeroFilled(PinProbe())
    check pinned == PinProbe(a: 0, b: false, c: "", d: 0)

  test "zeroFilled evaluates at compile time":
    # A1 wraps `const` settings literals too, so the rewrite has to survive
    # VM evaluation, not just runtime.
    const pinned = zeroFilled(PinProbe(d: 3))
    check pinned.a == 0
    check pinned.d == 3

  test "zeroFilled is a no-op on Settings today":
    # A1's own correctness claim: wrapping the 115 at-risk literals changes
    # nothing *now*. It starts mattering at A2, which is the point.
    check zeroFilled(Settings(maxExamples: 7, seed: 42)) ==
          Settings(maxExamples: 7, seed: 42)

suite "RFC-0010 A1 — characterization: the documented idiom is not the default":

  test "the README literal differs from defaultSettings in eight fields":
    # README.md:33-34, verbatim but for the property body. Seven of the eight
    # omitted non-zero defaults are lost outright; `integerBias` is the eighth
    # and is silently rescued downstream by `resolved()` at phases.nim:260 —
    # the one field somebody bespoke-fixed is the one that survives.
    #
    # GREEN today. A2 turns every one of these into equality and this test
    # goes RED; A3 deletes it.
    let readme = Settings(maxExamples: 7, seed: 42,
                          testId: "kdl-keywords", dbPath: ".nelli-db")
    let want = defaultSettings()
    check readme.maxRejections != want.maxRejections   # 0 vs 1000
    check readme.flakyRetries != want.flakyRetries     # 0 vs 5
    check readme.maxShrinks != want.maxShrinks         # 0 vs 500
    check readme.targetedSAIters != want.targetedSAIters   # 0 vs 200
    check readme.useSA != want.useSA                   # false vs true
    check readme.autoLabels != want.autoLabels         # false vs true
    check readme.printEvents != want.printEvents       # false vs true
    check readme.integerBias != want.integerBias       # zeroed vs 30/30/40

  test "the documented idiom exhausts a filtered property that trivially holds":
    # The sharpest consequence and the one the seed missed: `maxRejections: 0`
    # makes phases.nim:295 (`rejections > maxRejections`) fire on the FIRST
    # rejection, so any filtered or `assume`-using property reports
    # `otExhausted` after about two examples — on a property that holds.
    #
    # A spurious "exhausted" reads to a new user as "this library is broken",
    # not as "I mis-constructed my settings".
    let evens = integers(0, 100).filter(proc(x: int): bool = x mod 2 == 0)
    let holds = proc(x: int) = discard

    let viaDefaults = forAll(evens, holds, defaultSettings())
    check viaDefaults.outcome == otPassed
    check viaDefaults.examples == 100

    let viaLiteral = forAll(evens, holds, Settings(maxExamples: 100, seed: 42))
    check viaLiteral.outcome == otExhausted
    check viaLiteral.examples < 10

  test "the documented idiom silences distribution labels and event output":
    let holds = proc(x: int) = discard

    let viaDefaults = forAll(integers(0, 100), holds, defaultSettings())
    check viaDefaults.printEvents
    check viaDefaults.events.categorical.len > 0

    let viaLiteral = forAll(integers(0, 100), holds,
                            Settings(maxExamples: 20, seed: 42))
    check not viaLiteral.printEvents
    check viaLiteral.events.categorical.len == 0

  test "a bare var Settings is not the documented idiom and stays zero-filled":
    # Recorded as the residual in §7: `var s: Settings` zero-fills and stays
    # legal because `{.requiresInit.}` is deferred, so A2 does NOT make it
    # equal to the defaults. This assertion is green before and after the
    # flip; it exists so the divergence is asserted somewhere rather than
    # discovered by a downstream reader.
    var bare: Settings
    check bare.maxExamples == 0
    check bare.maxRejections == 0
    check not bare.autoLabels
    check bare.deadline == DurationZero
