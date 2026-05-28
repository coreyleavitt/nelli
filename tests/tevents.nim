import std/[unittest, strutils, tables, sequtils]
import proptest

suite "event(): categorical counts":
  test "event(label) accumulates a count across all passing examples":
    # Unlike note() which is per-example debug context wiped on success,
    # event() persists across the whole forAll run — that's how a user
    # discovers "my generator only produces empty lists 80% of the time."
    var nEven = 0
    proc parityProp(x: int) =
      if x mod 2 == 0:
        inc nEven
        event("even")
      else:
        event("odd")
      ensure true
    let r = forAll(integers(0, 9), parityProp,
                   Settings(maxExamples: 100, seed: 5,
                            flakyRetries: 0, maxShrinks: 50,
                            maxRejections: 100))
    check r.outcome == otPassed
    check r.events.categorical["even"] == nEven
    check r.events.categorical["odd"] == 100 - nEven
    check r.events.categorical["even"] + r.events.categorical["odd"] == 100

suite "event(): numeric summaries":
  test "event(label, numericValue) produces min/max/mean + quantiles":
    proc lenProp(xs: seq[int]) =
      event("list-length", xs.len)
      ensure true
    let r = forAll(lists(integers(0, 9), maxLen = 20), lenProp,
                   Settings(maxExamples: 200, seed: 13,
                            flakyRetries: 0, maxShrinks: 50,
                            maxRejections: 200))
    check r.outcome == otPassed
    let s = r.events.numeric["list-length"]
    check s.count == 200
    check s.mn >= 0.0 and s.mx <= 20.0
    check s.p50 <= s.p90
    check s.p90 <= s.p99
    check s.mean >= s.mn and s.mean <= s.mx

  test "mixing categorical and numeric on the same label raises ValueError":
    # A label that's sometimes a count and sometimes a sample is a
    # garbage histogram; fail loud.
    proc badProp(x: int) =
      if x mod 2 == 0:
        event("kind")           # categorical
      else:
        event("kind", x)        # numeric — collision
      ensure true
    let r = forAll(integers(0, 10), badProp,
                   Settings(maxExamples: 50, seed: 1,
                            flakyRetries: 0, maxShrinks: 20,
                            maxRejections: 100))
    # The ValueError propagates as a falsification (caught as CatchableError).
    check r.outcome == otFalsified
    check "event label" in r.message
    check "kind" in r.message

suite "events in repro()":
  test "repro() renders categorical histogram + numeric summary":
    proc p(x: int) =
      event(if x < 5: "low" else: "high")
      event("x-value", x)
      ensure true
    let r = forAll(integers(0, 9), p,
                   Settings(maxExamples: 50, seed: 1,
                            flakyRetries: 0, maxShrinks: 20,
                            maxRejections: 100, printEvents: true))
    let text = repro(r)
    check "events" in text                    # section header
    check "low" in text and "high" in text    # categorical labels
    check "x-value" in text                   # numeric label
    check "p50" in text or "median" in text   # quantile marker

  test "Settings.printEvents = false suppresses the [events] section":
    # Stats are useful, but verbose. Tests that intentionally event() in
    # tight loops want the data (in Report.events) without the noise in
    # the rendered output.
    proc p(x: int) =
      event("k")
      ensure true
    let r = forAll(integers(0, 9), p,
                   Settings(maxExamples: 20, seed: 1,
                            flakyRetries: 0, maxShrinks: 10,
                            maxRejections: 50,
                            printEvents: false))
    let text = repro(r)
    check "[events]" notin text
    # Programmatic access still works.
    check r.events.categorical["k"] == 20
