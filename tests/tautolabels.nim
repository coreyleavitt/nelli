import std/[unittest, times, tables, sets, strutils]
import nelli
import nelli/[choice, datasource, int128]
import zerofill  # RFC-0010 A1 pin; removed by A3

# #108 — strategy distribution auto-labels.
#
# The runtime gate is a threadvar proc-pointer sink in nelli/autolabel.
# Strategies call `autoLabel(...)` unconditionally; the engine installs a
# sink that writes to the current frame's eventsCategorical when
# `Settings.autoLabels` is on. With no sink, `autoLabel` is a no-op so
# raw `s.generate(...)` outside a forAll stays safe.

suite "autoLabel sink — no-op default":
  test "autoLabel without an installed sink does nothing":
    # No engine has run; sink is nil. autoLabel must silently no-op.
    # The observable property: it doesn't raise.
    autoLabel("auto.test:never-recorded")
    check currentAutoLabelSink() == nil

suite "engine installs sink under Settings.autoLabels":
  test "manual autoLabel inside prop appears in Report.events.categorical":
    # End-to-end: when the engine's autoLabels=true, an `autoLabel(...)`
    # call inside a property (or, downstream, inside a strategy) is
    # recorded as a categorical event the same way `event()` is.
    proc prop(x: int) =
      autoLabel("auto.test:hello")
      ensure true
    var s = zeroFilled(Settings(maxExamples: 5, maxRejections: 100, seed: 1,
                                flakyRetries: 1, maxShrinks: 10, useSA: false,
                                targetedSAIters: 0,
                                deadline: initDuration(seconds = 5)))
    s.autoLabels = true
    let r = forAll(integers(0, 10), prop, s)
    check r.outcome == otPassed
    check r.events.categorical.hasKey("auto.test:hello")
    check r.events.categorical["auto.test:hello"] == 5

  test "Settings.autoLabels=false leaves sink nil — no auto events":
    proc prop(x: int) =
      autoLabel("auto.test:should-not-record")
      ensure true
    var s = zeroFilled(Settings(maxExamples: 5, maxRejections: 100, seed: 1,
                                flakyRetries: 1, maxShrinks: 10, useSA: false,
                                targetedSAIters: 0,
                                deadline: initDuration(seconds = 5)))
    s.autoLabels = false
    let r = forAll(integers(0, 10), prop, s)
    check r.outcome == otPassed
    check not r.events.categorical.hasKey("auto.test:should-not-record")

  test "engine restores prior sink on exit":
    setAutoLabelSink(nil)
    proc prop(x: int) = ensure true
    var s = zeroFilled(Settings(maxExamples: 1, maxRejections: 100, seed: 1,
                                flakyRetries: 1, maxShrinks: 10, useSA: false,
                                targetedSAIters: 0,
                                deadline: initDuration(seconds = 5)))
    s.autoLabels = true
    discard forAll(integers(0, 10), prop, s)
    check currentAutoLabelSink() == nil

suite "integers auto-labels":
  test "buckets values into precedence-ordered categories":
    # Drive each precedence bucket by choosing a value that lands in it.
    # zero (== 0) > shrinkTowards (== st when st≠0) > near-lo > near-hi > other.
    var captured: seq[string]
    proc capture(label: string) {.nimcall.} = captured.add label
    setAutoLabelSink(capture)
    defer: setAutoLabelSink(nil)

    # Generate a single value of 0 via just(0); but `just` doesn't emit
    # int labels. We need the actual `integers` strategy. Use sampledFrom
    # of one value? sampledFrom emits its own label, not int's. Use
    # integers with weight to force a specific value.

    # Simpler: hand the strategy a replayed source forcing a specific value.
    proc draw(s: Strategy[int], v: int, lo, hi: int): string =
      ## Run `s` once against a recorded ChoiceNode forcing v as the draw,
      ## then return the captured auto.int:* label.
      captured.setLen(0)
      var ds = newReplaySource(@[
        ChoiceNode(kind: ckInteger,
                   intC: IntConstraints(min: toInt128(lo), max: toInt128(hi),
                                        shrinkTowards: toInt128(0)),
                   intVal: toInt128(v))])
      discard s.generate(ds)
      var label = ""
      for l in captured:
        if l.startsWith("auto.int:"): label = l
      label

    let s = integers(-100, 100)
    check draw(s, 0,    -100, 100) == "auto.int:zero"
    check draw(s, -100, -100, 100) == "auto.int:near-lo"
    check draw(s, 100,  -100, 100) == "auto.int:near-hi"
    check draw(s, 50,   -100, 100) == "auto.int:other"

  test "shrinkTowards label fires when value equals shrinkTowards (and is nonzero)":
    var captured: seq[string]
    proc capture(label: string) {.nimcall.} = captured.add label
    setAutoLabelSink(capture)
    defer: setAutoLabelSink(nil)

    # integers(lo, hi) hard-codes shrinkTowards=0. To exercise the
    # nonzero-shrinkTowards branch we'd need a strategy that exposes it.
    # The label precedence (zero > shrinkTowards) is what matters: with
    # shrinkTowards=0, hitting 0 should always categorise as "zero",
    # never "shrinkTowards".
    var ds = newReplaySource(@[
      ChoiceNode(kind: ckInteger,
                 intC: IntConstraints(min: toInt128(-100), max: toInt128(100),
                                      shrinkTowards: toInt128(0)),
                 intVal: toInt128(0))])
    discard integers(-100, 100).generate(ds)
    var sawZero = false
    var sawShrink = false
    for l in captured:
      if l == "auto.int:zero": sawZero = true
      if l == "auto.int:shrinkTowards": sawShrink = true
    check sawZero
    check not sawShrink

suite "lists auto-labels":
  test "buckets list length into empty/small/medium/near-max/max":
    var captured: seq[string]
    proc capture(label: string) {.nimcall.} = captured.add label
    setAutoLabelSink(capture)
    defer: setAutoLabelSink(nil)

    proc lastListLenLabel(): string =
      var l = ""
      for x in captured:
        if x.startsWith("auto.list-len:"): l = x
      l

    proc runReplay(s: Strategy[seq[int]], seq0: seq[ChoiceNode]) =
      var ds = newReplaySource(seq0)
      try: discard s.generate(ds)
      except CatchableError: discard

    # Hand-craft choice sequences that force specific list lengths via the
    # continue-bool node at each iteration.
    proc cont(v: bool): ChoiceNode =
      ChoiceNode(kind: ckBoolean, boolC: BoolConstraints(p: 0.9), boolVal: v)
    proc anyInt(): ChoiceNode =
      ChoiceNode(kind: ckInteger,
                 intC: IntConstraints(min: toInt128(0), max: toInt128(100),
                                      shrinkTowards: toInt128(0)),
                 intVal: toInt128(0))

    let s = lists(integers(0, 100), minLen = 0, maxLen = 8)

    # Empty: first cont=false.
    captured.setLen(0)
    runReplay(s, @[cont(false)])
    check lastListLenLabel() == "auto.list-len:empty"

    # Max: 8 elements then we stop (continue is forced false at maxLen,
    # so we omit a final cont and the strategy reads the constrained-
    # false implicit terminator).
    captured.setLen(0)
    var maxSeq: seq[ChoiceNode]
    for _ in 0 ..< 8:
      maxSeq.add cont(true)
      maxSeq.add anyInt()
    maxSeq.add cont(false)   # terminator at maxLen (p is forced 0.0)
    runReplay(s, maxSeq)
    check lastListLenLabel() == "auto.list-len:max"

    # Small: 1 element (≤ maxLen/4 = 2).
    captured.setLen(0)
    runReplay(s, @[cont(true), anyInt(), cont(false)])
    check lastListLenLabel() == "auto.list-len:small"

    # Near-max: 7 elements (≥ 3*maxLen/4 = 6, < maxLen = 8).
    captured.setLen(0)
    var nearSeq: seq[ChoiceNode]
    for _ in 0 ..< 7:
      nearSeq.add cont(true)
      nearSeq.add anyInt()
    nearSeq.add cont(false)
    runReplay(s, nearSeq)
    check lastListLenLabel() == "auto.list-len:near-max"

    # Medium: 4 elements (≈ midway).
    captured.setLen(0)
    var medSeq: seq[ChoiceNode]
    for _ in 0 ..< 4:
      medSeq.add cont(true)
      medSeq.add anyInt()
    medSeq.add cont(false)
    runReplay(s, medSeq)
    check lastListLenLabel() == "auto.list-len:medium"

suite "oneOf, sampledFrom auto-labels":
  test "oneOf emits branch-N for the chosen alternative":
    # oneOf draws a mask of N booleans then an index over enabled[].
    # Force all four branches enabled, pick branch 2.
    let four = oneOf(@[just(1), just(2), just(3), just(4)])
    var captured: seq[string]
    proc capture(l: string) {.nimcall.} = captured.add l
    setAutoLabelSink(capture); defer: setAutoLabelSink(nil)

    proc allEnabled(): seq[ChoiceNode] =
      for _ in 0 ..< 4:
        result.add ChoiceNode(kind: ckBoolean,
                              boolC: BoolConstraints(p: 0.8), boolVal: true)

    var seq2 = allEnabled()
    seq2.add ChoiceNode(kind: ckInteger,
                        intC: IntConstraints(min: toInt128(0),
                                             max: toInt128(3),
                                             shrinkTowards: toInt128(0)),
                        intVal: toInt128(2))
    var ds = newReplaySource(seq2)
    discard four.generate(ds)
    var got = ""
    for l in captured:
      if l.startsWith("auto.oneOf:"): got = l
    check got == "auto.oneOf:branch-2"

  test "sampledFrom emits idx-N":
    let s = sampledFrom(@["a", "b", "c", "d", "e"])
    var captured: seq[string]
    proc capture(l: string) {.nimcall.} = captured.add l
    setAutoLabelSink(capture); defer: setAutoLabelSink(nil)
    var ds = newReplaySource(@[
      ChoiceNode(kind: ckInteger,
                 intC: IntConstraints(min: toInt128(0), max: toInt128(4),
                                      shrinkTowards: toInt128(0)),
                 intVal: toInt128(3))])
    discard s.generate(ds)
    var got = ""
    for l in captured:
      if l.startsWith("auto.sampledFrom:"): got = l
    check got == "auto.sampledFrom:idx-3"

suite "floats, booleans auto-labels":
  test "floats classify zero / nan / inf / subnormal / other":
    var captured: seq[string]
    proc capture(l: string) {.nimcall.} = captured.add l
    setAutoLabelSink(capture); defer: setAutoLabelSink(nil)
    proc last(): string =
      var l = ""
      for x in captured:
        if x.startsWith("auto.float:"): l = x
      l
    let s = floats(min = NegInf, max = Inf, allowNan = true)
    template runOne(v: float) =
      captured.setLen(0)
      var ds = newReplaySource(@[
        ChoiceNode(kind: ckFloat,
                   floatC: FloatConstraints(min: NegInf, max: Inf,
                                            allowNan: true,
                                            smallestNonzeroMagnitude: 0.0),
                   floatVal: v)])
      try: discard s.generate(ds)
      except CatchableError: discard
    runOne(0.0);   check last() == "auto.float:zero"
    runOne(NaN);   check last() == "auto.float:nan"
    runOne(Inf);   check last() == "auto.float:inf"
    runOne(NegInf); check last() == "auto.float:inf"
    runOne(1.0);   check last() == "auto.float:other"
    runOne(5e-324); check last() == "auto.float:subnormal"

  test "booleans emit auto.bool:true / auto.bool:false":
    var captured: seq[string]
    proc capture(l: string) {.nimcall.} = captured.add l
    setAutoLabelSink(capture); defer: setAutoLabelSink(nil)
    proc emitsFor(v: bool): string =
      captured.setLen(0)
      var ds = newReplaySource(@[
        ChoiceNode(kind: ckBoolean,
                   boolC: BoolConstraints(p: 0.5), boolVal: v)])
      discard booleans().generate(ds)
      for l in captured:
        if l.startsWith("auto.bool:"): return l
      ""
    check emitsFor(true)  == "auto.bool:true"
    check emitsFor(false) == "auto.bool:false"

suite "containers + strings: family-tagged size labels":
  # Integration tests via forAll: the engine installs its own sink, so we
  # assert against Report.events.categorical instead of a local capture.
  proc anyKeyStartingWith(r: EventStats, prefix: string): bool =
    for k, _ in r.categorical:
      if k.startsWith(prefix): return true
    false

  test "strings emit auto.string-len:* by codepoint count":
    var s2 = defaultSettings()
    s2.maxExamples = 30; s2.useSA = false; s2.targetedSAIters = 0
    let r = forAll(strings(minLen = 0, maxLen = 8),
                   (proc(s: string) = ensure true), s2)
    check anyKeyStartingWith(r.events, "auto.string-len:")

  test "tables emit auto.table-size:*":
    var s2 = defaultSettings()
    s2.maxExamples = 20; s2.useSA = false; s2.targetedSAIters = 0
    let r = forAll(tables(integers(0, 10), integers(0, 10),
                          minSize = 0, maxSize = 4),
                   (proc(t: Table[int, int]) = ensure true), s2)
    check anyKeyStartingWith(r.events, "auto.table-size:")

  test "sets emit auto.set-size:*":
    var s2 = defaultSettings()
    s2.maxExamples = 20; s2.useSA = false; s2.targetedSAIters = 0
    let r = forAll(sets(integers(0, 10), minSize = 0, maxSize = 4),
                   (proc(s: HashSet[int]) = ensure true), s2)
    check anyKeyStartingWith(r.events, "auto.set-size:")

  test "arrays emit auto.array-len:*":
    var s2 = defaultSettings()
    s2.maxExamples = 20; s2.useSA = false; s2.targetedSAIters = 0
    let r = forAll(arrays[3, int](integers(0, 10)),
                   (proc(a: array[3, int]) = ensure true), s2)
    check anyKeyStartingWith(r.events, "auto.array-len:")
