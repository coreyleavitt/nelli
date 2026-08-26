import std/[unittest, options, times]
import nelli
import nelli/[datasource, choice, rng]

# #110 — Schema-aware IR mutation for the fuzz adapter.
#
# Today fuzzWith mutates raw bytes and `fuzzOnce` decodes them into a
# typed IR via `newReplaySourceFromBytes`. Byte-level mutations regularly
# decode into structurally-invalid IRs and get rejected. The whole
# architectural payoff of the M12 typed-IR decision is that we *can*
# mutate at the IR level and stay constraint-respecting by construction.
#
# This suite drives that capability in: fuzzOnceIR replays IR directly,
# the mutators rewrite IR sequences, and (under irMutation=true)
# fuzzWith uses them as the default mutation kernel.

suite "fuzzOnceIR — IR-level replay":
  test "replays a generated choice sequence and reports foOk":
    # Generate a value once, recording the IR; then feed that IR to
    # fuzzOnceIR and verify it reproduces a passing run.
    let s = integers(0, 1000)
    var ds = newDataSource(initSplitMix64(0xC0FFEE'u64))
    let x = s.generate(ds)
    let recorded = ds.recorded
    check recorded.len >= 1

    var seenValue = -1
    proc prop(v: int) =
      seenValue = v
      ensure true

    let r = fuzzOnceIR(s, prop, recorded)
    check r.outcome == foOk
    check r.value.isSome
    check r.value.get == x
    check seenValue == x

suite "mutateIRPerturbInteger":
  test "perturbs exactly one ckInteger node within its bounds":
    # Hand-craft a 3-int IR. After mutation, exactly one int should
    # differ; both should still satisfy their constraints.
    let c = IntConstraints(min: toInt128(0), max: toInt128(100),
                           shrinkTowards: toInt128(0))
    let base = @[
      ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(10)),
      ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(20)),
      ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(30)),
    ]
    var rng = initSplitMix64(0xBEEF'u64)
    let mutated = mutateIRPerturbInteger(rng, base)
    check mutated.len == base.len
    var diffs = 0
    for i in 0 ..< base.len:
      check mutated[i].kind == ckInteger
      if mutated[i].intVal != base[i].intVal:
        inc diffs
        check permits(mutated[i].intC, mutated[i].intVal)
    check diffs == 1

  test "identity when no ckInteger node present":
    let base = @[
      ChoiceNode(kind: ckBoolean, boolC: BoolConstraints(p: 0.5),
                 boolVal: true),
    ]
    var rng = initSplitMix64(1)
    let mutated = mutateIRPerturbInteger(rng, base)
    check mutated == base

  test "perturbation delta is drawn from the shared logScaledIntDeltas kernel (RFC-fuzzer-nextgen U1)":
    ## fuzzir.nim's integer-perturbation step and the targeted-PBT
    ## hill-climb's own ±2^k step (engine/targeting.nim) used to be two
    ## independently-maintained copies of the identical log-scaled-delta
    ## algorithm, split only to keep fuzzir.nim a leaf module with no
    ## engine deps. U1 dedups them onto one shared kernel
    ## (`logScaledIntDeltas`, now in `nelli/intdeltas`) that both import.
    ## Proven from the fuzz side: whatever single-node change
    ## `mutateIRPerturbInteger` makes, its |delta| must be a member of
    ## the SAME public `logScaledIntDeltas(width)` set the hill-climb
    ## draws from — or the value landed on a clamped range boundary,
    ## the one case where the raw delta itself isn't recoverable.
    let c = IntConstraints(min: toInt128(0), max: toInt128(1_000_000),
                           shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(500_000))]
    let allowedDeltas = logScaledIntDeltas(1_000_000'i64)
    check allowedDeltas.len > 0
    var sawAChange = false
    for seedVal in 0'u64 ..< 60:
      var rng = initSplitMix64(seedVal)
      let mutated = mutateIRPerturbInteger(rng, base)
      let newVal = mutated[0].intVal
      if newVal == base[0].intVal: continue    # this draw happened to no-op
      sawAChange = true
      if newVal == c.min or newVal == c.max:
        continue                               # clamped to a bound; raw delta unrecoverable
      let delta = toInt64(newVal) - toInt64(base[0].intVal)
      check (delta in allowedDeltas) or (-delta in allowedDeltas)
    check sawAChange

  test "perturbed IR replays without rejection (M12 thesis)":
    # The architectural payoff: a byte-flip on a length-prefix routinely
    # decodes into an invalid IR (Overrun → foRejected). An IR perturb
    # of a constrained integer is structurally valid by construction;
    # it must replay through fuzzOnceIR as foOk every time.
    let s = integers(0, 1000)
    var ds = newDataSource(initSplitMix64(0xC0FFEE'u64))
    let _ = s.generate(ds)
    let base = ds.recorded

    proc prop(v: int) = ensure true
    var rng = initSplitMix64(0xD15EA5E'u64)
    var seenOk = 0
    var seenRej = 0
    for _ in 0 ..< 32:
      let mutant = mutateIRPerturbInteger(rng, base)
      let r = fuzzOnceIR(s, prop, mutant)
      case r.outcome
      of foOk: inc seenOk
      of foRejected: inc seenRej
      of foFalsified: discard
    # All 32 mutations are structurally valid: zero rejections.
    check seenRej == 0
    check seenOk == 32

suite "mutateIRKindBoundary":
  test "swaps one node to a kind-respecting boundary value":
    let ic = IntConstraints(min: toInt128(0), max: toInt128(100),
                            shrinkTowards: toInt128(0))
    let base = @[
      ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(50)),
      ChoiceNode(kind: ckBoolean, boolC: BoolConstraints(p: 0.5),
                 boolVal: true),
    ]
    var rng = initSplitMix64(7)
    var changed = false
    for trial in 0 ..< 16:
      let mutated = mutateIRKindBoundary(rng, base)
      check mutated.len == base.len
      var diffs = 0
      var validBoundary = true
      for i in 0 ..< base.len:
        check mutated[i].kind == base[i].kind  # kind preserved
        let neq =
          case base[i].kind
          of ckInteger: mutated[i].intVal != base[i].intVal
          of ckBoolean: mutated[i].boolVal != base[i].boolVal
          of ckFloat:   mutated[i].floatVal != base[i].floatVal
          of ckBytes:   mutated[i].bytesVal != base[i].bytesVal
          of ckString:  mutated[i].strVal  != base[i].strVal
        if neq:
          inc diffs
          case base[i].kind
          of ckInteger:
            validBoundary = permits(mutated[i].intC, mutated[i].intVal)
          of ckBoolean: discard  # any boolean flip is valid
          else: discard
      if diffs > 0:
        check diffs == 1
        check validBoundary
        changed = true
    check changed   # across 16 trials, at least one produced a change

  test "identity when every node is forced":
    let base = @[
      ChoiceNode(kind: ckBoolean, boolC: BoolConstraints(p: 0.5),
                 boolVal: true, wasForced: true),
    ]
    var rng = initSplitMix64(1)
    check mutateIRKindBoundary(rng, base) == base

suite "mutateIRSpanSplice":
  test "replaces a base span with the donor's same-label span":
    # base spans:  [span L=1 covers 0..2)  [span L=2 covers 2..4)
    #              [a, b,                   c, d                  ]
    # donor spans: [span L=1 covers 0..3)
    #              [e, f, g]
    # splice should produce: [e, f, g,      c, d] (donor span 1 → base span 1)
    let ic = IntConstraints(min: toInt128(0), max: toInt128(1000),
                            shrinkTowards: toInt128(0))
    proc mkInt(v: int): ChoiceNode =
      ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(v))
    let base = @[mkInt(1), mkInt(2), mkInt(3), mkInt(4)]
    let baseSpans = @[Span(label: 1, start: 0, finish: 2),
                      Span(label: 2, start: 2, finish: 4)]
    let donor = @[mkInt(10), mkInt(20), mkInt(30)]
    let donorSpans = @[Span(label: 1, start: 0, finish: 3)]

    var rng = initSplitMix64(42)
    let mutated = mutateIRSpanSplice(rng, base, donor, baseSpans, donorSpans)
    # Length: base.len + donor_span_len - base_span_len = 4 + 3 - 2 = 5.
    check mutated.len == 5
    # The first 3 are the donor span; the last 2 are base[2..3].
    check mutated[0].intVal == toInt128(10)
    check mutated[1].intVal == toInt128(20)
    check mutated[2].intVal == toInt128(30)
    check mutated[3].intVal == toInt128(3)
    check mutated[4].intVal == toInt128(4)

  test "identity when no matching-label span pair exists":
    let ic = IntConstraints(min: toInt128(0), max: toInt128(100),
                            shrinkTowards: toInt128(0))
    proc mkInt(v: int): ChoiceNode =
      ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(v))
    let base = @[mkInt(1), mkInt(2)]
    let donor = @[mkInt(9)]
    let baseSpans  = @[Span(label: 1, start: 0, finish: 2)]
    let donorSpans = @[Span(label: 99, start: 0, finish: 1)]
    var rng = initSplitMix64(1)
    check mutateIRSpanSplice(rng, base, donor, baseSpans, donorSpans) == base

  test "identity when either side has no spans":
    let ic = IntConstraints(min: toInt128(0), max: toInt128(100),
                            shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(1))]
    let donor = @[ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(2))]
    var rng = initSplitMix64(1)
    check mutateIRSpanSplice(rng, base, donor, @[], @[]) == base

suite "mutateIRSpanDelete and mutateIRSpanDuplicate":
  test "delete removes one span's nodes; length decreases by span width":
    let ic = IntConstraints(min: toInt128(0), max: toInt128(100),
                            shrinkTowards: toInt128(0))
    proc mkInt(v: int): ChoiceNode =
      ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(v))
    let base = @[mkInt(1), mkInt(2), mkInt(3), mkInt(4), mkInt(5)]
    # one span covers indices [1..4): nodes 2, 3, 4
    let spans = @[Span(label: 7, start: 1, finish: 4)]
    var rng = initSplitMix64(99)
    let mutated = mutateIRSpanDelete(rng, base, spans)
    check mutated.len == 2
    check mutated[0].intVal == toInt128(1)
    check mutated[1].intVal == toInt128(5)

  test "duplicate inserts a copy of one span inline; length doubles the span":
    let ic = IntConstraints(min: toInt128(0), max: toInt128(100),
                            shrinkTowards: toInt128(0))
    proc mkInt(v: int): ChoiceNode =
      ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(v))
    let base = @[mkInt(1), mkInt(2), mkInt(3)]
    # span covers index [0..2): nodes 1, 2
    let spans = @[Span(label: 5, start: 0, finish: 2)]
    var rng = initSplitMix64(99)
    let mutated = mutateIRSpanDuplicate(rng, base, spans)
    check mutated.len == base.len + 2
    check mutated[0].intVal == toInt128(1)
    check mutated[1].intVal == toInt128(2)
    check mutated[2].intVal == toInt128(1)
    check mutated[3].intVal == toInt128(2)
    check mutated[4].intVal == toInt128(3)

  test "identity when no spans available":
    let ic = IntConstraints(min: toInt128(0), max: toInt128(100),
                            shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: ic, intVal: toInt128(1))]
    var rng = initSplitMix64(1)
    check mutateIRSpanDelete(rng, base, @[]) == base
    check mutateIRSpanDuplicate(rng, base, @[]) == base

suite "fuzzWith — IR-mode runner":
  test "irMutation defaults to true; corpus survivors are IR":
    proc fnUnderTest(x: int): int {.cover.} =
      if x > 1000:
        if x mod 7 == 3:
          x * 2
        else:
          x + 1
      else:
        x - 1

    proc prop(x: int) =
      discard fnUnderTest(x)
      ensure true

    let settings = FuzzSettings(maxIterations: 300, seed: 1,
                                timeBudget: initDuration(seconds = 10))
    # RFC-fuzzer-nextgen U3: `FuzzMutationMode`/`mutationMode` is gone — IR is
    # the only mutation kernel `fuzzWith` runs, unconditionally.
    let r = fuzzWith(integers(low(int32), high(int32)), prop, settings)
    check r.iterations >= 1
    check r.coverageHits > 0
    # Survivors live in the IR corpus, not the byte corpus.
    check r.corpus.kind == fckIR
    check r.corpus.irEntries.len >= 1
