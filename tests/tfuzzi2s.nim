## RFC-fuzzer-nextgen G5 — IR-level I2S replacement + auto-dictionary.
##
## G4 (`{.covercmp.}`/`logCmp`, coverage.nim) logs a run's typed comparison
## operand pairs. This suite drives the CONSUMER: `mutateIRI2SReplace`
## (fuzzir.nim) maps a logged operand back to the `ChoiceNode`(s) whose
## concrete value produced it (exact, per §G-cmp's identity-flow scope — the
## typed-provenance win over byte-offset-guessing RedQueen) and emits a
## mutant with that node's value replaced by the OTHER (constant) operand.
## Wired as fuzz.nim's 6th mutation operator, gated on `FuzzSettings.enableI2S`
## (opt-in — off by default, so a pre-G5 campaign's RNG-consumption/trajectory
## is byte-for-byte unchanged, matching every other additive knob's convention
## in this loop: `stallRounds`, `uniformSchedule`, `reVerify`).
##
## Headline (deliverables 1+2): a multi-byte-constant gate that random
## mutation cannot reasonably pass (`0xDEADBEEF`, a `"MAGIC"` string) IS
## passed by I2S alone — `stallRounds: 0`, no concolic bridge, no Z3.
import std/unittest
import nelli
import nelli/[datasource, choice, rng]

suite "mutateIRI2SReplace — operand-log -> choice-node mapping (int)":

  test "exact match: node's value equals the logged lhs -> replaced with rhs":
    let c = IntConstraints(min: toInt128(0), max: toInt128(0xFFFFFFFF'i64),
                           shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(7))]
    let log = @[CmpLogEntry(kind: clkInt, op: coEq, width: sizeof(int),
                            lhsInt: 7'u64, rhsInt: 0xDEADBEEF'u64)]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated.len == 1
    check mutated[0].intVal == toInt128(0xDEADBEEF'i64)
    check permits(mutated[0].intC, mutated[0].intVal)

  test "exact match on the OTHER side: node's value equals the logged rhs -> replaced with lhs":
    let c = IntConstraints(min: toInt128(0), max: toInt128(0xFFFFFFFF'i64),
                           shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(0xDEADBEEF'i64))]
    let log = @[CmpLogEntry(kind: clkInt, op: coEq, width: sizeof(int),
                            lhsInt: 7'u64, rhsInt: 0xDEADBEEF'u64)]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated[0].intVal == toInt128(7)

  test "out-of-range replacement is clamped into the node's declared bounds, not skipped":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100),
                           shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(7))]
    let log = @[CmpLogEntry(kind: clkInt, op: coEq, width: sizeof(int),
                            lhsInt: 7'u64, rhsInt: 0xDEADBEEF'u64)]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated[0].intVal == c.max          # clamped, still a legal node
    check permits(mutated[0].intC, mutated[0].intVal)

  test "identity when no node's value matches any logged operand":
    let c = IntConstraints(min: toInt128(0), max: toInt128(0xFFFFFFFF'i64),
                           shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(99))]
    let log = @[CmpLogEntry(kind: clkInt, op: coEq, width: sizeof(int),
                            lhsInt: 7'u64, rhsInt: 0xDEADBEEF'u64)]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated == base

  test "identity when the log is empty (no {.covercmp.} instrumentation fired)":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100),
                           shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(7))]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, @[], Dictionary())
    check mutated == base

  test "a forced node is never a replacement target":
    let c = IntConstraints(min: toInt128(0), max: toInt128(0xFFFFFFFF'i64),
                           shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(wasForced: true, kind: ckInteger, intC: c, intVal: toInt128(7))]
    let log = @[CmpLogEntry(kind: clkInt, op: coEq, width: sizeof(int),
                            lhsInt: 7'u64, rhsInt: 0xDEADBEEF'u64)]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated == base

proc deadbeefGate(x: int) {.cover, covercmp.} =
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

suite "RFC-fuzzer-nextgen G5 headline — I2S solves a wide-int constant gate WITHOUT concolic":

  test "enableI2S: true breaks the 0xDEADBEEF gate (stallRounds: 0, no concolic bridge)":
    let report = fuzzWith(integers(0, 0xFFFFFFFF), deadbeefGate,
                          FuzzSettings(seed: 42'u64, maxIterations: 200, guidance: GuidanceConfig(enableI2S: true)))
    check report.coverageHits == 2   # both the "hit" and "miss" edges

  test "the identical campaign with enableI2S left at false (the default) does not":
    let report = fuzzWith(integers(0, 0xFFFFFFFF), deadbeefGate,
                          FuzzSettings(seed: 42'u64, maxIterations: 200))
    check report.coverageHits == 1   # only "miss" — mutation alone can't hit 1-in-4B

suite "mutateIRI2SReplace — operand-log -> choice-node mapping (bytes/string)":

  test "exact bytes match: node's value equals the logged lhs bytes -> replaced with rhs":
    let c = BytesConstraints(minSize: 5, maxSize: 5)
    let base = @[ChoiceNode(kind: ckBytes, bytesC: c, bytesVal: @[byte(1), 2, 3, 4, 5])]
    let magic = @[byte(0x4D), byte(0x41), byte(0x47), byte(0x49), byte(0x43)]  # "MAGIC"
    let log = @[CmpLogEntry(kind: clkBytes, op: coEq,
                            lhsBytes: @[byte(1), 2, 3, 4, 5], rhsBytes: magic)]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated[0].bytesVal == magic

  test "exact string match: node's value equals the logged lhs string -> replaced with rhs":
    let c = StringConstraints(intervals: intervals([(0x20'i32, 0x7e'i32)]), minSize: 5, maxSize: 5)
    let base = @[ChoiceNode(kind: ckString, strC: c, strVal: "xxxxx")]
    let log = @[CmpLogEntry(kind: clkString, op: coEq, lhsStr: "xxxxx", rhsStr: "MAGIC")]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated[0].strVal == "MAGIC"

  test "a string replacement violating the node's constraints is skipped, not fabricated":
    let c = StringConstraints(intervals: intervals([(0x20'i32, 0x7e'i32)]), minSize: 2, maxSize: 2)
    let base = @[ChoiceNode(kind: ckString, strC: c, strVal: "xx")]
    let log = @[CmpLogEntry(kind: clkString, op: coEq, lhsStr: "xx", rhsStr: "MAGIC")]  # len 5, out of [2,2]
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRI2SReplace(rng, base, log, Dictionary())
    check mutated == base   # no legal replacement -> identity

proc rawBytesStrategy(minLen, maxLen: int): Strategy[seq[byte]] =
  ## A `seq[byte]` strategy over `datasource.drawBytes` — a SINGLE `ckBytes`
  ## choice node, not the public `bytes()` strategy's `lists(integers(0,
  ## 255))` decomposition (which records one `ckInteger` node PER byte plus
  ## per-element continuation `ckBoolean`s — no single node ever carries the
  ## whole byte string, so an exact node-level I2S match can never apply to
  ## it). §G-cmp's own scope is "the typed choice nodes... ckBytes/ckString";
  ## this is the strategy shape that scope describes — mirrors how
  ## `strings()` already draws one `ckString` node via `drawString`.
  Strategy[seq[byte]](run: proc(src: var DataSource): seq[byte] =
    result = src.drawBytes(minLen, maxLen))

proc magicBytesGate(b: seq[byte]) {.cover, covercmp.} =
  if b == @[byte(0x4D), byte(0x41), byte(0x47), byte(0x49), byte(0x43)]:  # "MAGIC"
    discard "hit"
  else:
    discard "miss"

proc magicStringGate(s: string) {.cover, covercmp.} =
  if s == "MAGIC":
    discard "hit"
  else:
    discard "miss"

suite "RFC-fuzzer-nextgen G5 headline — I2S solves the multi-byte-constant gate WITHOUT concolic":

  test "enableI2S: true breaks a fixed-length seq[byte] \"MAGIC\" gate (ckBytes)":
    let report = fuzzWith(rawBytesStrategy(5, 5), magicBytesGate,
                          FuzzSettings(seed: 7'u64, maxIterations: 200, guidance: GuidanceConfig(enableI2S: true)))
    check report.coverageHits == 2

  test "the identical seq[byte] campaign with enableI2S left at false (the default) does not":
    let report = fuzzWith(rawBytesStrategy(5, 5), magicBytesGate,
                          FuzzSettings(seed: 7'u64, maxIterations: 200))
    check report.coverageHits == 1

  test "enableI2S: true breaks a fixed-length string \"MAGIC\" gate (ckString) — the RFC's own example":
    let report = fuzzWith(strings(5, 5), magicStringGate,
                          FuzzSettings(seed: 7'u64, maxIterations: 200, guidance: GuidanceConfig(enableI2S: true)))
    check report.coverageHits == 2

  test "the identical string campaign with enableI2S left at false (the default) does not":
    let report = fuzzWith(strings(5, 5), magicStringGate,
                          FuzzSettings(seed: 7'u64, maxIterations: 200))
    check report.coverageHits == 1

suite "harvestDictionary — auto-dictionary accumulation (RFC-fuzzer-nextgen G5 deliverable 3)":

  test "an int comparison's constant operand is harvested into the dictionary":
    var dict: Dictionary
    let log = @[CmpLogEntry(kind: clkInt, op: coEq, width: sizeof(int),
                            lhsInt: 7'u64, rhsInt: 0xDEADBEEF'u64)]
    harvestDictionary(dict, log)
    var found = false
    for e in dict.entries:
      if e.kind == dvInt and e.intVal == toInt128(0xDEADBEEF'i64): found = true
    check found

  test "a bytes/string comparison's operands are both harvested":
    var dict: Dictionary
    let magic = @[byte(0x4D), byte(0x41), byte(0x47), byte(0x49), byte(0x43)]
    let log = @[CmpLogEntry(kind: clkBytes, op: coEq, lhsBytes: @[byte(1)], rhsBytes: magic),
                CmpLogEntry(kind: clkString, op: coEq, lhsStr: "x", rhsStr: "MAGIC")]
    harvestDictionary(dict, log)
    var foundBytes, foundString = false
    for e in dict.entries:
      if e.kind == dvBytes and e.bytesVal == magic: foundBytes = true
      if e.kind == dvString and e.strVal == "MAGIC": foundString = true
    check foundBytes
    check foundString

  test "re-harvesting the same operand does not grow the dictionary (deduped)":
    var dict: Dictionary
    let log = @[CmpLogEntry(kind: clkString, op: coEq, lhsStr: "x", rhsStr: "MAGIC")]
    harvestDictionary(dict, log)
    let sizeAfterFirst = dict.entries.len
    harvestDictionary(dict, log)
    check dict.entries.len == sizeAfterFirst

  test "mutateIRI2SReplace falls back to the dictionary when the log has no direct match":
    let c = StringConstraints(intervals: intervals([(0x20'i32, 0x7e'i32)]), minSize: 5, maxSize: 5)
    let base = @[ChoiceNode(kind: ckString, strC: c, strVal: "zzzzz")]
    var dict: Dictionary
    dict.entries.add DictEntry(kind: dvString, strVal: "MAGIC")
    var rng = initSplitMix64(1'u64)
    # empty log — no direct I2S match possible, only the dictionary can supply a replacement
    let mutated = mutateIRI2SReplace(rng, base, @[], dict)
    check mutated[0].strVal == "MAGIC"

  test "a campaign accumulates its comparison constants into report.dictionary":
    let report = fuzzWith(integers(0, 0xFFFFFFFF), deadbeefGate,
                          FuzzSettings(seed: 42'u64, maxIterations: 200, guidance: GuidanceConfig(enableI2S: true)))
    var found = false
    for e in report.dictionary.entries:
      if e.kind == dvInt and e.intVal == toInt128(0xDEADBEEF'i64): found = true
    check found

  test "enableI2S left at false never harvests anything (opt-out is inert, per its own contract)":
    let report = fuzzWith(integers(0, 0xFFFFFFFF), deadbeefGate,
                          FuzzSettings(seed: 42'u64, maxIterations: 200))
    check report.dictionary.entries.len == 0
