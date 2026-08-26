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
                          FuzzSettings(seed: 42'u64, maxIterations: 200, enableI2S: true))
    check report.coverageHits == 2   # both the "hit" and "miss" edges

  test "the identical campaign with enableI2S left at false (the default) does not":
    let report = fuzzWith(integers(0, 0xFFFFFFFF), deadbeefGate,
                          FuzzSettings(seed: 42'u64, maxIterations: 200))
    check report.coverageHits == 1   # only "miss" — mutation alone can't hit 1-in-4B
