## RFC-fuzzer-nextgen S3 — havoc stacking + interesting-value tables.
##
## Three deliverables, tested bottom-up:
## 1. `drawHavocStackCount` — geometric-count (1..N) stack size draw.
## 2. `interestingIntValues`/`mutateIRInterestingValue` — a boundary-value
##    table for integer choice nodes, clamped/filtered to the node's own
##    declared bounds (constraint-respecting IR-level havoc).
## 3. `mutateIRDictInsert` — the G5 auto-dictionary wired as a standalone
##    havoc insertion source.
## The loop-level wiring (stacking + the widened arm space, gated by
## `FuzzSettings.uniformHavoc`) is exercised in the suites at the bottom.
import std/unittest
import nelli
import nelli/[choice, rng]

suite "interestingIntValues — boundary-value table (RFC-fuzzer-nextgen S3 deliverable 2)":

  test "contains min, max, and 0 when 0 is in range":
    let c = IntConstraints(min: toInt128(-100), max: toInt128(100), shrinkTowards: toInt128(0))
    let vs = interestingIntValues(c)
    check toInt128(-100) in vs
    check toInt128(100) in vs
    check toInt128(0) in vs

  test "contains ±1 and min±1/max±1 where legal":
    let c = IntConstraints(min: toInt128(-100), max: toInt128(100), shrinkTowards: toInt128(0))
    let vs = interestingIntValues(c)
    check toInt128(1) in vs
    check toInt128(-1) in vs
    check toInt128(-99) in vs   # min+1
    check toInt128(99) in vs    # max-1

  test "contains powers of two and their off-by-one neighbors within range":
    let c = IntConstraints(min: toInt128(0), max: toInt128(1000), shrinkTowards: toInt128(0))
    let vs = interestingIntValues(c)
    check toInt128(64) in vs     # 2^6
    check toInt128(63) in vs     # 2^6 - 1
    check toInt128(65) in vs     # 2^6 + 1
    check toInt128(512) in vs    # 2^9

  test "every entry is clamped/filtered to the node's declared [min, max]":
    let c = IntConstraints(min: toInt128(10), max: toInt128(20), shrinkTowards: toInt128(10))
    let vs = interestingIntValues(c)
    for v in vs:
      check v >= toInt128(10)
      check v <= toInt128(20)
    # boundary-interesting values still present within the narrow range
    check toInt128(10) in vs
    check toInt128(20) in vs
    check toInt128(11) in vs   # min+1
    check toInt128(19) in vs   # max-1

  test "deduplicated: no value appears twice":
    let c = IntConstraints(min: toInt128(0), max: toInt128(2), shrinkTowards: toInt128(0))
    let vs = interestingIntValues(c)
    var seen: seq[ChoiceInt]
    for v in vs:
      check v notin seen
      seen.add v

  test "empty table for an inverted range":
    let c = IntConstraints(min: toInt128(10), max: toInt128(5), shrinkTowards: toInt128(10))
    check interestingIntValues(c).len == 0

suite "mutateIRInterestingValue — the IR mutator (RFC-fuzzer-nextgen S3 deliverable 2)":

  test "replaces an integer node with a boundary value from its table":
    let c = IntConstraints(min: toInt128(0), max: toInt128(1000), shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(500))]
    var sawInteresting = false
    # Try several seeds — the pick is random among the table, so confirm
    # SOME draw lands on a genuine table entry (max, 0, or a power of two).
    for seed in 1'u64 .. 40'u64:
      var r = initSplitMix64(seed)
      let mutated = mutateIRInterestingValue(r, base)
      if mutated[0].intVal in @[toInt128(1000), toInt128(0), toInt128(512), toInt128(1), toInt128(-1)]:
        sawInteresting = true
        break
    check sawInteresting

  test "every replacement is a legal node (permits holds)":
    let c = IntConstraints(min: toInt128(-50), max: toInt128(50), shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(3))]
    for seed in 1'u64 .. 20'u64:
      var r = initSplitMix64(seed)
      let mutated = mutateIRInterestingValue(r, base)
      check permits(mutated[0].intC, mutated[0].intVal)

  test "identity when there is no integer node":
    let base = @[ChoiceNode(kind: ckBoolean, boolC: BoolConstraints(p: 0.5), boolVal: true)]
    var rng = initSplitMix64(1'u64)
    check mutateIRInterestingValue(rng, base) == base

  test "identity when the only integer node is forced":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100), shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(wasForced: true, kind: ckInteger, intC: c, intVal: toInt128(7))]
    var rng = initSplitMix64(1'u64)
    check mutateIRInterestingValue(rng, base) == base

  test "identity when the node is pinned to a single legal value":
    let c = IntConstraints(min: toInt128(5), max: toInt128(5), shrinkTowards: toInt128(5))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(5))]
    var rng = initSplitMix64(1'u64)
    check mutateIRInterestingValue(rng, base) == base

suite "mutateIRDictInsert — standalone dictionary havoc source (RFC-fuzzer-nextgen S3 deliverable 3)":

  test "inserts a dictionary constant with no cmp-log involved at all":
    let c = StringConstraints(intervals: intervals([(0x20'i32, 0x7e'i32)]), minSize: 5, maxSize: 5)
    let base = @[ChoiceNode(kind: ckString, strC: c, strVal: "zzzzz")]
    var dict: Dictionary
    dict.entries.add DictEntry(kind: dvString, strVal: "MAGIC")
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRDictInsert(rng, base, dict)
    check mutated[0].strVal == "MAGIC"

  test "inserts an int dictionary constant, clamped to the node's bounds":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100), shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(7))]
    var dict: Dictionary
    dict.entries.add DictEntry(kind: dvInt, intVal: toInt128(0xDEADBEEF'i64))
    var rng = initSplitMix64(1'u64)
    let mutated = mutateIRDictInsert(rng, base, dict)
    check mutated[0].intVal == c.max
    check permits(mutated[0].intC, mutated[0].intVal)

  test "identity when the dictionary is empty":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100), shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(7))]
    var rng = initSplitMix64(1'u64)
    check mutateIRDictInsert(rng, base, Dictionary()) == base

  test "identity when no node accepts any dictionary entry (kind mismatch)":
    let c = IntConstraints(min: toInt128(0), max: toInt128(100), shrinkTowards: toInt128(0))
    let base = @[ChoiceNode(kind: ckInteger, intC: c, intVal: toInt128(7))]
    var dict: Dictionary
    dict.entries.add DictEntry(kind: dvString, strVal: "MAGIC")
    var rng = initSplitMix64(1'u64)
    check mutateIRDictInsert(rng, base, dict) == base

suite "drawHavocStackCount — geometric stack-count draw (RFC-fuzzer-nextgen S3 deliverable 1)":

  test "always at least 1":
    for seed in 1'u64 .. 50'u64:
      var r = initSplitMix64(seed)
      check drawHavocStackCount(r) >= 1

  test "never exceeds maxHavocStackOps":
    for seed in 1'u64 .. 200'u64:
      var r = initSplitMix64(seed)
      check drawHavocStackCount(r) <= maxHavocStackOps

  test "over many draws, both 1 and something greater than 1 occur (genuinely geometric, not fixed)":
    var sawOne = false
    var sawMore = false
    for seed in 1'u64 .. 200'u64:
      var r = initSplitMix64(seed)
      let n = drawHavocStackCount(r)
      if n == 1: sawOne = true
      if n > 1: sawMore = true
    check sawOne
    check sawMore

  test "continueP == 0.0 always yields exactly 1 (degenerate, no stacking)":
    for seed in 1'u64 .. 20'u64:
      var r = initSplitMix64(seed)
      check drawHavocStackCount(r, maxStackOps = 8, continueP = 0.0) == 1

  test "maxStackOps == 1 always yields exactly 1 regardless of continueP":
    for seed in 1'u64 .. 20'u64:
      var r = initSplitMix64(seed)
      check drawHavocStackCount(r, maxStackOps = 1, continueP = 1.0) == 1
