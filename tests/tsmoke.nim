import std/unittest
import proptest

suite "proptest smoke":
  test "package imports and exposes its version":
    check proptestVersion.len > 0

  test "DataSource draw methods are reachable through 'import proptest' alone":
    # `newStrategy` is the public escape hatch for custom strategies, so the
    # methods a custom strategy actually calls on its `DataSource` parameter
    # must be reachable from the same import. Without these re-exports the
    # documented path doesn't compile.
    check compiles(block:
      let s = newStrategy(proc(src: var DataSource): int =
        let v = src.drawInteger(toInt128(0), toInt128(10), toInt128(0))
        let _ = src.drawBoolean(0.5)
        let _ = src.drawFloat(0.0, 1.0, false, 0.0)
        let _ = src.drawBytes(0, 4)
        let _ = src.drawString(intervals([(0x61'i32, 0x7a'i32)]), 0, 4)
        src.startSpan(0)
        src.endSpan()
        discard src.isReplaying
        discard src.nextRoll
        toInt64(v).int)
      discard s)

  test "internal modules are not bulk-re-exported through proptest":
    # The public surface is `strategy`, `engine`, `dsl`, `derive`, `db`,
    # `stateful` (plus the supporting types they re-export). Choice IR,
    # serialize, raw RNG, raw DataSource, and shrinker internals must NOT be
    # implicit imports — users who need them should reach for the submodule.
    check not compiles(integerChoice(1, 0, 10, 0))       # choice
    check not compiles(toBytes(@[integerChoice(1, 0, 10, 0)]))  # serialize
    check not compiles(initSplitMix64(1))                # rng
    check not compiles(newDataSource(initSplitMix64(1))) # datasource
    check not compiles(complexity(integerChoice(1, 0, 10, 0)))  # shrinker
