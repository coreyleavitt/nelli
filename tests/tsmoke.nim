import std/unittest
import proptest

suite "proptest smoke":
  test "package imports and exposes its version":
    check proptestVersion.len > 0

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
