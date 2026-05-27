import std/unittest
import proptest

suite "proptest smoke":
  test "package imports and exposes its version":
    check proptestVersion.len > 0
