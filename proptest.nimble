# Package

version       = "0.1.0"
author        = "Corey Leavitt"
description   = "Property-based testing for Nim with internal choice-sequence shrinking (a Hypothesis-style engine)"
license       = "MIT"
srcDir        = "src"

# Dependencies

requires "nim >= 2.0.0"

# Tasks

task test, "Run the test suite":
  exec "nim c -r --hints:off tests/tsmoke.nim"
