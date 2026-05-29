import std/unittest
import proptest

# #106 — runtime gate on the coverage bitmap. Default policy is opt-in:
# `recordEdge` is a no-op until the caller opts into `cmRecording`, so a
# {.cover.}'d proc imposes zero runtime cost on consumers who haven't
# asked for coverage.

suite "coverage runtime toggle":
  test "default mode is cmOff; recordEdge does nothing":
    setCoverageMode(cmOff)              # establish a known starting state
    resetCoverage()
    check currentCoverageMode() == cmOff
    recordEdge(1)
    recordEdge(2)
    check currentCoverage() == 0

  test "setCoverageMode(cmRecording) enables the bitmap":
    setCoverageMode(cmRecording)
    resetCoverage()
    check currentCoverageMode() == cmRecording
    recordEdge(11)
    recordEdge(22)
    check currentCoverage() == 2
    setCoverageMode(cmOff)              # clean up so we don't leak state

  test "switching back to cmOff freezes the bitmap":
    setCoverageMode(cmRecording)
    resetCoverage()
    recordEdge(5)
    recordEdge(6)
    check currentCoverage() == 2
    setCoverageMode(cmOff)
    recordEdge(7)                       # ignored — mode is cmOff
    check currentCoverage() == 2
