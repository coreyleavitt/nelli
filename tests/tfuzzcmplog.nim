## RFC-fuzzer-nextgen G4 (C1) — the Nim-tier comparison hook: a `{.cover.}`-
## sibling pragma (`{.covercmp.}`) that injects a `logCmp(lhs, rhs, op)` call
## at each comparison operator, logging the TYPED operand pair (integer AND
## bytes/string — `ckBytes`/`ckString`) into a per-thread log. Mirrors
## `coverage.nim`'s `{.cover.}`/`recordEdge` mechanism: gated by a runtime
## mode (`clOff` by default, zero cost until a caller opts in), and the hook
## itself is `{.symexOpaque.}` so a property that is BOTH `{.cover.}`'d and
## `{.covercmp.}`'d still walks cleanly under `concolicFlip` (G3fix's
## instrumentation-opacity precedent — `recordEdge` got the same treatment).
##
## This file exercises the IN-PROCESS log (recording mode, snapshot, reset,
## typed entries, serialization round-trip). The shm transport is
## `tests/tfuzzcmplogshm.nim` (G4 C2); the external `trace-cmp` runtime is
## `tests/tfuzzcbuild.nim`'s cmp-log suite (G4 C3).
import std/unittest
import nelli

proc intGate(x: int) {.covercmp.} =
  if x == 0xDEADBEEF:
    discard "hit"
  else:
    discard "miss"

proc bytesGate(b: seq[byte]) {.covercmp.} =
  if b == @[byte(0x4D), byte(0x41), byte(0x47), byte(0x49), byte(0x43)]:  # "MAGIC"
    discard "hit"
  else:
    discard "miss"

proc stringGate(s: string) {.covercmp.} =
  if s == "MAGIC":
    discard "hit"
  else:
    discard "miss"

proc orderedGate(x: int) {.covercmp.} =
  if x < 10:
    discard "lo"
  elif x >= 100:
    discard "hi"
  else:
    discard "mid"

proc uninterestingGate(a, b: bool; c, d: float) {.covercmp.} =
  # Non-int/bytes/string comparisons must compile clean (generic no-op
  # overload) and must never appear in the log.
  if a == b:
    discard "bools equal"
  if c < d:
    discard "floats ordered"

proc coverAndCovercmpGate(x: int) {.cover, covercmp.} =
  ## Combining BOTH pragmas on the same proc must compile and both
  ## instrumentations must fire independently (cover's branch-edge bitmap,
  ## covercmp's operand log) — they touch disjoint AST positions (branch
  ## bodies vs. comparison expressions) so composition is orthogonal.
  if x == 0xCAFEBABE:
    discard "hit"
  else:
    discard "miss"

suite "RFC-fuzzer-nextgen G4 C1 — Nim-tier comparison hook (in-process log)":

  setup:
    resetCmpLog()
    setCmpLogMode(clOff)

  teardown:
    setCmpLogMode(clOff)
    resetCmpLog()

  test "default mode (clOff) logs nothing — zero cost for a non-opted-in caller":
    intGate(0xDEADBEEF)
    check currentCmpLog().len == 0

  test "clRecording logs the observed/constant operand pair for an int comparison":
    setCmpLogMode(clRecording)
    intGate(42)
    let entries = parseCmpLog(currentCmpLog())
    check entries.len == 1
    check entries[0].kind == clkInt
    check entries[0].op == coEq
    check entries[0].width == sizeof(int)
    check (entries[0].lhsInt == 42'u64 or entries[0].rhsInt == 42'u64)
    check (entries[0].lhsInt == 0xDEADBEEF'u64 or entries[0].rhsInt == 0xDEADBEEF'u64)

  test "clRecording logs the typed bytes operand pair (ckBytes)":
    setCmpLogMode(clRecording)
    bytesGate(@[byte(1), byte(2)])
    let entries = parseCmpLog(currentCmpLog())
    check entries.len == 1
    check entries[0].kind == clkBytes
    check entries[0].op == coEq
    check (entries[0].lhsBytes == @[byte(1), byte(2)] or entries[0].rhsBytes == @[byte(1), byte(2)])
    let magic = @[byte(0x4D), byte(0x41), byte(0x47), byte(0x49), byte(0x43)]
    check (entries[0].lhsBytes == magic or entries[0].rhsBytes == magic)

  test "clRecording logs the typed string operand pair (ckString)":
    setCmpLogMode(clRecording)
    stringGate("hello")
    let entries = parseCmpLog(currentCmpLog())
    check entries.len == 1
    check entries[0].kind == clkString
    check (entries[0].lhsStr == "hello" or entries[0].rhsStr == "hello")
    check (entries[0].lhsStr == "MAGIC" or entries[0].rhsStr == "MAGIC")

  test "each of <, >=, == gets its own typed op-tagged entry":
    setCmpLogMode(clRecording)
    orderedGate(50)
    let entries = parseCmpLog(currentCmpLog())
    check entries.len == 2         # `x < 10` then `x >= 100` (elif chain evaluates both)
    check entries[0].op == coLt
    check entries[1].op == coGe

  test "non-int/bytes/string comparisons compile and are silently skipped (no log entry)":
    setCmpLogMode(clRecording)
    uninterestingGate(true, true, 1.0, 2.0)
    check parseCmpLog(currentCmpLog()).len == 0

  test "resetCmpLog clears the buffer between runs (per-run isolation, like resetCoverage)":
    setCmpLogMode(clRecording)
    intGate(1)
    check parseCmpLog(currentCmpLog()).len == 1
    resetCmpLog()
    check currentCmpLog().len == 0
    intGate(2)
    check parseCmpLog(currentCmpLog()).len == 1   # not 2 — the prior entry didn't survive reset

  test "{.cover.} and {.covercmp.} compose on the same proc":
    setCoverageMode(cmRecording)
    setCmpLogMode(clRecording)
    resetCoverage()
    coverAndCovercmpGate(0xCAFEBABE)
    check currentCoverage() >= 1                  # cover's branch-edge hit
    let entries = parseCmpLog(currentCmpLog())
    check entries.len == 1                        # covercmp's operand-pair hit
    check entries[0].kind == clkInt
    setCoverageMode(cmOff)

  test "parseCmpLog gracefully truncates a cut-off trailing record instead of raising":
    setCmpLogMode(clRecording)
    intGate(7)
    var raw = currentCmpLog()
    raw.setLen(raw.len - 3)             # chop off the tail mid-record
    let entries = parseCmpLog(raw)      # must not raise
    check entries.len == 0              # the one (now-truncated) record is dropped, not fabricated
