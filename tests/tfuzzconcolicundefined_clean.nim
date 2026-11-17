## RFC-0016 K10a-concolic -- `undefinedReached` gets its reader.
##
## The concolic flip reports an operation of the target decision's condition
## it can drive into undefined behaviour (`ConcolicFlipResult.undefinedReached`),
## and never uses that input as a seed. Before this wiring only a counter read
## it, so the fuzzer's concolic bridge found the input and dropped it.
##
## The reader mirrors `annotationViolations`: `tryConcolicBridge` collects each
## `ConcolicUndefined`, one per (kind, site), onto the `Orchestrator`, and
## `FuzzReport.undefinedFindings` hands them to the caller with the witnessing
## input. Verdict-neutral: the witness is never run, so it is not a crash.
##
## Split (RFC-0016 INT-51) so each file runs inside the CI ceiling:
## `tfuzzconcolicundefined_div` holds the campaign that reaches the zero
## divisor, and this file the campaigns that must report none.
import std/unittest
import nelli
import nelli/concolic


## `a div b > a` holds only through `b == 0` (otherwise the quotient is at most
## `a`), and `b == 0` only at `d == 0xCAFEBABE`, a value a random campaign does
## not draw: only the bridge's undefined-side solve can name it.
proc divGate(d: int) {.cover.} =
  let a = uint32(d)
  let b = a - 0xCAFEBABE'u32
  if a > 0'u32:
    if a div b > a:
      discard "wrapped"
    else:
      discard "ok"

proc cleanGate(d: int) {.cover.} =
  let a = uint32(d)
  if a > 0'u32:
    if a div 7'u32 > a:
      discard "never"
    else:
      discard "ok"

suite "K10a-concolic -- undefined behaviour the bridge reaches is reported":
  test "a property with no undefined side reports none":
    let report = fuzzConcolic(integers(0, 0xFFFFFFFF), cleanGate,
                              FuzzSettings(seed: 42'u64, maxIterations: 60))
    check report.undefinedFindings.len == 0
    check formatUndefinedFindings(report) == ""

  test "no assist, no walk: nothing to report":
    let report = fuzz(integers(0, 0xFFFFFFFF), divGate,
                      FuzzSettings(seed: 42'u64, maxIterations: 20))
    check report.undefinedFindings.len == 0
