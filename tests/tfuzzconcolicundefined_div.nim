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
## Split (RFC-0016 INT-51) so each file runs inside the CI ceiling: this file
## holds the campaign that reaches the zero divisor, and
## `tfuzzconcolicundefined_clean` the campaigns that must report none.
import std/[unittest, strutils]
import nelli
import nelli/concolic
import nelli/choice
import nelli/smt/errorkind


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

var divMemo: FuzzReport
var divRan = false

proc divCampaign(): FuzzReport =
  ## The `divGate` campaign (seed 42, 60 iterations). It is deterministic, and
  ## both tests read the same one, so it runs once: run twice, the second
  ## campaign repeated the first and was close to half the old file's run.
  if not divRan:
    divMemo = fuzzConcolic(integers(0, 0xFFFFFFFF), divGate,
                           FuzzSettings(seed: 42'u64, maxIterations: 60))
    divRan = true
  divMemo

suite "K10a-concolic -- undefined behaviour the bridge reaches is reported":
  test "a campaign reports the zero divisor only the undefined side satisfies":
    let report = divCampaign()
    check report.undefinedFindings.len == 1          # deduped across flips
    if report.undefinedFindings.len == 1:
      let f = report.undefinedFindings[0]
      check f.kind == ubUnsignedDivZero
      check f.site.len > 0
      check f.input.len == 1
      check f.input[0].intVal == toInt128(0xCAFEBABE'i64)
    check report.irCrashes.len == 0                  # not a crash
    check report.stats.concolicYield.flip.undefinedReached > 0

  test "the summary names the finding":
    let report = divCampaign()
    let text = formatUndefinedFindings(report)
    check "ubUnsignedDivZero" in text
