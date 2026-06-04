## Phase 4.5 (docs/fuzz/FUZZ_PLAN.md): the external-execution contract — pure logic,
## no subprocess. InputDelivery built-ins (D13), Oracle built-ins over a stub RunResult
## (D14), and the default coverage-fingerprint crashKey (D11). Phase 5 wires the real child.

import std/unittest
import proptest

proc tb(s: string): seq[byte] =
  result = newSeq[byte](s.len)
  for i in 0 ..< s.len: result[i] = byte(s[i])

suite "fuzz: external-execution contract (Phase 4.5)":
  test "stdinDelivery: input on stdin, argv unchanged":
    let plan = stdinDelivery().plan(@[0x41'u8, 0x42], @["./t", "-x"], "/tmp/run")
    check plan.argv == @["./t", "-x"]
    check plan.stdin == @[0x41'u8, 0x42]
    check plan.filesToWrite.len == 0

  test "argvFileDelivery: @@ → temp file path; file scheduled for write + clean":
    let plan = argvFileDelivery(".nim").plan(@[0x41'u8], @["./nim", "c", "@@"], "/tmp/run")
    check plan.argv == @["./nim", "c", "/tmp/run/ptinput.nim"]
    check plan.filesToWrite.len == 1
    check plan.filesToWrite[0].path == "/tmp/run/ptinput.nim"
    check plan.filesToWrite[0].content == @[0x41'u8]
    check plan.filesToClean == @["/tmp/run/ptinput.nim"]
    check plan.stdin.len == 0

  test "envVarDelivery: input as an env var value":
    let plan = envVarDelivery("PT_INPUT").plan(tb("hi"), @["./t"], "/tmp/run")
    check plan.env == @[("PT_INPUT", "hi")]

  test "signalOracle: signal/non-zero → interesting; timeout → timed out; clean → ok":
    let o = signalOracle[int]()
    check o.judge(RunResult(signal: 11), 0) == vInteresting
    check o.judge(RunResult(exitCode: 1), 0) == vInteresting
    check o.judge(RunResult(timedOut: true), 0) == vTimedOut
    check o.judge(RunResult(exitCode: 0), 0) == vOk

  test "sanitizerOracle: a stderr report is a finding even on exit 0":
    let o = sanitizerOracle[int]()
    check o.judge(RunResult(exitCode: 0,
      stderr: tb("==ERROR: AddressSanitizer: heap-use-after-free")), 0) == vInteresting
    check o.judge(RunResult(exitCode: 0, stderr: @[]), 0) == vOk

  test "exitCodeOracle: only listed codes are bugs":
    let o = exitCodeOracle[int]({1'u8, 134'u8})
    check o.judge(RunResult(exitCode: 1), 0) == vInteresting
    check o.judge(RunResult(exitCode: 2), 0) == vOk          # not in the set
    check o.judge(RunResult(signal: 6), 0) == vInteresting   # a signal is always a finding

  test "coverageFingerprint keys the edge SET, not the counts":
    let a = Coverage(counters: @[1'u8, 0, 1, 0])
    let b = Coverage(counters: @[5'u8, 0, 9, 0])             # same slots set, diff counts
    let c = Coverage(counters: @[1'u8, 1, 0, 0])             # a different slot set
    check coverageFingerprint(a) == coverageFingerprint(b)
    check coverageFingerprint(a) != coverageFingerprint(c)
