## Phase 1a (docs/fuzz/FUZZ_PLAN.md): prove nelli's test harness can build +
## run an instrumented EXTERNAL C target. Net-new machinery — nelli had no
## C-compilation and no subprocess use in its tests before this. The build helpers
## live in fuzzsupport.nim; this just exercises the dual backend at the smallest
## scope. A backend whose compiler or sancov flag is absent is skipped, never failed.

import std/[unittest, os, osproc]
import fuzzsupport
import nelli

const branchTarget = """
int main(int argc, char** argv) {
  if (argc > 1 && argv[1][0] == 'x') return 3;   /* a branch coverage will differ on */
  return 0;
}
"""

suite "fuzz: instrumented-C build + run scaffold (Phase 1a)":
  test "at least one coverage backend is available":
    # gcc is always present in the stock nimlang image (Linux), and the
    # `fuzzer-windows` CI leg's own toolchain carries both gcc and clang
    # (RFC-fuzzer-nextgen Eci) — so the scaffold can actually exercise
    # something on either platform. RFC-fuzzer-nextgen E4c: `available`
    # (fuzzsupport.nim) no longer hardcodes false off POSIX (its own doc
    # comment explains what changed), so this assertion now holds
    # everywhere; a hypothetical environment with neither compiler would
    # still fail loudly here rather than silently skip a premise every
    # OTHER test in this suite depends on.
    #
    # That hypothetical environment turned out to be real: the MSVC parity
    # leg runs inside a toolchain container that ships cl.exe and NO
    # gcc/clang, so the external-C scaffold has no backend to build with
    # there. It declares that explicitly via $NELLI_NO_COV_BACKEND rather
    # than this test inferring it from the platform — an environment that
    # promises a backend and then lacks one (a Linux image that lost gcc,
    # say) must still fail here, loudly, exactly as before.
    if getEnv("NELLI_NO_COV_BACKEND") == "1":
      skip()
    else:
      check (available(cbGcc) or available(cbClang))

  for backend in [cbGcc, cbClang]:
    test "build & run an instrumented C target — " & $backend:
      if not available(backend):
        skip()
      else:
        let bin = buildInstrumented(backend, @[branchTarget], noopRuntime(backend))
        let (_, code0) = execCmdEx(quoteShell(bin))
        check code0 == 0                       # default path
        let (_, code3) = execCmdEx(quoteShell(bin) & " x")
        check code3 == 3                       # the branch was taken
        removeDir(bin.parentDir)

# --- trace-cmp: the external tier's comparison-operand log (RFC-fuzzer-nextgen G4 C3) ----
#
# `nelli_cov.c`'s __sanitizer_cov_trace_cmp*/`_const_cmp*` hooks, built via
# `-fsanitize-coverage=inline-8bit-counters,trace-cmp` (clang-only — gcc's
# sancov subset has no trace-cmp analog). Real end-to-end interop: the C
# PRODUCER (a fresh child process) publishes to the cmp log's shm channel at
# exit; the Nim ORCHESTRATOR side (`shmReadCmpLog`, `coverage.nim`) reads it
# back — the SAME wire format and channel machinery a persistent Nim worker
# uses (`tfuzzcmplogshm.nim`), now proven from an independent C writer.

const cmpGateTarget = """
#include <stdlib.h>
int main(int argc, char** argv) {
  int x = (argc > 1) ? atoi(argv[1]) : 0;
  if (x == 0xDEADBEEF) return 3;   /* the comparison trace-cmp logs the operand pair for */
  return 0;
}
"""

let cmpCovRuntime = embedCSource("../src/nelli/nelli_cov.c")
  ## `let`, not `const` — chunked via `embedCSource` (MSVC's 16380-byte
  ## C2026 single-string-literal cap; `nelli_cov.c` is 26100 bytes; a
  ## `const` would re-fold the chunks back into one oversized literal).
const magicOperand = 0xDEADBEEF'u64

# The G4 C3 suite reads the cmp log back over the shm channel
# (`shmReadCmpLog`, coverage.nim) — POSIX-only through E4a, widened to
# `when defined(posix) or defined(windows)` by E4b (Windows shm coverage:
# CreateFileMapping/MapViewOfFile). RFC-fuzzer-nextgen E4c: the OTHER half
# of this suite's platform gate — `available`/`traceCmpSupported`
# (fuzzsupport.nim) no longer hardcode false off POSIX either (their own
# doc comments explain what changed: `nelli_cov.c`/`nelli_shm.c` both now
# build clean on Windows) — so this suite runs everywhere the flag probe
# says trace-cmp is supported, not just on POSIX. The Phase 1a build
# scaffold suite above already stays live on every platform.
suite "fuzz: trace-cmp external-tier operand log (RFC-fuzzer-nextgen G4 C3)":
  test "trace-cmp flag is accepted, or this test skips (clang-only, no gcc analog)":
    # Not a hard requirement that clang itself be absent — an OLD clang
    # predating `trace-cmp` still counts as "not supported," matching
    # `flagSupported`'s own probe-don't-assume discipline.
    check traceCmpSupported() or not available(cbClang)

  test "an instrumented external binary logs its comparison operands, read back by the orchestrator over shm":
    if not traceCmpSupported():
      skip()
    else:
      let bin = buildInstrumentedTraceCmp(@[cmpGateTarget], cmpCovRuntime)
      let shmName = "/nelli_g4c3_" & $getCurrentProcessId()
      shmHoldCmpLog(shmName)
        # RFC-fuzzer-nextgen E4c C3 round 3: pre-attach BEFORE spawning the
        # child — see `shmHoldCmpLog`'s own doc comment (coverage.nim) for
        # why: this test's own `NELLI_COV_DEBUG` trail (round 2) proved the
        # child published correctly every time; the reader still saw 0
        # entries because a Windows named file mapping is destroyed when its
        # LAST handle closes, and `execCmdEx` below fully waits for the
        # child to exit before this test ever attached its own handle —
        # attaching FIRST, while this (long-lived) test process is the one
        # holding it, keeps the segment alive across the child's entire
        # spawn-publish-exit lifecycle.
      putEnv("NELLI_CMP_SHM", shmName)
      putEnv("NELLI_COV_DEBUG", "1")
        # RFC-fuzzer-nextgen E4c C3 round 2: opt-in fprintf(stderr) trail in
        # nelli_cov.c/nelli_shm.c's publish path (runtime init, env-var
        # read + transformed segment name, each publish attempt with entry
        # count, CreateFileMapping/MapViewOfFile failure codes) --
        # `execCmdEx`'s merged stdout+stderr capture below surfaces it
        # through THIS test's own diagnostic echo on the next CI round.
      let (output, code) = execCmdEx(quoteShell(bin) & " 42")   # a non-magic value: the comparison still fires
      delEnv("NELLI_CMP_SHM")
      delEnv("NELLI_COV_DEBUG")
      # RFC-fuzzer-nextgen E4c C3 fix-up (fuzzer-windows CI runs 33017017592
      # then 33019262657 both FAILED here on Windows: `entries.len >= 1` was
      # 0 — POSIX has always been green; the C-level trace-cmp -> nelli_shm.c
      # shm publish path this depends on could not be further diagnosed or
      # fixed blind, since no mingw-targeted clang exists in this repo's
      # local toolchain to probe whether Windows-native clang's
      # `-fsanitize-coverage=...,trace-cmp` genuinely emits
      # `__sanitizer_cov_trace_cmp*` calls for a COFF/PE target the way it
      # does for native/ELF (a real, plausible sancov maturity gap, not
      # necessarily a bug in this repo's own code — `nelli_shm.c`'s
      # IDENTICAL push/copy+generation-word mechanism is independently
      # proven correct on Windows via `tests/tfuzzwinshm.nim`'s
      # Nim-published cmp-log suite, and this exact C-level publish chain is
      # independently proven correct on POSIX via this same test). Asserting
      # `code == 0` FIRST, and echoing the captured process output (now
      # carrying the `NELLI_COV_DEBUG` trail) on any failure below, narrows
      # the next CI round's diagnosis to an exact line in the chain.
      if code != 0:
        echo "DIAGNOSTIC: instrumented target exited " & $code & ", output:\n" & output

      check code == 0                                       # 42 != 0xDEADBEEF

      let entries = shmReadCmpLog(shmName)
      if entries.len == 0:
        echo "DIAGNOSTIC: shmReadCmpLog('" & shmName & "') returned 0 entries after a code==0 run " &
             "of a trace-cmp-instrumented binary -- see this test's own comment for the suspects " &
             "(clang Windows trace-cmp instrumentation vs the nelli_shm.c publish path) and how " &
             "tests/tfuzzwinshm.nim already rules the shm mechanism itself out independently. " &
             "NELLI_COV_DEBUG trail (child's stdout+stderr):\n" & output
      check entries.len >= 1                                # at least the `x == 0xDEADBEEF` comparison
      var found = false
      for e in entries:
        if e.kind == clkInt and e.op == coUnknown and
           (e.lhsInt == 42'u64 or e.rhsInt == 42'u64) and
           (e.lhsInt == magicOperand or e.rhsInt == magicOperand):
          found = true
      check found
      removeDir(bin.parentDir)

  test "a second fresh-exec'd run over the SAME shm segment publishes its OWN operand, not a union with the prior run's":
    if not traceCmpSupported():
      skip()
    else:
      let bin = buildInstrumentedTraceCmp(@[cmpGateTarget], cmpCovRuntime)
      let shmName = "/nelli_g4c3b_" & $getCurrentProcessId()
      shmHoldCmpLog(shmName)   # see the sibling test above for why this must happen before the FIRST spawn

      putEnv("NELLI_CMP_SHM", shmName)
      putEnv("NELLI_COV_DEBUG", "1")   # see the sibling test above for what this surfaces
      let (output1, code1) = execCmdEx(quoteShell(bin) & " 7")
      if code1 != 0: echo "DIAGNOSTIC: run 1 exited " & $code1 & ", output:\n" & output1
      check code1 == 0
      let entries1 = shmReadCmpLog(shmName)
      # RFC-fuzzer-nextgen E4c C3 fix-up: same diagnostic as the sibling test
      # above (fuzzer-windows CI runs 33017017592, 33019262657 — see its comment).
      if entries1.len == 0:
        echo "DIAGNOSTIC: shmReadCmpLog('" & shmName & "') returned 0 entries after run 1 (code==0). " &
             "NELLI_COV_DEBUG trail:\n" & output1
      var found7a = false
      for e in entries1:
        if e.kind == clkInt and (e.lhsInt == 7'u64 or e.rhsInt == 7'u64): found7a = true
      check found7a

      let (output2, code2) = execCmdEx(quoteShell(bin) & " 99")
      delEnv("NELLI_CMP_SHM")
      delEnv("NELLI_COV_DEBUG")
      if code2 != 0: echo "DIAGNOSTIC: run 2 exited " & $code2 & ", output:\n" & output2
      check code2 == 0
      let entries2 = shmReadCmpLog(shmName)
      if entries2.len == 0:
        echo "DIAGNOSTIC: shmReadCmpLog('" & shmName & "') returned 0 entries after run 2 (code==0). " &
             "NELLI_COV_DEBUG trail:\n" & output2
      var found7b, found99 = false
      for e in entries2:
        if e.kind == clkInt and (e.lhsInt == 7'u64 or e.rhsInt == 7'u64): found7b = true
        if e.kind == clkInt and (e.lhsInt == 99'u64 or e.rhsInt == 99'u64): found99 = true
      check found99            # the SECOND (latest) run's own operand is present
      check not found7b        # the FIRST run's stale operand is NOT — a fresh publish
                                # replaces, it never unions with, the prior generation
      removeDir(bin.parentDir)

# --- externalTarget's OWN $NELLI_CMP_SHM wiring (RFC-fuzzer-nextgen R12 code review) ----
#
# The suite above proves the C-level publish/shm-read mechanism end to end,
# but by driving `spawnWorkerProcess`/`shmReadCmpLog` directly — standing in
# for an orchestrator role that, before R12, no production code actually
# played for the external tier: `externalTarget`/`fuzzBinary` never set
# `$NELLI_CMP_SHM` in the child's environment at all. This suite drives the
# REAL `externalTarget` proc (fuzz.nim) instead, proving its own
# `Observation.cmpLog` is populated from a real child's publish — the
# RFC's own named G4-C3 use case (cmp-guidance for an external target,
# exactly where in-process `{.covercmp.}` instrumentation cannot reach).

const stdinCmpGateTarget = """
#include <stdio.h>
int main(void) {
  unsigned int x = 0;
  if (fread(&x, sizeof(x), 1, stdin) != 1) return 1;
  if (x == 0xDEADBEEFu) return 3;   /* the comparison trace-cmp logs the operand pair for */
  return 0;
}
"""

proc encodeLE32(x: int): seq[byte] =
  let u = uint32(x)
  @[byte(u and 0xFF), byte((u shr 8) and 0xFF), byte((u shr 16) and 0xFF), byte((u shr 24) and 0xFF)]

suite "fuzz: externalTarget sets $NELLI_CMP_SHM itself (RFC-fuzzer-nextgen R12 code review)":
  test "externalTarget's own Observation.cmpLog carries the child's logged operand -- not just the raw shmReadCmpLog primitive":
    if not traceCmpSupported():
      skip()
    else:
      let bin = buildInstrumentedTraceCmp(@[stdinCmpGateTarget], cmpCovRuntime)
      let target = externalTarget[int](@[bin], stdinDelivery(), signalOracle[int](),
                                       encode = encodeLE32)
      let obs = target.run(42)   # a non-magic value: the comparison still fires, no crash
      check obs.verdict == vOk
      check obs.runResult.exitCode == 0

      check obs.cmpLog.isSome    # R12: populated by externalTarget itself, not left `none`
      let entries = obs.cmpLog.get
      if entries.len == 0:
        echo "DIAGNOSTIC: externalTarget's own Observation.cmpLog was Some(@[]) after a " &
             "code==0 run of a trace-cmp-instrumented binary -- see the sibling G4 C3 suite " &
             "above (which proves the shm mechanism itself independently) for how to narrow " &
             "this to the externalTarget wiring specifically."
      check entries.len >= 1
      var found = false
      for e in entries:
        if e.kind == clkInt and e.op == coUnknown and
           (e.lhsInt == 42'u64 or e.rhsInt == 42'u64) and
           (e.lhsInt == magicOperand or e.rhsInt == magicOperand):
          found = true
      check found
      removeDir(bin.parentDir)

  test "a target NOT built with trace-cmp reads back Some(@[]) -- absent, never stale, matching the coverage map's own D7 discipline":
    # `branchTarget` (top of this file) is not trace-cmp instrumented --
    # exercised here purely for its exit code, via stdinDelivery feeding it
    # bytes it never reads.
    if not available(cbGcc):
      skip()
    else:
      let bin = buildInstrumented(cbGcc, @[branchTarget], noopRuntime(cbGcc))
      let target = externalTarget[int](@[bin], stdinDelivery(), signalOracle[int](),
                                       encode = encodeLE32)
      let obs = target.run(42)
      check obs.cmpLog.isSome     # externalTarget ALWAYS reads back (absent vs stale, D7)
      check obs.cmpLog.get.len == 0
      removeDir(bin.parentDir)
