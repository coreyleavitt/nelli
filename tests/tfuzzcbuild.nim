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
    # gcc is always present in the stock nimlang image, so the scaffold can
    # actually exercise something (not every backend skipped).
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

const cmpCovRuntime = staticRead("../src/nelli/nelli_cov.c")
const magicOperand = 0xDEADBEEF'u64

# The G4 C3 suite reads the cmp log back over the POSIX shm channel
# (`shmReadCmpLog` only exists under `when defined(posix)` in coverage.nim).
# E4b (Windows shm coverage: CreateFileMapping/MapViewOfFile) is the slice
# that brings this transport to Windows — when it lands, this gate must be
# WIDENED to include it, not left as a permanent skip. The Phase 1a build
# scaffold suite above stays live on every platform.
when not defined(posix):
  echo "SKIP (posix-only until E4b): trace-cmp external-tier operand log suite"
else:
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
      putEnv("NELLI_CMP_SHM", shmName)
      let (_, code) = execCmdEx(quoteShell(bin) & " 42")   # a non-magic value: the comparison still fires
      delEnv("NELLI_CMP_SHM")
      check code == 0                                       # 42 != 0xDEADBEEF

      let entries = shmReadCmpLog(shmName)
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

      putEnv("NELLI_CMP_SHM", shmName)
      let (_, code1) = execCmdEx(quoteShell(bin) & " 7")
      check code1 == 0
      let entries1 = shmReadCmpLog(shmName)
      var found7a = false
      for e in entries1:
        if e.kind == clkInt and (e.lhsInt == 7'u64 or e.rhsInt == 7'u64): found7a = true
      check found7a

      let (_, code2) = execCmdEx(quoteShell(bin) & " 99")
      delEnv("NELLI_CMP_SHM")
      check code2 == 0
      let entries2 = shmReadCmpLog(shmName)
      var found7b, found99 = false
      for e in entries2:
        if e.kind == clkInt and (e.lhsInt == 7'u64 or e.rhsInt == 7'u64): found7b = true
        if e.kind == clkInt and (e.lhsInt == 99'u64 or e.rhsInt == 99'u64): found99 = true
      check found99            # the SECOND (latest) run's own operand is present
      check not found7b        # the FIRST run's stale operand is NOT — a fresh publish
                                # replaces, it never unions with, the prior generation
      removeDir(bin.parentDir)
