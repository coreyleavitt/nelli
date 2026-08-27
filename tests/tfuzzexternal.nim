## Phase 5a (docs/fuzz/FUZZ_PLAN.md): externalTarget + fuzzBinary — the real subprocess.
## runChild captures exit/signal/stdout precisely and enforces the timeout
## (SIGTERM→grace→SIGKILL on POSIX; poll-then-kill on Windows); fuzzBinary drives an
## instrumented child end to end and accrues its coverage into the frontier.
##
## RFC-fuzzer-nextgen E4c C3: widened off `when defined(posix)` — `runChild`/
## `externalTarget`/`fuzzBinary` now compile `when defined(posix) or defined(windows)`
## (fuzz.nim), and `probeTarget`'s `<unistd.h>` `read(0, ...)` compiles+runs fine
## under mingw too (it ships a POSIX-compat `<unistd.h>`, unlike the false assumption
## an earlier slice's CI failure history corrected for `nelli_cov.c`'s OWN surface —
## see that file's module doc). Only the CRASH-DECODE assertions are genuinely
## platform-shaped: POSIX reports a null-pointer dereference as `SIGSEGV`
## (`signal == 11`, `exitCode == -1`); Windows has no signal taxonomy at all — the
## SAME access violation surfaces only via `exitCode`, carrying the NTSTATUS
## `STATUS_ACCESS_VIOLATION` (`0xC0000005`) that `nelli_cov.c`'s Windows
## `SetUnhandledExceptionFilter` arm lets propagate as the process's own exit status
## (see that file's module doc, and `fuzzworker.nim`'s `observationForDeath`'s
## identical Windows NTSTATUS decode for the persistent-worker tier). Skipped when
## no coverage backend is available (`fuzzsupport.available`, itself no longer
## posix-hardcoded either — see that module's own doc comment).
import std/[unittest, os, times]
import nelli
import fuzzsupport

let covRuntime = embedCSource("../src/nelli/nelli_cov.c")
  ## `let`, not `const` — chunked via `embedCSource` (MSVC's 16380-byte
  ## C2026 single-string-literal cap; `nelli_cov.c` is 26100 bytes; a
  ## `const` would re-fold the chunks back into one oversized literal).
const probeTarget = """
#include <unistd.h>
int main(int argc, char** argv){
  char b[4] = {0};
  read(0, b, 3);
  if (b[0]=='x') return 3;
  if (b[0]=='k'){ volatile int* p = 0; return *p; }   /* SIGSEGV / access violation */
  return 0;
}
"""

proc byteStrat(): Strategy[seq[byte]] =
  lists(integers(0, 255), 1, 4).map(proc(xs: seq[int]): seq[byte] =
    result = newSeq[byte](xs.len)
    for i, v in xs: result[i] = byte(v))

suite "fuzz: externalTarget + fuzzBinary (Phase 5a)":
  test "runChild captures exit code, signal, and stdout":
    if not available(cbGcc): skip()
    else:
      let bin = buildInstrumented(cbGcc, @[probeTarget], covRuntime)
      let r0 = runChild(@[bin], @[], @[byte('a')], ResourceLimits())
      check r0.exitCode == 0 and r0.signal == 0
      let r3 = runChild(@[bin], @[], @[byte('x')], ResourceLimits())
      check r3.exitCode == 3
      let rk = runChild(@[bin], @[], @[byte('k')], ResourceLimits())
      when defined(windows):
        # No signal taxonomy on Windows — the null-pointer dereference
        # surfaces only via `exitCode`, carrying the raw NTSTATUS
        # `STATUS_ACCESS_VIOLATION` (`0xC0000005`) as its (signed, so
        # negative when viewed as `int`) exit status.
        check rk.signal == 0
        check cast[uint32](int32(rk.exitCode)) == 0xC0000005'u32
      else:
        check rk.signal == 11 and rk.exitCode == -1        # SIGSEGV
      removeDir(bin.parentDir)

  test "runChild times out a hang (SIGTERM → grace → SIGKILL on POSIX; poll-then-kill on Windows)":
    if not available(cbGcc): skip()
    else:
      let bin = buildInstrumented(cbGcc, @["int main(void){ while(1); }\n"], covRuntime)
      let r = runChild(@[bin], @[], @[], ResourceLimits(perRunTimeout: initDuration(milliseconds = 300)))
      check r.timedOut
      removeDir(bin.parentDir)

  test "fuzzBinary drives the external child and accrues coverage":
    if not available(cbGcc): skip()
    else:
      let bin = buildInstrumented(cbGcc, @[probeTarget], covRuntime)
      let rep = fuzzBinary(byteStrat(), @[bin],
                           FuzzSettings(maxIterations: 25, seed: 1),
                           ResourceLimits(perRunTimeout: initDuration(seconds = 5)))
      check rep.iterations == 25
      check rep.coverageHits >= 1                        # child coverage reached the frontier
      removeDir(bin.parentDir)
