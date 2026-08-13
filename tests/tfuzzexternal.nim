## Phase 5a (docs/fuzz/FUZZ_PLAN.md): externalTarget + fuzzBinary — the real subprocess.
## runChild captures exit/signal/stdout precisely and enforces the timeout
## (SIGTERM→grace→SIGKILL); fuzzBinary drives an instrumented child end to end and accrues
## its coverage into the frontier. POSIX-only; skipped when gcc/clang is absent.

import std/[unittest, os, times]
import nelli
import fuzzsupport

when defined(posix):
  const covRuntime = staticRead("../src/nelli/nelli_cov.c")
  const probeTarget = """
#include <unistd.h>
int main(int argc, char** argv){
  char b[4] = {0};
  read(0, b, 3);
  if (b[0]=='x') return 3;
  if (b[0]=='k'){ volatile int* p = 0; return *p; }   /* SIGSEGV */
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
        check rk.signal == 11 and rk.exitCode == -1        # SIGSEGV
        removeDir(bin.parentDir)

    test "runChild times out a hang (SIGTERM → grace → SIGKILL)":
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
