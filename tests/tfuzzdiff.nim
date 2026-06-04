## Phase 5b (docs/fuzz/FUZZ_PLAN.md): differentialTarget (D15) — fan one input across N
## child Targets and reduce their RunResults to one Verdict via `compare`. Still a Target[T],
## so the fuzz loop drives it unchanged. Two instrumented C children that disagree on a
## specific input prove divergence detection + coverage union. POSIX/compiler-gated.

import std/unittest
import proptest
import fuzzsupport

when defined(posix):
  const covRuntime = staticRead("../src/proptest/proptest_cov.c")
  # progVar prints BANG only when the first byte is 'Z'; progOK always prints OK.
  # So they diverge iff the input begins with 'Z'.
  const progVar = """
#include <unistd.h>
int main(void){ char b[4]={0}; read(0,b,3);
  if (b[0]=='Z') write(1,"BANG",4); else write(1,"OK",2); return 0; }
"""
  const progOK = """
#include <unistd.h>
int main(void){ char b[4]={0}; read(0,b,3); write(1,"OK",2); return 0; }
"""

  proc mismatchCompare(rs: seq[RunResult]; x: seq[byte]): Verdict =
    if rs[0].stdout != rs[1].stdout: vInteresting else: vOk

  proc twoChildren(): seq[Target[seq[byte]]] =
    let a = buildInstrumented(cbGcc, @[progVar], covRuntime)
    let b = buildInstrumented(cbGcc, @[progOK], covRuntime)
    let id = proc(x: seq[byte]): seq[byte] = x
    @[externalTarget[seq[byte]](@[a], stdinDelivery(), exitCodeOracle[seq[byte]]({}), ResourceLimits(), id),
      externalTarget[seq[byte]](@[b], stdinDelivery(), exitCodeOracle[seq[byte]]({}), ResourceLimits(), id)]

  suite "fuzz: differentialTarget (Phase 5b)":
    test "diverging output → vInteresting; matching output → vOk":
      if not available(cbGcc): skip()
      else:
        let dt = differentialTarget(twoChildren(), mismatchCompare)
        check dt.run(@[byte('Z'), byte('1')]).verdict == vInteresting   # BANG vs OK
        check dt.run(@[byte('a'), byte('1')]).verdict == vOk            # OK vs OK

    test "fan-out unions child coverage into one map":
      if not available(cbGcc): skip()
      else:
        let dt = differentialTarget(twoChildren(), mismatchCompare)
        let obs = dt.run(@[byte('a')])
        # joint map = both children's edge vectors concatenated → strictly wider than one child
        check obs.coverage.counters.len > 0

    test "fuzz drives differentialTarget and retains the divergence":
      if not available(cbGcc): skip()
      else:
        let dt = differentialTarget(twoChildren(), mismatchCompare)
        var frontier = newCoverageFrontier()
        let rep = fuzz(just(@[byte('Z'), byte('9')]), dt, frontier,
                       FuzzSettings(maxIterations: 8, seed: 1))
        check rep.iterations == 8
        check rep.coverageHits >= 1
        check rep.irCrashes.len >= 1                  # the divergent input was retained
