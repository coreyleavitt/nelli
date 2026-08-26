## RFC-fuzzer-nextgen E5: the external tier onto the `Worker[T]`/`Orchestrator[T]`
## seams. `newExternalWorker[T]` wraps the same `(argv, delivery, oracle, limits,
## encode)` an `externalTarget` takes, but replays a `ChoiceSeq` (the Worker's
## currency, Appendix C) through a `Strategy[T]` to a value first — mirroring
## `newInProcessWorker`'s ChoiceSeq->value bridge — then runs the child exactly
## like `externalTarget.run` does. POSIX-only (mirrors `tfuzzexternal.nim`;
## skipped when gcc/clang is absent).
##
## Windows persistent-mode external worker (N-inputs-per-worker via a
## libFuzzer-driver-style loop in the target) is explicitly OUT OF SCOPE here —
## see the `newExternalWorker` doc comment in `src/nelli/fuzz.nim` (RFC E5's
## stated throughput-asymmetry caveat, not an equivalence).

import std/[unittest, os, times]
import nelli
import nelli/[datasource, rng]
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

  proc drawUntil(seedBase: uint64; strat: Strategy[seq[byte]];
                 pred: proc(v: seq[byte]): bool): tuple[val: seq[byte], choices: ChoiceSeq] =
    ## Draw a value matching `pred` through the REAL strategy (never
    ## hand-build a `ChoiceNode` — replay must stay strategy-valid), mirroring
    ## `tfuzzworkerprocess.nim`'s helper of the same name.
    for attempt in 0'u64 ..< 10_000'u64:
      var ds = newDataSource(initSplitMix64(seedBase + attempt))
      let v = strat.generate(ds)
      if pred(v): return (v, ds.recorded)
    doAssert false, "could not draw a value matching the predicate"

  suite "fuzz: external tier onto the Worker/Orchestrator seams (RFC-fuzzer-nextgen E5)":
    test "newExternalWorker.submit yields the same Observation as externalTarget.run for the same input":
      if not available(cbGcc): skip()
      else:
        let bin = buildInstrumented(cbGcc, @[probeTarget], covRuntime)
        let strat = byteStrat()
        let limits = ResourceLimits(perRunTimeout: initDuration(seconds = 5))
        let encode = proc(x: seq[byte]): seq[byte] = x

        let target = externalTarget[seq[byte]](@[bin], stdinDelivery(),
                                                signalOracle[seq[byte]](), limits, encode)
        let worker = newExternalWorker[seq[byte]](strat, @[bin], stdinDelivery(),
                                                   signalOracle[seq[byte]](), limits, encode)

        # A non-crashing input.
        let (valOk, choicesOk) = drawUntil(1'u64, strat,
          proc(v: seq[byte]): bool = v.len > 0 and v[0] != byte('x') and v[0] != byte('k'))
        let refOk = target.run(valOk)
        let obsOk = worker.submit(choicesOk)
        check obsOk.verdict == refOk.verdict
        check obsOk.coverage.counters == refOk.coverage.counters
        check obsOk.crash.isNone and refOk.crash.isNone

        # An exit-code finding.
        let (valExit, choicesExit) = drawUntil(2'u64, strat,
          proc(v: seq[byte]): bool = v.len > 0 and v[0] == byte('x'))
        let refExit = target.run(valExit)
        let obsExit = worker.submit(choicesExit)
        check obsExit.verdict == refExit.verdict
        check obsExit.crash.isSome and refExit.crash.isSome
        check obsExit.crash.get.kind == refExit.crash.get.kind
        check obsExit.crash.get.exitCode == refExit.crash.get.exitCode

        # A SIGSEGV finding — signal takes precedence in the typed CrashInfo.
        let (valCrash, choicesCrash) = drawUntil(3'u64, strat,
          proc(v: seq[byte]): bool = v.len > 0 and v[0] == byte('k'))
        let refCrash = target.run(valCrash)
        let obsCrash = worker.submit(choicesCrash)
        check obsCrash.verdict == refCrash.verdict
        check obsCrash.crash.isSome and refCrash.crash.isSome
        check obsCrash.crash.get.kind == refCrash.crash.get.kind
        check obsCrash.crash.get.signal == refCrash.crash.get.signal

        removeDir(bin.parentDir)
