## RFC-fuzzer-nextgen R19/R47 (code review, MEDIUM): `shmHoldCoverage`/
## `shmHoldCmpLog` (coverage.nim) are the two callers whose contract already
## requires being the unconditional FIRST attacher of a given shm name
## (called before the producer they'll read even exists — see their own doc
## comments). This suite proves that contract is now ENFORCED end-to-end
## through the real Nim API, not just at the raw C primitive
## `tests/tfuzzcovshm.nim` already pins:
##
## - R19: a name that already names a segment at a DIFFERENT capacity makes
##   `shmHoldCoverage`/`shmHoldCmpLog` raise `ShmProtocolError` instead of
##   silently attaching to a mismatched layout.
## - R47: a name that already names ANY preexisting segment (even at the
##   SAME capacity — the "stale, unrelated prior run" hazard) also raises,
##   since these two callers' whole point is to be first.
## - The positive case: a genuinely fresh name raises nothing.
##
## Uses the same embedded-C-driver technique `tests/tfuzzcovshm.nim` uses to
## pre-create a segment out-of-band (a separate OS process calling
## `pt_shm_init`/`pt_cmplog_init` directly, modeling "some earlier run left
## this behind") before the real Nim `shmHoldCoverage`/`shmHoldCmpLog` calls
## attach to that same name.
import std/[unittest, os, osproc]
import nelli
import fuzzsupport

when defined(posix):
  let shmRuntime = embedCSource("../src/nelli/nelli_shm.c")

  const makeDriverSrc = """
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

extern int pt_shm_init(const char* name, uint32_t capacity);
extern int pt_cmplog_init(const char* name, uint32_t capacity);

int main(int argc, char** argv) {
  const char* mode = argc > 1 ? argv[1] : "";
  const char* name = argc > 2 ? argv[2] : "";
  uint32_t cap = argc > 3 ? (uint32_t)atoi(argv[3]) : 1;

  if (strcmp(mode, "makecov") == 0) {
    int rc = pt_shm_init(name, cap);
    printf("rc=%d\n", rc);
    return rc == 0 ? 0 : 1;
  } else if (strcmp(mode, "makecmp") == 0) {
    int rc = pt_cmplog_init(name, cap);
    printf("rc=%d\n", rc);
    return rc == 0 ? 0 : 1;
  } else if (strcmp(mode, "cleanup") == 0) {
    extern int shm_unlink(const char*);
    shm_unlink(name);
    return 0;
  }
  fprintf(stderr, "usage: makedriver makecov|makecmp|cleanup <shmname> [capacity]\n");
  return 2;
}
"""

  var buildCtr = 0
  proc buildMakeDriver(): string =
    inc buildCtr
    let dir = getTempDir() / ("ptshmhold_build_" & $buildCtr)
    removeDir(dir); createDir(dir)
    let drvC = dir / "makedriver.c"
    let rtC = dir / "nelli_shm.c"
    writeFile(drvC, makeDriverSrc)
    writeFile(rtC, shmRuntime)
    let cc = findExe("gcc")
    doAssert cc.len > 0, "gcc not found"
    let bin = dir / "makedriver"
    let (o, c) = execCmdEx(cc & " " & quoteShell(drvC) & " " & quoteShell(rtC) &
                            " -o " & quoteShell(bin))
    doAssert c == 0, "makedriver build failed:\n" & o
    bin

  suite "RFC-fuzzer-nextgen R19/R47 -- shmHoldCoverage/shmHoldCmpLog enforce their first-attacher contract":
    test "shmHoldCoverage succeeds silently on a genuinely fresh name":
      let bin = buildMakeDriver()
      let shmName = "/nelli_t_hold_fresh_cov_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)
      shmHoldCoverage(shmName)   # must not raise
      discard execCmdEx(bin & " cleanup " & shmName)

    test "R47: shmHoldCoverage raises ShmProtocolError on a STALE (already-initialized, SAME-capacity) segment":
      let bin = buildMakeDriver()
      let shmName = "/nelli_t_hold_stale_cov_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)
      let (o, c) = execCmdEx(bin & " makecov " & shmName & " " & $coverageEdgeCount)
      check c == 0
      # A prior, unrelated process already initialized this segment at the
      # SAME capacity nelli's own worker would use -- exactly the R47
      # hazard: indistinguishable from a genuine same-run publish by
      # capacity alone.
      expect ShmProtocolError:
        shmHoldCoverage(shmName)
      discard execCmdEx(bin & " cleanup " & shmName)

    test "R19: shmHoldCoverage raises ShmProtocolError on a CAPACITY-MISMATCHED segment":
      let bin = buildMakeDriver()
      let shmName = "/nelli_t_hold_mismatch_cov_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)
      let wrongCap = coverageEdgeCount + 123   # deliberately not what shmHoldCoverage will request
      let (o, c) = execCmdEx(bin & " makecov " & shmName & " " & $wrongCap)
      check c == 0
      expect ShmProtocolError:
        shmHoldCoverage(shmName)
      discard execCmdEx(bin & " cleanup " & shmName)

    test "shmHoldCmpLog succeeds silently on a genuinely fresh name":
      let bin = buildMakeDriver()
      let shmName = "/nelli_t_hold_fresh_cmp_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)
      shmHoldCmpLog(shmName)   # must not raise
      discard execCmdEx(bin & " cleanup " & shmName)

    test "R47: shmHoldCmpLog raises ShmProtocolError on a STALE (already-initialized, SAME-capacity) segment":
      let bin = buildMakeDriver()
      let shmName = "/nelli_t_hold_stale_cmp_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)
      let (o, c) = execCmdEx(bin & " makecmp " & shmName & " " & $cmpLogShmCapacity)
      check c == 0
      expect ShmProtocolError:
        shmHoldCmpLog(shmName)
      discard execCmdEx(bin & " cleanup " & shmName)

    test "R19: shmHoldCmpLog raises ShmProtocolError on a CAPACITY-MISMATCHED segment":
      let bin = buildMakeDriver()
      let shmName = "/nelli_t_hold_mismatch_cmp_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)
      let wrongCap = cmpLogShmCapacity - 1000   # deliberately not what shmHoldCmpLog will request
      let (o, c) = execCmdEx(bin & " makecmp " & shmName & " " & $wrongCap)
      check c == 0
      expect ShmProtocolError:
        shmHoldCmpLog(shmName)
      discard execCmdEx(bin & " cleanup " & shmName)
else:
  suite "RFC-fuzzer-nextgen R19/R47 -- shmHoldCoverage/shmHoldCmpLog enforce their first-attacher contract":
    test "skipped on non-POSIX":
      skip()
