## RFC-fuzzer-nextgen E2b (C1): the double-buffered shm coverage transport in
## `nelli_cov.c` — push/copy publish, the atomic generation word, and the
## acquire-before-trust reader that never hands back a torn snapshot.
##
## POSIX-only (shm_open/mmap). Tests the shm MECHANISM directly (not through
## sancov instrumentation — that is `tfuzzcovdump.nim`'s job, and E2b C2
## extends it) via a tiny standalone C driver linked against `nelli_cov.c`
## that exercises the new `pt_shm_*` exported functions with synthetic byte
## buffers. A real writer and a real reader run as CONCURRENT OS processes
## (mirroring `tfuzzcovdump.nim`'s own real-subprocess-signal testing style,
## not the "fabricated sequence" fold-algebra style E3a uses elsewhere — this
## IS a genuine cross-process shm protocol, so real concurrency is the
## faithful test).

import std/[unittest, os, osproc, strutils, streams]
import fuzzsupport

when defined(posix):
  let shmRuntime = embedCSource("../src/nelli/nelli_shm.c")
    ## The shm mechanism now lives in its OWN file (RFC-fuzzer-nextgen E2b
    ## C3 split it out of nelli_cov.c so a Nim in-process worker can link it
    ## alone, without nelli_cov.c's process-wide signal-handler constructor —
    ## see nelli_shm.c's header). This driver only calls `pt_shm_*`
    ## functions, so it only needs this file, not nelli_cov.c. `let`, not
    ## `const` — chunked via `embedCSource` (MSVC's 16380-byte C2026 cap; a
    ## `const` would re-fold the chunks into one oversized literal).

  # Each publish fills its ENTIRE capacity with ONE repeated byte value (the
  # iteration number). A torn read shows up as two DIFFERENT byte values
  # inside a single read — a cheap, sensitive tear detector that needs no
  # checksum bookkeeping.
  const driverSrc = """
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>

extern int pt_shm_init(const char* name, uint32_t capacity);
extern void pt_shm_reset_buffer(void);
extern void pt_shm_publish_bytes(const uint8_t* data, uint32_t len);
extern int pt_shm_read(uint8_t* out, uint32_t outCap, uint32_t* outLen);

#define CAP 64

int main(int argc, char** argv) {
  const char* mode = argc > 1 ? argv[1] : "";
  const char* name = argc > 2 ? argv[2] : "/nelli_test_shm";

  if (strcmp(mode, "writer") == 0) {
    int n = argc > 3 ? atoi(argv[3]) : 5;
    if (pt_shm_init(name, CAP) != 0) { fprintf(stderr, "init failed\n"); return 1; }
    uint8_t buf[CAP];
    for (int k = 1; k <= n; k++) {
      pt_shm_reset_buffer();
      memset(buf, (uint8_t)k, CAP);
      pt_shm_publish_bytes(buf, CAP);
      printf("wrote %d\n", k);
      fflush(stdout);
      usleep(2000);
    }
    return 0;
  } else if (strcmp(mode, "reader") == 0) {
    int n = argc > 3 ? atoi(argv[3]) : 40;
    if (pt_shm_init(name, CAP) != 0) { fprintf(stderr, "init failed\n"); return 1; }
    uint8_t out[CAP];
    uint32_t outLen = 0;
    int badTear = 0;
    int lastSeen = -1;
    int sawAny = 0;
    for (int i = 0; i < n; i++) {
      int ok = pt_shm_read(out, CAP, &outLen);
      if (!ok) { badTear = 1; }
      else if (outLen > 0) {
        sawAny = 1;
        uint8_t first = out[0];
        for (uint32_t j = 1; j < outLen; j++) {
          if (out[j] != first) badTear = 1;
        }
        lastSeen = (int)first;
      }
      usleep(1000);
    }
    printf("tear=%d lastSeen=%d sawAny=%d\n", badTear, lastSeen, sawAny);
    return 0;
  } else if (strcmp(mode, "cleanup") == 0) {
    extern int shm_unlink(const char*);
    shm_unlink(name);
    return 0;
  } else if (strcmp(mode, "initpub") == 0) {
    // R23: publish once at an EXPLICIT capacity, then exit WITHOUT
    // unlinking -- models a prior campaign/spawn that leaked its shm
    // segment (crash, kill -9, or simply a caller that reused a name
    // instead of a fresh per-spawn one).
    uint32_t cap = argc > 3 ? (uint32_t)atoi(argv[3]) : 64;
    uint8_t fill = argc > 4 ? (uint8_t)atoi(argv[4]) : 7;
    if (pt_shm_init(name, cap) != 0) { fprintf(stderr, "init failed\n"); return 1; }
    uint8_t* buf = malloc(cap);
    memset(buf, fill, cap);
    pt_shm_reset_buffer();
    pt_shm_publish_bytes(buf, cap);
    printf("published cap=%u fill=%u\n", cap, fill);
    return 0;
  } else if (strcmp(mode, "readonce") == 0) {
    // R23: a SINGLE pt_shm_read call at an explicit (possibly stale-
    // mismatched) capacity -- models a fresh reader attaching to whatever
    // segment already exists at `name`, honestly not knowing whether it is
    // missing, freshly created, or a stale leftover from a completely
    // unrelated prior run.
    uint32_t cap = argc > 3 ? (uint32_t)atoi(argv[3]) : 64;
    if (pt_shm_init(name, cap) != 0) { fprintf(stderr, "init failed\n"); return 1; }
    uint8_t* out = malloc(cap);
    uint32_t outLen = 0;
    int ok = pt_shm_read(out, cap, &outLen);
    if (!ok) { printf("ok=0 outLen=0 first=-1\n"); return 0; }
    int first = (outLen > 0) ? (int)out[0] : -1;
    int uniform = 1;
    for (uint32_t i = 1; i < outLen; i++) if (out[i] != out[0]) uniform = 0;
    printf("ok=1 outLen=%u first=%d uniform=%d\n", outLen, first, uniform);
    return 0;
  } else if (strcmp(mode, "holdfresh") == 0) {
    // R19/R47 fix: models coverage.nim's shmHoldCoverage/shmHoldCmpLog
    // contract -- the caller claims to be the UNCONDITIONAL FIRST attacher
    // of `name`, and now has a way to VERIFY that claim instead of quietly
    // trusting whatever segment already happens to exist there.
    extern int pt_shm_freshly_created(void);
    uint32_t cap = argc > 3 ? (uint32_t)atoi(argv[3]) : 64;
    int rc = pt_shm_init(name, cap);
    if (rc != 0) { printf("rc=%d fresh=0\n", rc); return 1; }
    int fresh = pt_shm_freshly_created();
    printf("rc=0 fresh=%d\n", fresh);
    return fresh ? 0 : 1;
  }
  fprintf(stderr, "usage: driver writer|reader|cleanup|initpub|readonce|holdfresh <shmname> [n]\n");
  return 2;
}
"""

  var buildCtr = 0
  proc buildDriver(): string =
    inc buildCtr
    let dir = getTempDir() / ("ptshm_build_" & $buildCtr)
    removeDir(dir); createDir(dir)
    let drvC = dir / "driver.c"
    let rtC = dir / "nelli_shm.c"
    writeFile(drvC, driverSrc)
    writeFile(rtC, shmRuntime)
    let cc = findExe("gcc")
    doAssert cc.len > 0, "gcc not found"
    let bin = dir / "driver"
    let (o, c) = execCmdEx(cc & " " & quoteShell(drvC) & " " & quoteShell(rtC) &
                            " -o " & quoteShell(bin))
    doAssert c == 0, "driver build failed:\n" & o
    bin

  suite "fuzz: shm coverage transport (RFC-fuzzer-nextgen E2b C1)":
    test "a writer publishes to shm and a concurrent reader reads back with no torn reads":
      let bin = buildDriver()
      let shmName = "/nelli_t_c1_" & $getCurrentProcessId()
      # Reader started FIRST (with more iterations than the writer needs) so
      # it observes the "never published yet" (generation==0) state too.
      var reader = startProcess(bin, args = @["reader", shmName, "60"],
                                 options = {poUsePath, poStdErrToStdOut})
      var writer = startProcess(bin, args = @["writer", shmName, "10"],
                                 options = {poUsePath, poStdErrToStdOut})
      let writerOut = writer.outputStream.readAll()
      discard writer.waitForExit()
      writer.close()
      let readerOut = reader.outputStream.readAll()
      discard reader.waitForExit()
      reader.close()
      discard execCmdEx(bin & " cleanup " & shmName)

      check "wrote 10" in writerOut
      let line = readerOut.strip()
      check "tear=0" in line          # never observed a mixed-byte (torn) buffer
      check "sawAny=1" in line        # did observe at least one real publish
      check "lastSeen=10" in line     # eventually converges on the writer's final publish

    test "a reader started before any publish sees an empty (never-torn) read":
      let bin = buildDriver()
      let shmName = "/nelli_t_c1b_" & $getCurrentProcessId()
      let (readerOut, code) = execCmdEx(bin & " reader " & shmName & " 3")
      check code == 0
      check "tear=0" in readerOut
      check "sawAny=0" in readerOut
      discard execCmdEx(bin & " cleanup " & shmName)

    test "R47: attaching to a STALE segment (same capacity, left by a prior/unrelated run that never unlinked) still reads back that prior run's data via the raw pt_shm_read primitive, same as before":
      # `pt_shm_ch_init`'s header-reinit guard (`if (hdr->capacity == 0)`)
      # only zeroes `published`/`buf_len`/`generation` for the FIRST process
      # ever to attach a given segment -- a later attacher of an
      # already-initialized (nonzero-capacity) segment skips straight past
      # it, inheriting whatever `published`/`generation` the ORIGINAL
      # publisher left behind. This is exactly the hazard
      # `fuzzworker.nim`'s per-spawn-unique shm-name discipline (`nelli_
      # worker_cov_<pid>_<spawnCtr>`) exists to avoid -- this test proves
      # what would actually happen if that discipline were ever violated
      # (a name reused across spawns/campaigns): a "fresh" attacher gets a
      # `pt_shm_read` that reports `ok=1` with a plausible nonzero length,
      # not the empty/absent read a genuinely fresh segment gives (the
      # "reader started before any publish" test just above).
      #
      # This is UNCHANGED by the R19/R47 fix, and deliberately so: the raw
      # `pt_shm_init`/`pt_shm_read` primitive still has no way to know
      # whether ITS caller expects to be first -- that's a property of the
      # CALLER's contract, not the segment. `shmReadCoverage`/`shmProbe` (the
      # ordinary read path, coverage.nim) legitimately attach to a segment a
      # SIBLING process already created (the orchestrator's own
      # `shmHoldCoverage` pre-attach), so the primitive cannot refuse this
      # case outright without breaking that. The companion test just below
      # proves the actual fix: a caller that DOES claim to be first (the
      # `shmHoldCoverage`/`shmHoldCmpLog` contract, modeled here by
      # `holdfresh`) can now verify that claim and refuse loudly if it's
      # false -- see `pt_shm_freshly_created()`.
      let bin = buildDriver()
      let shmName = "/nelli_t_c1_stale_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)   # sweep any leftover from a prior run of this suite

      let (pubOut, pubCode) = execCmdEx(bin & " initpub " & shmName & " 64 9")
      check pubCode == 0
      check "published cap=64 fill=9" in pubOut

      # A logically unrelated "new" reader, attaching at the SAME capacity,
      # with no reset/publish of its own -- exactly what a caller would do
      # if it (wrongly) reused a name instead of minting a fresh one.
      let (readOut, readCode) = execCmdEx(bin & " readonce " & shmName & " 64")
      check readCode == 0
      # Silent staleness, not absence: `ok=1`, a full-capacity length, and
      # the PRIOR run's fill byte (9) -- indistinguishable from a genuine
      # same-run publish from the reader's point of view, IF the reader only
      # ever calls `pt_shm_read` and never asks `pt_shm_freshly_created()`.
      check "ok=1 outLen=64 first=9 uniform=1" in readOut
      discard execCmdEx(bin & " cleanup " & shmName)

    test "R47 FIX: a caller that requires being the first attacher (holdfresh, modeling shmHoldCoverage/shmHoldCmpLog) now detects that same stale segment loudly instead of silently accepting it":
      # The direct fix proof for the hazard the test above documents: the
      # SAME reused-name scenario, but through `pt_shm_freshly_created()` --
      # the primitive `shmHoldCoverage`/`shmHoldCmpLog` now consult (see
      # `nelli_shm.c`'s module doc, R47 section, and `coverage.nim`'s
      # `ShmProtocolError`) to verify the "I am the first attacher" claim
      # their contract requires, rather than trusting it blindly.
      let bin = buildDriver()
      let shmName = "/nelli_t_c1_stale_holdfresh_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)

      let (pubOut, pubCode) = execCmdEx(bin & " initpub " & shmName & " 64 9")
      check pubCode == 0
      check "published cap=64 fill=9" in pubOut

      # A genuinely fresh name: holdfresh must succeed and report fresh=1.
      let freshName = "/nelli_t_c1_genuinely_fresh_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & freshName)
      let (freshOut, freshCode) = execCmdEx(bin & " holdfresh " & freshName & " 64")
      check freshCode == 0
      check "rc=0 fresh=1" in freshOut
      discard execCmdEx(bin & " cleanup " & freshName)

      # The STALE name from above: holdfresh must now FAIL LOUDLY (nonzero
      # exit code) rather than silently reporting success over stale data.
      let (staleOut, staleCode) = execCmdEx(bin & " holdfresh " & shmName & " 64")
      check staleCode != 0
      check "rc=0 fresh=0" in staleOut
      discard execCmdEx(bin & " cleanup " & shmName)

    test "R19 FIX: attaching to a STALE segment at a DIFFERENT (mismatched) capacity than it was created with now fails loudly instead of reading a wrong-but-plausible-looking snapshot":
      # The companion hazard: not just a reused name, but a caller that
      # (e.g. across a build with a changed `coverageEdgeCount`, or simply
      # a bug) attaches at a DIFFERENT capacity than the segment's original
      # creator used. Before the fix, `ch->cap` (this attacher's own
      # buffer-offset math) and `ch->shdr->capacity` (the stale header
      # field) could diverge silently: the ORIGINAL publish landed at an
      # offset computed from the OLD capacity, but a later reader's `sbuf[]`
      # pointers were computed from ITS OWN (different) capacity -- a read
      # landing on a completely different byte range than where the prior
      # publisher actually wrote, with no crash and no refusal.
      #
      # FIX: `pt_shm_ch_init` now derives layout from `hdr->capacity` (the
      # segment's OWN, already-established value), not the caller's
      # argument -- a caller whose requested capacity disagrees with an
      # existing segment's gets `pt_shm_init` returning -2 (never a
      # mismatched layout, never silently proceeding). This applies to EVERY
      # caller of `pt_shm_init`/`pt_cmplog_init`, not just the `holdfresh`-
      # style contract the test above covers.
      let bin = buildDriver()
      let shmName = "/nelli_t_c1_wrongsize_" & $getCurrentProcessId()
      discard execCmdEx(bin & " cleanup " & shmName)

      let (pubOut, pubCode) = execCmdEx(bin & " initpub " & shmName & " 32 7")
      check pubCode == 0
      check "published cap=32 fill=7" in pubOut

      # Re-attach at a LARGER capacity (64, not 32): pt_shm_init itself now
      # refuses (rc=-2), so the driver's own `if (pt_shm_init(...) != 0)`
      # guard reports "init failed" and exits nonzero -- loud, not a wrong
      # read.
      let (readOut, readCode) = execCmdEx(bin & " readonce " & shmName & " 64")
      check readCode == 1
      check "init failed" in readOut
      # And explicitly NOT the old silent-wrong-data pin.
      check "ok=1" notin readOut

      # The companion direction: re-attach at a SMALLER capacity (16, not
      # 32) than the segment was created with -- also refused, same way.
      let (readOut2, readCode2) = execCmdEx(bin & " readonce " & shmName & " 16")
      check readCode2 == 1
      check "init failed" in readOut2
      discard execCmdEx(bin & " cleanup " & shmName)
else:
  suite "fuzz: shm coverage transport (RFC-fuzzer-nextgen E2b C1)":
    test "skipped on non-POSIX":
      skip()
