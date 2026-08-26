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

when defined(posix):
  const covRuntime = staticRead("../src/nelli/nelli_cov.c")

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
  }
  fprintf(stderr, "usage: driver writer|reader|cleanup <shmname> [n]\n");
  return 2;
}
"""

  var buildCtr = 0
  proc buildDriver(): string =
    inc buildCtr
    let dir = getTempDir() / ("ptshm_build_" & $buildCtr)
    removeDir(dir); createDir(dir)
    let drvC = dir / "driver.c"
    let rtC = dir / "nelli_cov.c"
    writeFile(drvC, driverSrc)
    writeFile(rtC, covRuntime)
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
else:
  suite "fuzz: shm coverage transport (RFC-fuzzer-nextgen E2b C1)":
    test "skipped on non-POSIX":
      skip()
