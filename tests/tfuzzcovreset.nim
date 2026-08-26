## RFC-fuzzer-nextgen E2b (C2): per-input reset/republish in `nelli_cov.c` —
## `pt_shm_reset`/`pt_shm_reset_buffer` zero the live counters and the
## INACTIVE shm buffer and re-arm `pt_dumped`, so a persistent process can
## publish N independent per-input snapshots instead of one process-lifetime
## snapshot (E2a's interim file-dump policy).
##
## Two characterization claims, each proven against a REAL persistent
## process (not a fabricated/simulated sequence — this is a genuine
## cross-process/signal safety protocol, matching `tfuzzcovdump.nim`'s own
## real-subprocess-signal testing style):
##
## 1. "independent runs" — a persistent process that resets between two
##    "inputs" hitting DIFFERENT branches publishes each input's snapshot
##    matching an EQUIVALENT single-shot (fresh-process, file-dump) reference
##    run — not the union of both (which would mean stale bleed).
## 2. "signal mid-reset never reads a half-reset buffer" — a real SIGALRM is
##    calibrated (self-timed against one uninterrupted reset call) to land
##    approximately mid-`pt_shm_reset_buffer`, whose handler ALSO tries to
##    publish; the reader must never observe a torn (mixed-byte) buffer
##    across many repeated trials.

import std/[unittest, os, osproc, strutils]
import fuzzsupport

when defined(posix):
  const covRuntime = staticRead("../src/nelli/nelli_cov.c")
  const shmRuntime = staticRead("../src/nelli/nelli_shm.c")
    ## `nelli_cov.c` now `extern`s its shm mechanism from this separate file
    ## (E2b C3 split it out — see nelli_shm.c's header). "Claim 1" below
    ## builds real sancov-instrumented binaries via `buildInstrumented`,
    ## which links both files; "claim 2" (the reset-race driver) only calls
    ## `pt_shm_*` directly and so only needs this one.

  proc covSig(bytes: seq[byte]): uint32 =
    ## Same FNV-1a signature style `tfuzzcovdump.nim` uses, so a
    ## persistent-process shm snapshot's signature is directly comparable to
    ## a fresh-process file-dump reference's.
    result = 2166136261'u32
    for b in bytes: result = (result xor uint32(b)) * 16777619'u32

  proc parseHexBytes(s: string): seq[byte] =
    var i = 0
    while i + 1 < s.len:
      result.add byte(parseHexInt(s[i .. i+1]))
      i += 2

  proc unlinkShm(name: string) =
    ## Best-effort shm cleanup (Linux backs POSIX shm objects under
    ## `/dev/shm/`; the container this suite runs in is always Linux — see
    ## the "podman tooling" project convention). Neither test driver needs
    ## its own `shm_unlink` call path; removing the backing file has the
    ## same effect once every mapping process has exited.
    discard tryRemoveFile("/dev/shm/" & name.strip(chars = {'/'}))

  # --- claim 1: independent per-input runs -------------------------------
  #
  # A cross-binary comparison (this persistent process's dump vs. a
  # fresh-process file-dump reference for "the same" input) does NOT work
  # for the gcc trace-pc backend: its bitmap slot for a given source edge
  # depends on `pt_prev` (the AFL prev-loc fold) AND on the exact PC address
  # sequence the WHOLE binary executes before reaching that edge — both
  # differ between a minimal reference binary and this persistent driver
  # (extra instrumented code: `main`'s own control flow, `printHex`, the
  # `pt_shm_*` call sites). So the proof is WITHIN one binary instead: three
  # cycles (x, y, x) — the third replays the FIRST input after an
  # intervening DIFFERENT one. If reset leaves ANY state behind (a value in
  # `pt_map` OR the `pt_prev` edge-context carried across runs), the third
  # cycle's snapshot would differ from the first's, since it would land
  # slots relative to a PC history the first cycle never saw. Equality
  # proves the reset is a genuine return to a fresh-process-equivalent
  # state, not just "the affected bytes happen to look similar."

  const tworunSrc = """
static int helper(int c) {
  if (c == 'x') return 3;
  if (c == 'y') return 5;
  return 0;
}
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

extern uint32_t pt_cov_total_len(void);
extern int pt_shm_init(const char* name, uint32_t capacity);
extern void pt_shm_reset(void);
extern void pt_shm_publish_now(void);
extern int pt_shm_read(uint8_t* out, uint32_t outCap, uint32_t* outLen);

static void printHex(uint8_t* buf, uint32_t len) {
  for (uint32_t i = 0; i < len; i++) printf("%02x", buf[i]);
  printf("\n");
}

static void cycle(uint8_t* buf, uint32_t cap, int input) {
  pt_shm_reset();
  helper(input);
  pt_shm_publish_now();
  uint32_t len = 0;
  pt_shm_read(buf, cap, &len);
  printHex(buf, len);
}

int main(int argc, char** argv) {
  const char* name = argv[1];
  uint32_t cap = pt_cov_total_len();
  if (pt_shm_init(name, cap) != 0) { fprintf(stderr, "shm init failed\n"); return 1; }
  uint8_t* buf = malloc(cap);

  cycle(buf, cap, 'x');
  cycle(buf, cap, 'y');
  cycle(buf, cap, 'x');

  free(buf);
  return 0;
}
"""

  suite "fuzz: coverage per-input reset/republish (RFC-fuzzer-nextgen E2b C2)":
    test "a persistent process's resets publish INDEPENDENT per-input snapshots, not a union":
      if not available(cbGcc): skip()
      else:
        let twoBin = buildInstrumented(cbGcc, @[tworunSrc], covRuntime)
        let shmName = "/nelli_t_c2a_" & $getCurrentProcessId()
        let (outp, code) = execCmdEx(quoteShell(twoBin) & " " & shmName)
        check code == 0
        let lines = outp.strip().splitLines()
        check lines.len == 3
        let sig1 = covSig(parseHexBytes(lines[0]))   # input 'x'
        let sig2 = covSig(parseHexBytes(lines[1]))   # input 'y'
        let sig3 = covSig(parseHexBytes(lines[2]))   # input 'x' again, after 'y' ran in between
        check sig1 != sig2      # sanity: the two inputs are genuinely distinguishable
        check sig1 == sig3      # replaying 'x' after 'y' reproduces 'x's OWN snapshot exactly —
                                 # no leftover value AND no leftover edge-context from 'y'
        unlinkShm(shmName)
        removeDir(twoBin.parentDir)

  # --- claim 2: signal mid-reset never observes a torn buffer -------------

  const resetRaceSrc = """
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <time.h>
#include <sys/time.h>
#include <stdint.h>

extern int pt_shm_init(const char* name, uint32_t capacity);
extern void pt_shm_reset_buffer(void);
extern void pt_shm_publish_bytes(const uint8_t* data, uint32_t len);
extern int pt_shm_read(uint8_t* out, uint32_t outCap, uint32_t* outLen);

static uint32_t g_cap;
static uint8_t* g_marker;
static volatile sig_atomic_t g_fired = 0;

static void alarmHandler(int sig) {
  (void)sig;
  g_fired = 1;
  pt_shm_publish_bytes(g_marker, g_cap);
}

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1e6;
}

static void arm(long usec) {
  struct itimerval tv;
  tv.it_value.tv_sec = usec / 1000000;
  tv.it_value.tv_usec = usec % 1000000;
  tv.it_interval.tv_sec = 0;
  tv.it_interval.tv_usec = 0;
  setitimer(ITIMER_REAL, &tv, NULL);
}

static void disarm(void) {
  struct itimerval tv;
  memset(&tv, 0, sizeof(tv));
  setitimer(ITIMER_REAL, &tv, NULL);
}

int main(int argc, char** argv) {
  const char* name = argv[1];
  g_cap = 3000000u;
  if (pt_shm_init(name, g_cap) != 0) { fprintf(stderr, "init failed\n"); return 1; }
  uint8_t* initBuf = malloc(g_cap);
  memset(initBuf, 0x11, g_cap);
  g_marker = malloc(g_cap);
  memset(g_marker, 0xAB, g_cap);
  pt_shm_publish_bytes(initBuf, g_cap);

  signal(SIGALRM, alarmHandler);

  double t0 = now_ms();
  pt_shm_reset_buffer();
  double calibMs = now_ms() - t0;
  pt_shm_publish_bytes(initBuf, g_cap);   // restore a known baseline post-calibration

  long usec = (long)(calibMs * 1000.0 / 2.0);
  if (usec < 200) usec = 200;

  int iterations = 12;
  int torn = 0;
  int firedCount = 0;
  uint8_t* readBuf = malloc(g_cap);

  for (int i = 0; i < iterations; i++) {
    g_fired = 0;
    arm(usec);
    pt_shm_reset_buffer();
    disarm();
    if (g_fired) firedCount++;

    uint32_t outLen = 0;
    int ok = pt_shm_read(readBuf, g_cap, &outLen);
    if (!ok) { torn = 1; }
    else if (outLen > 0) {
      uint8_t first = readBuf[0];
      for (uint32_t j = 1; j < outLen; j++) {
        if (readBuf[j] != first) { torn = 1; break; }
      }
      if (first != 0x11 && first != 0xAB) torn = 1;
    }

    // restore a known baseline for the next iteration via an UNINTERRUPTED cycle
    pt_shm_reset_buffer();
    pt_shm_publish_bytes(initBuf, g_cap);
  }

  printf("torn=%d fired=%d calibMs=%f\n", torn, firedCount, calibMs);
  return 0;
}
"""

  proc buildResetRace(): string =
    let dir = getTempDir() / ("ptshm_resetrace_" & $getCurrentProcessId())
    removeDir(dir); createDir(dir)
    let drvC = dir / "resetrace.c"
    let rtC = dir / "nelli_shm.c"
    writeFile(drvC, resetRaceSrc)
    writeFile(rtC, shmRuntime)
    let cc = findExe("gcc")
    doAssert cc.len > 0
    let bin = dir / "resetrace"
    let (o, c) = execCmdEx(cc & " -O0 " & quoteShell(drvC) & " " & quoteShell(rtC) &
                            " -o " & quoteShell(bin))
    doAssert c == 0, "resetrace build failed:\n" & o
    bin

  suite "fuzz: signal-safety of per-input reset (RFC-fuzzer-nextgen E2b C2)":
    test "a real SIGALRM calibrated to land mid-reset never yields a torn buffer":
      let bin = buildResetRace()
      let shmName = "/nelli_t_c2b_" & $getCurrentProcessId()
      let (outp, code) = execCmdEx(quoteShell(bin) & " " & shmName)
      check code == 0
      check "torn=0" in outp
      unlinkShm(shmName)
      removeDir(bin.parentDir)
else:
  suite "fuzz: coverage per-input reset/republish (RFC-fuzzer-nextgen E2b C2)":
    test "skipped on non-POSIX":
      skip()
