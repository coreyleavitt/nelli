/* nelli_cov.c — the vendorable SanitizerCoverage dump runtime.
 * See docs/fuzz/FUZZ_PLAN.md (D1, D5, D7) and docs/fuzz/INTERFACE.md (wire format).
 *
 * MUST be compiled WITHOUT -fsanitize-coverage (it must not instrument itself —
 * gcc would make __sanitizer_cov_trace_pc recurse into a stack overflow), and
 * linked against an instrumented target. Two backends, selected at build:
 *   default (clang): target built with -fsanitize-coverage=inline-8bit-counters;
 *                    this runtime captures the counter region(s) via the init
 *                    callback the target's module constructor calls.
 *   -DNELLI_COV_GCC: target built with -fsanitize-coverage=trace-pc; this
 *                    runtime keeps an AFL-style PC-hash edge bitmap.
 *
 * On normal exit OR a fatal signal it dumps the map to $NELLI_COV_FILE:
 *   "PCOV" | u32 version | u32 targetId | u32 len | <len bytes> | u32 checksum
 * (little-endian), written to "<path>.tmp" then rename()d (atomic; no torn read).
 * The dump path uses only async-signal-safe calls so it is valid from a handler.
 * A target killed by SIGKILL or _exit()ing before the handlers run leaves NO file
 * — the reader treats absent as no-coverage, never stale.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>     /* rename */
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>

#define NELLI_COV_VERSION 1u
#ifndef NELLI_COV_TARGETID
#define NELLI_COV_TARGETID 0u
#endif

#ifdef NELLI_COV_GCC
/* ---- gcc trace-pc: AFL-style hashed-edge bitmap ---- */
  #ifndef NELLI_COV_MAPBITS
  #define NELLI_COV_MAPBITS 16
  #endif
  #define PT_MAPLEN (1u << NELLI_COV_MAPBITS)
  static uint8_t pt_map[PT_MAPLEN];
  static uintptr_t pt_prev;
  void __sanitizer_cov_trace_pc(void) {
    uintptr_t pc = (uintptr_t)__builtin_return_address(0);
    uintptr_t cur = (pc >> 4) ^ (pc >> 12);          /* fold the return address */
    uint32_t idx = (uint32_t)((cur ^ pt_prev) & (PT_MAPLEN - 1));
    if (pt_map[idx] < 255) pt_map[idx]++;
    pt_prev = cur >> 1;                               /* AFL prev-loc shift */
  }
#else
/* ---- clang inline-8bit-counters: accumulate counter region(s) (multi-TU) ---- */
  #define PT_MAXREGIONS 256
  static uint8_t* pt_rstart[PT_MAXREGIONS];
  static uint8_t* pt_rstop[PT_MAXREGIONS];
  static int pt_nregions;
  void __sanitizer_cov_8bit_counters_init(uint8_t* start, uint8_t* stop) {
    if (pt_nregions < PT_MAXREGIONS) {                /* one call per instrumented module */
      pt_rstart[pt_nregions] = start;
      pt_rstop[pt_nregions] = stop;
      pt_nregions++;
    }
  }
#endif

static void pt_put32(uint8_t* p, uint32_t v) { p[0]=v; p[1]=v>>8; p[2]=v>>16; p[3]=v>>24; }

static volatile sig_atomic_t pt_dumped = 0;

static void pt_dump(void) {
  if (pt_dumped) return;                              /* dump exactly once */
  pt_dumped = 1;
  const char* path = getenv("NELLI_COV_FILE");
  if (!path) return;
  char tmp[4096];
  size_t n = strlen(path);
  if (n + 5 >= sizeof(tmp)) return;
  memcpy(tmp, path, n); memcpy(tmp + n, ".tmp", 5);
  int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  if (fd < 0) return;

  uint32_t len = 0, sum = 0;
#ifdef NELLI_COV_GCC
  len = PT_MAPLEN;
#else
  for (int r = 0; r < pt_nregions; r++) len += (uint32_t)(pt_rstop[r] - pt_rstart[r]);
#endif
  uint8_t hdr[16];
  memcpy(hdr, "PCOV", 4);
  pt_put32(hdr + 4, NELLI_COV_VERSION);
  pt_put32(hdr + 8, (uint32_t)NELLI_COV_TARGETID);
  pt_put32(hdr + 12, len);
  if (write(fd, hdr, 16) != 16) { close(fd); return; }

#ifdef NELLI_COV_GCC
  for (uint32_t i = 0; i < len; i++) sum += pt_map[i];
  (void)write(fd, pt_map, len);
#else
  for (int r = 0; r < pt_nregions; r++) {
    uint8_t* s = pt_rstart[r];
    uint32_t rl = (uint32_t)(pt_rstop[r] - s);
    for (uint32_t i = 0; i < rl; i++) sum += s[i];
    (void)write(fd, s, rl);
  }
#endif
  uint8_t cs[4]; pt_put32(cs, sum);
  (void)write(fd, cs, 4);
  close(fd);
  (void)rename(tmp, path);                            /* atomic publish */
}

static void pt_sig(int sig) { pt_dump(); signal(sig, SIG_DFL); raise(sig); }

__attribute__((constructor))
static void pt_init(void) {
  atexit(pt_dump);
  int sigs[] = { SIGTERM, SIGINT, SIGSEGV, SIGABRT, SIGBUS, SIGFPE, SIGILL };
  for (unsigned i = 0; i < sizeof(sigs) / sizeof(sigs[0]); i++) signal(sigs[i], pt_sig);
}
