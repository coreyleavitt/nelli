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
 *
 * RFC-fuzzer-nextgen E2b: when $NELLI_COV_SHM (or an explicit pt_shm_init
 * call) is present, the SAME atexit/signal dispatch (pt_cov_publish, below)
 * publishes to the double-buffered shm transport instead of the file — see
 * nelli_shm.c for that mechanism (a SEPARATE file, deliberately: it has no
 * constructor and installs no signal handlers of its own, so a Nim in-process
 * worker can link ONLY nelli_shm.c without inheriting THIS file's process-wide
 * signal hijacking, which a real external-target integration linking BOTH
 * files still gets). A real external sancov target must link BOTH this file
 * AND nelli_shm.c together; a Nim persistent worker (E2b C3) links ONLY
 * nelli_shm.c and calls its pt_shm_* functions directly with its own
 * {.cover.} bitmap bytes — this file is never part of that build.
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
static void pt_put64(uint8_t* p, uint64_t v) {
  for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> (8 * i));
}

/* `pt_dumped` gates "at most one publish per run" — defined in nelli_shm.c
 * (shared with its shm gate) and re-armed there, between inputs, by
 * `pt_shm_reset_buffer()`. A single-shot external target never calls
 * reset, so this reads as "once per process" for it, unchanged from before
 * E2b. */
extern volatile sig_atomic_t pt_dumped;

/* ---- E2b shm primitives this file calls into (nelli_shm.c) ---------------- */
extern int pt_shm_init(const char* name, uint32_t capacity);
extern int pt_shm_begin(uint8_t** outPtr, uint32_t* outCapacity);
extern void pt_shm_commit(uint32_t totalLen);
extern void pt_shm_reset_buffer(void);
extern uint32_t pt_shm_capacity_get(void);

/* ---- G4 C2 cmp-log's OWN shm channel (nelli_shm.c) ------------------------ */
extern int pt_cmplog_init(const char* name, uint32_t capacity);
extern void pt_cmplog_publish_bytes(const uint8_t* data, uint32_t len);
extern void pt_cmplog_reset_buffer(void);

/* ---- trace-cmp: comparison-operand logging (RFC-fuzzer-nextgen G4 C3) -----
 *
 * clang's `-fsanitize-coverage=trace-cmp` instruments every integer
 * comparison with a call to one of the eight callbacks below, passing both
 * operands widened to the matching unsigned width. UNLIKE the Nim-tier
 * `{.covercmp.}` hook (`coverage.nim`), the sanitizer-coverage ABI does not
 * convey WHICH operator (`==`, `<`, ...) triggered the call — every entry
 * from this path is tagged `coUnknown` (`coverage.nim`'s `CmpOp`), the
 * honest external-tier limitation this mechanism has always had (upstream
 * RedQueen/AFL++ implementations treat trace-cmp the same way: the operand
 * PAIR is the I2S signal, the missing operator is not).
 *
 * Entries accumulate in a fixed local buffer (bounded — writes past the cap
 * are dropped, never overflowed; `PT_CMP_MAXBYTES` matches `coverage.nim`'s
 * `cmpLogShmCapacity` exactly, so what reaches shm is always whole records,
 * never a cap-truncated partial one) in the SAME wire format
 * `coverage.nim`'s `parseCmpLog` decodes (`kind u8 | op u8 | ...` — see that
 * proc's doc for the full per-kind layout), published over the cmp log's
 * OWN independent shm channel (`pt_cmplog_*`) at the SAME
 * atexit/signal dispatch point coverage already uses (`pt_cov_publish`,
 * below) — gated on `$NELLI_CMP_SHM` (checked once, cached), so a target
 * built WITH trace-cmp but run WITHOUT the env var pays only that one
 * cached check per comparison, never touches shm at all.
 */
#define PT_CMP_MAXBYTES 65536u
#define PT_CMP_OP_UNKNOWN 6u   /* coverage.nim's CmpOp.coUnknown ordinal (appended last, so 6) */

static uint8_t pt_cmp_buf[PT_CMP_MAXBYTES];
static uint32_t pt_cmp_len;
static int pt_cmp_enabled = -1;        /* -1 = unchecked, 0 = off, 1 = on */
static char pt_cmp_shm_name[256];
static int pt_cmp_shm_ready;

static int pt_cmp_check_enabled(void) {
  if (pt_cmp_enabled < 0) {
    const char* n = getenv("NELLI_CMP_SHM");
    if (n && n[0] && strlen(n) < sizeof(pt_cmp_shm_name)) {
      memcpy(pt_cmp_shm_name, n, strlen(n) + 1);
      pt_cmp_enabled = 1;
    } else {
      pt_cmp_enabled = 0;
    }
  }
  return pt_cmp_enabled;
}

static void pt_cmp_log_int(uint8_t width, uint64_t lhs, uint64_t rhs) {
  if (!pt_cmp_check_enabled()) return;
  const uint32_t need = 1 + 1 + 1 + 8 + 8;   /* kind + op + width + lhs + rhs */
  if (pt_cmp_len + need > PT_CMP_MAXBYTES) return;   /* drop past cap — never overflow */
  pt_cmp_buf[pt_cmp_len++] = 0;                       /* kind: clkInt */
  pt_cmp_buf[pt_cmp_len++] = (uint8_t)PT_CMP_OP_UNKNOWN;
  pt_cmp_buf[pt_cmp_len++] = width;
  pt_put64(pt_cmp_buf + pt_cmp_len, lhs); pt_cmp_len += 8;
  pt_put64(pt_cmp_buf + pt_cmp_len, rhs); pt_cmp_len += 8;
}

void __sanitizer_cov_trace_cmp1(uint8_t a, uint8_t b)         { pt_cmp_log_int(1, a, b); }
void __sanitizer_cov_trace_cmp2(uint16_t a, uint16_t b)       { pt_cmp_log_int(2, a, b); }
void __sanitizer_cov_trace_cmp4(uint32_t a, uint32_t b)       { pt_cmp_log_int(4, a, b); }
void __sanitizer_cov_trace_cmp8(uint64_t a, uint64_t b)       { pt_cmp_log_int(8, a, b); }
void __sanitizer_cov_trace_const_cmp1(uint8_t a, uint8_t b)   { pt_cmp_log_int(1, a, b); }
void __sanitizer_cov_trace_const_cmp2(uint16_t a, uint16_t b) { pt_cmp_log_int(2, a, b); }
void __sanitizer_cov_trace_const_cmp4(uint32_t a, uint32_t b) { pt_cmp_log_int(4, a, b); }
void __sanitizer_cov_trace_const_cmp8(uint64_t a, uint64_t b) { pt_cmp_log_int(8, a, b); }

static void pt_cmp_publish(void) {
  if (!pt_cmp_check_enabled()) return;
  if (!pt_cmp_shm_ready) {
    pt_cmplog_init(pt_cmp_shm_name, PT_CMP_MAXBYTES);
    pt_cmp_shm_ready = 1;
  }
  pt_cmplog_publish_bytes(pt_cmp_buf, pt_cmp_len);
}

/* ---- file-dump path (unchanged; the fallback when $NELLI_COV_SHM unset) --- */

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

/* ---- shm path: gather THIS file's own sancov counters, wired the same way
 * pt_dump gathers them for the file path. Used by pt_cov_publish (below)
 * for a real external sancov-instrumented target; a Nim in-process worker
 * (E2b C3) calls `pt_shm_publish_bytes` (nelli_shm.c) directly instead —
 * its counters live in Nim memory, not here. */
static void pt_shm_publish_counters(void) {
  uint8_t* p; uint32_t cap;
  if (!pt_shm_begin(&p, &cap)) return;
  uint32_t total = 0;
#ifdef NELLI_COV_GCC
  uint32_t n = PT_MAPLEN < cap ? PT_MAPLEN : cap;
  memcpy(p, pt_map, n);
  total = PT_MAPLEN;
#else
  uint32_t off = 0;
  for (int r = 0; r < pt_nregions; r++) {
    uint8_t* s = pt_rstart[r];
    uint32_t rl = (uint32_t)(pt_rstop[r] - s);
    if (off < cap) {
      uint32_t take = rl;
      if (off + take > cap) take = cap - off;
      memcpy(p + off, s, take);
      off += take;
    }
    total += rl;
  }
#endif
  pt_shm_commit(total);
}

void pt_shm_reset(void) {
  /* Full per-input reset for THIS file's OWN sancov counters (zero the live
   * globals so the next run starts clean — mirrors `coverage.nim`'s
   * `resetCoverage` for the in-process Nim bitmap) plus the generic shm
   * staging-buffer reset (`pt_shm_reset_buffer`, nelli_shm.c). Ordering
   * matches that function's discipline: the live counters are zeroed
   * BEFORE its gate re-arm (its own LAST step), so a signal landing
   * mid-zero here ALSO finds `pt_dumped` still set and no-ops. */
#ifdef NELLI_COV_GCC
  memset(pt_map, 0, PT_MAPLEN);
  pt_prev = 0;   /* the AFL prev-loc edge-context fold — NOT just pt_map's byte
                  * values — must also restart at its fresh-process value, or a
                  * SECOND run's edges hash into different slots than an
                  * EQUIVALENT single-shot process would, purely because of
                  * PC history this run never executed. That is stale bleed
                  * too (a context leak, not a value leak) and defeats the
                  * whole point of per-input independence — caught by the
                  * "same input replayed after an intervening different
                  * input reproduces the same snapshot" characterization
                  * test (tests/tfuzzcovreset.nim, E2b C2). */
#else
  for (int r = 0; r < pt_nregions; r++)
    memset(pt_rstart[r], 0, (size_t)(pt_rstop[r] - pt_rstart[r]));
#endif
  pt_shm_reset_buffer();
  pt_cmp_len = 0;                 /* G4 C3: per-run isolation for a future persistent external target */
  pt_cmplog_reset_buffer();
}

/* ---- publish dispatcher: shm when configured, else the unchanged file path */

uint32_t pt_cov_total_len(void) {
  /* Current total byte length of THIS file's own sancov counter region(s) —
   * gcc's single fixed `pt_map`, or clang's sum of registered regions so
   * far. Exposed so a caller (a persistent-process test harness, or a real
   * external-target integration) can size `pt_shm_init`'s capacity to
   * exactly match what a fresh dump would report, instead of guessing. */
  uint32_t total = 0;
#ifdef NELLI_COV_GCC
  total = PT_MAPLEN;
#else
  for (int r = 0; r < pt_nregions; r++) total += (uint32_t)(pt_rstop[r] - pt_rstart[r]);
#endif
  return total;
}

static void pt_cov_publish(void) {
  const char* shmName = getenv("NELLI_COV_SHM");
  int shmAttached = pt_shm_capacity_get() != 0;
  int shmWanted = (shmName && shmName[0]) || shmAttached;
  /* An already-completed `pt_shm_init` call counts as shm mode too,
   * independent of the env var — a caller (a C-level test driver; a
   * persistent-worker Nim caller in E2b C3) that initialized shm directly,
   * without going through the env var, still wants THIS publish to land in
   * shm, not silently fall through to the file path. */
  if (shmWanted) {
    if (!shmAttached) {
      /* Lazy attach for a real external sancov target that never called
       * `pt_shm_init` itself (a persistent-worker-side Nim caller always
       * calls it explicitly first, with a capacity IT chose — see the
       * dlopen note in nelli_shm.c). Size from whatever this process's own
       * sancov registration total is right now — module-load-order caveats
       * are the same ones already documented for `pt_shm_init`. */
      uint32_t cap = pt_cov_total_len();
      if (cap == 0) cap = 1;
      pt_shm_init(shmName, cap);
    }
    pt_shm_publish_counters();
  } else {
    pt_dump();
  }
  pt_cmp_publish();
    /* RFC-fuzzer-nextgen G4 C3: fires from the SAME atexit/signal dispatch
     * as coverage, unconditionally — `pt_cmp_publish` is internally gated
     * on `$NELLI_CMP_SHM` (a no-op otherwise) and uses its OWN independent
     * `pt_cmplog_dumped` gate (not `pt_dumped`, which the branch above just
     * used for coverage), so this never starves — or is starved by — the
     * coverage publish just above it. */
}

void pt_shm_publish_now(void) {
  /* Public entry point for a PERSISTENT process to force a publish of THIS
   * file's own sancov counters between "runs" without waiting for process
   * exit/a signal — the C-level analog of what a Nim in-process worker does
   * explicitly via `pt_shm_publish_bytes` for its own bitmap. Only
   * meaningful once `$NELLI_COV_SHM`/`pt_shm_init` is in play; a no-op
   * (falls through to the gated no-op file dump) otherwise, matching
   * `pt_cov_publish`'s own fallback. */
  pt_cov_publish();
}

static void pt_sig(int sig) { pt_cov_publish(); signal(sig, SIG_DFL); raise(sig); }

__attribute__((constructor))
static void pt_init(void) {
  atexit(pt_cov_publish);
  int sigs[] = { SIGTERM, SIGINT, SIGSEGV, SIGABRT, SIGBUS, SIGFPE, SIGILL };
  for (unsigned i = 0; i < sizeof(sigs) / sizeof(sigs[0]); i++) signal(sigs[i], pt_sig);
}
