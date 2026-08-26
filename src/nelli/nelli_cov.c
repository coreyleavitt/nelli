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
#include <sys/mman.h>  /* shm_open/mmap (E2b shm transport) */
#include <sys/stat.h>

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

/* `pt_dumped` gates "at most one publish per run" — originally "per process"
 * (the E2a file-dump interim path: a fresh worker process per input, so
 * once-per-process WAS once-per-run). E2b's `pt_shm_reset_buffer()` (below)
 * re-arms it explicitly between inputs in a PERSISTENT worker, so the same
 * gate now reads as "at most one publish per run" in both regimes — a
 * single-shot process just never re-arms it, which is exactly today's
 * behavior, unchanged. */
static volatile sig_atomic_t pt_dumped = 0;

/* ---- E2b: double-buffered shm coverage transport --------------------------
 *
 * Push/copy, not zero-copy (RFC-fuzzer-nextgen E2b): the clang inline-8bit
 * counters / gcc trace-pc bitmap are ordinary static globals the instrumented
 * target writes IN PLACE — they cannot be relocated into shared memory
 * without per-target linker-script placement, so a directly-mapped view is
 * out of scope. Instead, `pt_shm_publish_bytes` COPIES a snapshot into one of
 * two shm-backed buffers, publishing it via an atomic generation word
 * (release-after-copy) so a reader (a DIFFERENT process, possibly mid-write
 * from this process's point of view — the first `CoverageProbe` for which
 * that is true) can trust a snapshot it reads acquire-before-trust.
 *
 * Layout (one contiguous mmap'd region):
 *   pt_shm_header | buf[0][capacity] | buf[1][capacity]
 *
 * Generic over the counter SOURCE: `pt_shm_publish_bytes`/`pt_shm_begin`/
 * `pt_shm_commit` take a raw `(ptr, len)` — used internally by this file's
 * own sancov gather (gcc's single `pt_map`, clang's multi-region walk) AND,
 * via Nim `importc`, by a persistent in-process Nim worker publishing its
 * OWN `{.cover.}` bitmap (`coverage.nim`) through this exact mechanism
 * (E2b C3) — one publish/read protocol, two producers.
 *
 * Safety discipline (no `sigprocmask`, no second lock — reuses the SAME
 * `pt_dumped` single-shot gate the file-dump path already trusts):
 *   - `pt_shm_reset_buffer()` (called by the worker BEFORE each input, never
 *     by the orchestrator — `CoverageProbe.resetsPerRun` is a pure
 *     capability flag, not a cross-process reset verb) zeroes ONLY the
 *     STAGING buffer (`1 - published`) — the buffer nobody ever reads — and
 *     re-arms `pt_dumped` as its LAST step, strictly AFTER the zero
 *     completes. A signal that lands mid-zero-loop (an async SIGTERM/SIGINT,
 *     or a synchronous crash signal from buggy code running during reset)
 *     finds `pt_dumped` still 1 (from the PRIOR run's publish) and its own
 *     publish attempt is a no-op — so it can never race the in-progress
 *     zero, and the buffer a reader trusts (`published`) is never touched by
 *     reset at all. Only once reset's zero is complete and the gate is
 *     re-armed can a subsequent publish (normal end-of-run, or a crash mid
 *     THIS run) proceed — and that publish targets the SAME
 *     freshly-zeroed staging buffer, now safe to overwrite wholesale.
 *   - `pt_shm_commit()` flips `published` (a plain store) and bumps
 *     `generation` LAST, via a release store — so a reader's acquire load of
 *     `generation` happens-before it trusts `published`/`buf_len`/the buffer
 *     bytes (all plain stores that preceded the release).
 *   - The reader (`pt_shm_read`) re-checks `generation` (acquire) AFTER
 *     copying the buffer out; if it changed, a publish raced the read and
 *     the reader retries against the new generation (bounded retries, then
 *     reports "no valid read" — D7's "absent, never torn," never a torn
 *     buffer handed to a caller).
 *
 * dlopen'd modules (RFC-pinned decision, not left silent): shm capacity is
 * FIXED at `pt_shm_init` — sized either by the Nim caller (a fixed 8192 for
 * the in-process `{.cover.}` bitmap; dlopen is a non-issue there, it is not
 * dynamically-registered sancov state) or, for a real external sancov
 * target, from whatever `pt_nregions` total is current when shm is first
 * initialized. UNLIKE the file-dump path (`pt_dump`, which recomputes `len`
 * fresh at every dump and so naturally unions any module registered before
 * THAT dump, dlopen'd or not), the shm path does NOT grow after `pt_shm_init`
 * — a module `dlopen`'d (and hence sancov-registering its counter region)
 * AFTER shm capacity was fixed is DROPPED from the shm view once the total
 * exceeds capacity: `pt_shm_commit` clamps the copy to `capacity` and sets
 * `truncated` (queryable via `pt_shm_truncated()`). This is the RFC's
 * "documented shm-path regression for plugin-loading targets" choice, made
 * explicitly rather than the union-on-resize alternative: resizing a shm
 * segment that a DIFFERENT process already has mapped requires a
 * resize-and-remap handshake across the worker/orchestrator seam that is out
 * of scope for this slice. A target that `dlopen`s coverage-bearing plugins
 * after startup should use the file-dump transport (leave `$NELLI_COV_SHM`
 * unset), not shm, until a future slice adds that handshake.
 */

typedef struct {
  unsigned int published;     /* 0 or 1: last COMPLETE, reader-safe buffer. Plain store/load — made visible via `generation`'s release/acquire, never written by reset. */
  unsigned int capacity;      /* fixed per-buffer byte capacity; 0 == not yet initialized (shm-header idempotency marker) */
  unsigned int buf_len[2];    /* valid byte count currently held in each buffer */
  sig_atomic_t truncated;     /* 1 iff a publish's source length ever exceeded capacity (the dlopen/late-registration regression signal, above) */
  unsigned int generation;    /* accessed ONLY via __atomic builtins; 0 == never published */
} pt_shm_header;

static pt_shm_header* pt_shdr = NULL;
static uint8_t* pt_sbuf[2] = { NULL, NULL };
static uint32_t pt_shm_cap = 0;

int pt_shm_init(const char* name, uint32_t capacity) {
  if (pt_shdr) return 0;                              /* idempotent: already attached in THIS process */
  if (!name || !name[0] || capacity == 0) return -1;
  size_t sz = sizeof(pt_shm_header) + 2u * (size_t)capacity;
  int fd = shm_open(name, O_CREAT | O_RDWR, 0600);
  if (fd < 0) return -1;
  if (ftruncate(fd, (off_t)sz) != 0) { close(fd); return -1; }
  void* mem = mmap(NULL, sz, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  close(fd);
  if (mem == MAP_FAILED) return -1;
  pt_shdr = (pt_shm_header*)mem;
  pt_sbuf[0] = (uint8_t*)mem + sizeof(pt_shm_header);
  pt_sbuf[1] = pt_sbuf[0] + capacity;
  pt_shm_cap = capacity;
  if (pt_shdr->capacity == 0) {
    /* First process to reach here (the creator, or a racing-but-first
     * attacher of a freshly ftruncate'd all-zero segment) performs the
     * one-time header init. A LATER attacher (e.g. this same process's own
     * orchestrator side, or a worker attaching after the orchestrator
     * pre-created the segment) sees `capacity != 0` and skips straight past
     * — never re-zeroing a header a producer may already be publishing
     * through. */
    pt_shdr->capacity = capacity;
    pt_shdr->published = 0;
    pt_shdr->buf_len[0] = 0;
    pt_shdr->buf_len[1] = 0;
    pt_shdr->truncated = 0;
    __atomic_store_n(&pt_shdr->generation, 0u, __ATOMIC_RELAXED);
  }
  return 0;
}

uint32_t pt_shm_capacity_get(void) { return pt_shdr ? pt_shdr->capacity : 0; }
int pt_shm_truncated(void) { return pt_shdr ? (int)pt_shdr->truncated : 0; }

void pt_shm_reset_buffer(void) {
  /* Generic staging-buffer reset — see the module doc above for why
   * re-arming `pt_dumped` LAST is what makes this safe against a signal
   * landing mid-zero. Callable directly (e.g. via Nim `importc`) by a
   * producer whose live counters live outside this file (the in-process Nim
   * `{.cover.}` bitmap, which resets its OWN counters via `resetCoverage`);
   * `pt_shm_reset` (below) wraps this for this file's OWN sancov counters. */
  if (!pt_shdr) return;
  unsigned int target = 1u - pt_shdr->published;
  memset(pt_sbuf[target], 0, pt_shm_cap);
  pt_shdr->buf_len[target] = 0;
  pt_dumped = 0;                                      /* re-arm LAST */
}

int pt_shm_begin(uint8_t** outPtr, uint32_t* outCapacity) {
  /* Low-level publish half 1/2: gate-check + hand the caller a direct
   * pointer to the staging buffer to fill (possibly via several partial
   * writes — the clang multi-region gather does this). Returns 0 (caller
   * must not write or call `pt_shm_commit`) if shm isn't initialized or this
   * run already published. */
  if (!pt_shdr || pt_dumped) return 0;
  pt_dumped = 1;
  unsigned int target = 1u - pt_shdr->published;
  *outPtr = pt_sbuf[target];
  *outCapacity = pt_shm_cap;
  return 1;
}

void pt_shm_commit(uint32_t totalLen) {
  /* Low-level publish half 2/2: finalize the staging buffer `pt_shm_begin`
   * handed out — clamp/flag truncation, then the atomic release-store
   * handoff (`generation`) that makes it the published, reader-trusted
   * buffer. */
  if (!pt_shdr) return;
  unsigned int target = 1u - pt_shdr->published;
  uint32_t len = totalLen;
  if (len > pt_shm_cap) { len = pt_shm_cap; pt_shdr->truncated = 1; }
  pt_shdr->buf_len[target] = len;
  pt_shdr->published = target;                        /* plain store */
  uint32_t g = __atomic_load_n(&pt_shdr->generation, __ATOMIC_RELAXED);
  __atomic_store_n(&pt_shdr->generation, g + 1, __ATOMIC_RELEASE);
}

void pt_shm_publish_bytes(const uint8_t* data, uint32_t len) {
  /* Convenience wrapper over begin/commit for a single contiguous source —
   * what a Nim caller (a single `seq[uint8]` bitmap) uses directly. */
  uint8_t* p; uint32_t cap;
  if (!pt_shm_begin(&p, &cap)) return;
  uint32_t n = len < cap ? len : cap;
  memcpy(p, data, n);
  pt_shm_commit(len);
}

int pt_shm_read(uint8_t* out, uint32_t outCap, uint32_t* outLen) {
  /* Acquire-before-trust reader, safe from a DIFFERENT process. Returns 1
   * with `*outLen == 0` if nothing has ever been published (never touches
   * `out` in that case) — D7's "absent, never stale/torn" extended to shm.
   * Returns 0 only if a publish kept racing the read past the retry bound
   * (never returns a torn buffer). */
  if (!pt_shdr) return 0;
  uint32_t g1 = __atomic_load_n(&pt_shdr->generation, __ATOMIC_ACQUIRE);
  if (g1 == 0) { *outLen = 0; return 1; }
  for (int attempt = 0; attempt < 4; attempt++) {
    unsigned int a = pt_shdr->published;              /* plain load; safe — happens-after the acquire above */
    uint32_t len = pt_shdr->buf_len[a];
    uint32_t n = len < outCap ? len : outCap;
    memcpy(out, pt_sbuf[a], n);
    uint32_t g2 = __atomic_load_n(&pt_shdr->generation, __ATOMIC_ACQUIRE);
    if (g2 == g1) { *outLen = n; return 1; }           /* stable: no publish raced this copy */
    g1 = g2;                                           /* a publish landed mid-copy: retry against the new generation */
  }
  return 0;
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
 * (E2b C3) calls `pt_shm_publish_bytes` directly instead — its counters
 * live in Nim memory, not here. */
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
   * staging-buffer reset. Ordering matches `pt_shm_reset_buffer`'s
   * discipline: the live counters are zeroed BEFORE the gate is re-armed
   * (inside `pt_shm_reset_buffer`, called last), so a signal landing
   * mid-zero here ALSO finds `pt_dumped` still set and no-ops. */
#ifdef NELLI_COV_GCC
  memset(pt_map, 0, PT_MAPLEN);
#else
  for (int r = 0; r < pt_nregions; r++)
    memset(pt_rstart[r], 0, (size_t)(pt_rstop[r] - pt_rstart[r]));
#endif
  pt_shm_reset_buffer();
}

/* ---- publish dispatcher: shm when configured, else the unchanged file path */

static void pt_cov_publish(void) {
  const char* shmName = getenv("NELLI_COV_SHM");
  if (shmName && shmName[0]) {
    if (!pt_shdr) {
      /* Lazy attach for a real external sancov target that never called
       * `pt_shm_init` itself (a persistent-worker-side Nim caller always
       * calls it explicitly first, with a capacity IT chose — see the
       * dlopen note above). Size from whatever this process's own sancov
       * registration total is right now — module-load-order caveats are
       * the same ones already documented for `pt_shm_init`. */
      uint32_t cap = 0;
#ifdef NELLI_COV_GCC
      cap = PT_MAPLEN;
#else
      for (int r = 0; r < pt_nregions; r++) cap += (uint32_t)(pt_rstop[r] - pt_rstart[r]);
#endif
      if (cap == 0) cap = 1;
      pt_shm_init(shmName, cap);
    }
    pt_shm_publish_counters();
  } else {
    pt_dump();
  }
}

static void pt_sig(int sig) { pt_cov_publish(); signal(sig, SIG_DFL); raise(sig); }

__attribute__((constructor))
static void pt_init(void) {
  atexit(pt_cov_publish);
  int sigs[] = { SIGTERM, SIGINT, SIGSEGV, SIGABRT, SIGBUS, SIGFPE, SIGILL };
  for (unsigned i = 0; i < sizeof(sigs) / sizeof(sigs[0]); i++) signal(sigs[i], pt_sig);
}
