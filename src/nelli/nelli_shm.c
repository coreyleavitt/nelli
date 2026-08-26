/* nelli_shm.c — RFC-fuzzer-nextgen E2b: the double-buffered shm coverage
 * transport, extracted from nelli_cov.c into its OWN, dependency-free file.
 *
 * WHY a separate file rather than living inside nelli_cov.c (which already
 * has a `pt_shm_*` block E2b C1/C2 originally added there): nelli_cov.c also
 * carries a `__attribute__((constructor))` (`pt_init`) that installs process-
 * wide SIGTERM/SIGINT/SIGSEGV/SIGABRT/SIGBUS/SIGFPE/SIGILL handlers and an
 * `atexit` hook — exactly what an EXTERNAL, fresh-exec'd sancov target
 * needs, but NOT something a persistent Nim worker process wants pulled into
 * its OWN address space just to publish coverage: linking the whole of
 * nelli_cov.c into the nelli library would hijack every nelli user's signal
 * handlers process-wide (breaking, at minimum, Nim's own crash/stack-trace
 * handling) as an unintended side effect of E2b C3's Nim `shmProbe` wiring.
 * This file has NO constructor and installs NO signal handlers — the Nim
 * worker's own crash behavior (E2a's `observationForDeath`, detected by the
 * ORCHESTRATOR via a dead pipe, not by a handler in the worker) is untouched.
 *
 * nelli_cov.c still LINKS AGAINST this file (an `extern` of every symbol
 * below) for its OWN sancov-external-target shm support — `pt_shm_reset`/
 * `pt_shm_publish_counters`/`pt_cov_publish`/`pt_shm_publish_now` there
 * gather counters from `pt_map`/`pt_rstart`..`pt_rstop` (sancov-specific
 * globals that belong in nelli_cov.c, not here) and hand them to the
 * generic `pt_shm_begin`/`pt_shm_commit`/`pt_shm_publish_bytes` primitives
 * defined here. A Nim persistent worker (E2b C3, `coverage.nim`/
 * `fuzzworker.nim`) links ONLY this file and calls `pt_shm_publish_bytes`
 * directly with its OWN `{.cover.}` bitmap — no sancov globals in play at
 * all on that path.
 *
 * See the safety-discipline and dlopen-decision documentation on the E2b
 * design in `nelli_cov.c`'s history (same protocol, same reasoning) —
 * repeated in full here since this is now the canonical home of the
 * mechanism itself:
 *
 * Push/copy, not zero-copy: instrumented counters are ordinary static
 * globals a target writes IN PLACE — they cannot be relocated into shared
 * memory without per-target linker-script placement, so a directly-mapped
 * view is out of scope. `pt_shm_publish_bytes` COPIES a snapshot into one of
 * two shm-backed buffers, publishing it via an atomic generation word
 * (release-after-copy) so a reader (a DIFFERENT process, possibly mid-write
 * from this process's point of view — the first `CoverageProbe` for which
 * that is true) can trust a snapshot it reads acquire-before-trust.
 *
 * Layout (one contiguous mmap'd region):
 *   pt_shm_header | buf[0][capacity] | buf[1][capacity]
 *
 * Safety discipline (no `sigprocmask`, no second lock — a single `pt_dumped`
 * single-shot gate):
 *   - `pt_shm_reset_buffer()` (called by the worker BEFORE each input, never
 *     by the orchestrator — `CoverageProbe.resetsPerRun` is a pure
 *     capability flag, not a cross-process reset verb) zeroes ONLY the
 *     STAGING buffer (`1 - published`) — the buffer nobody ever reads — and
 *     re-arms `pt_dumped` as its LAST step, strictly AFTER the zero
 *     completes. A signal that lands mid-zero-loop finds `pt_dumped` still 1
 *     (from the PRIOR run's publish) and its own publish attempt is a
 *     no-op — so it can never race the in-progress zero, and the buffer a
 *     reader trusts (`published`) is never touched by reset at all.
 *   - `pt_shm_commit()` flips `published` (a plain store) and bumps
 *     `generation` LAST, via a release store — so a reader's acquire load of
 *     `generation` happens-before it trusts `published`/`buf_len`/the buffer
 *     bytes (all plain stores that preceded the release).
 *   - The reader (`pt_shm_read`) re-checks `generation` (acquire) AFTER
 *     copying the buffer out; if it changed, a publish raced the read and
 *     the reader retries against the new generation (bounded retries, then
 *     reports "no valid read" — absent, never torn).
 *
 * dlopen'd modules (RFC-pinned decision, not left silent): shm capacity is
 * FIXED at `pt_shm_init` — sized by the Nim caller (a fixed 8192 for the
 * in-process `{.cover.}` bitmap; dlopen is a non-issue there, it is not
 * dynamically-registered sancov state) or, for a real external sancov
 * target (nelli_cov.c's `pt_cov_publish`), from whatever total is current
 * when shm is first initialized. UNLIKE the file-dump path (which
 * recomputes its length fresh at every dump and so naturally unions any
 * module registered before THAT dump, dlopen'd or not), the shm path does
 * NOT grow after `pt_shm_init` — a module `dlopen`'d (and hence registering
 * a NEW counter region) AFTER shm capacity was fixed is DROPPED from the
 * shm view once the total exceeds capacity: `pt_shm_commit` clamps the copy
 * to `capacity` and sets `truncated` (queryable via `pt_shm_truncated()`).
 * This is the RFC's "documented shm-path regression for plugin-loading
 * targets" choice, made explicitly rather than the union-on-resize
 * alternative: resizing a shm segment a DIFFERENT process already has
 * mapped requires a resize-and-remap handshake across the worker/
 * orchestrator seam that is out of scope for this slice. A target that
 * `dlopen`s coverage-bearing plugins after startup should use the
 * file-dump transport, not shm, until a future slice adds that handshake.
 */
#include <stdint.h>
#include <string.h>
#include <signal.h>    /* sig_atomic_t only — no handlers installed here */
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

/* `pt_dumped` gates "at most one publish per run". `pt_shm_reset_buffer`
 * re-arms it between inputs in a persistent worker; a single-shot process
 * that never calls reset just never re-arms it (once-per-process). Shared
 * with nelli_cov.c's OWN file-dump gate when both files are linked together
 * (a real external sancov target) — declared here, `extern`'d there. */
volatile sig_atomic_t pt_dumped = 0;

typedef struct {
  unsigned int published;     /* 0 or 1: last COMPLETE, reader-safe buffer. Plain store/load — made visible via `generation`'s release/acquire, never written by reset. */
  unsigned int capacity;      /* fixed per-buffer byte capacity; 0 == not yet initialized (shm-header idempotency marker) */
  unsigned int buf_len[2];    /* valid byte count currently held in each buffer */
  sig_atomic_t truncated;     /* 1 iff a publish's source length ever exceeded capacity (the dlopen/late-registration regression signal, above) */
  unsigned int generation;    /* accessed ONLY via __atomic builtins; 0 == never published */
} pt_shm_header;

/* RFC-fuzzer-nextgen G4: `pt_shm_init` et al. below are a SINGLETON per
 * process — one `pt_shdr`/`pt_sbuf`/`pt_shm_cap` triple, matching the E2b
 * design brief ("ride E2b's shm transport") for the ONE coverage channel a
 * process ever needs. G4 adds a SECOND, independent per-run log (comparison
 * operand pairs) that must NOT share the coverage channel's shm segment —
 * `pt_shm_init` calling `pt_shm_init` again with a DIFFERENT name would hit
 * the `if (pt_shdr) return 0` idempotency guard and silently keep attached
 * to the FIRST (coverage's) segment, never opening the second at all.
 *
 * Rather than duplicate this whole protocol into a second copy-pasted file
 * (the design/audit cost of a second implementation to keep in sync), the
 * six core operations are parameterized over an explicit `pt_shm_channel`
 * instead of module statics. The ORIGINAL zero-argument functions below
 * (`pt_shm_init`, `pt_shm_reset_buffer`, `pt_shm_begin`, `pt_shm_commit`,
 * `pt_shm_publish_bytes`, `pt_shm_read`, `pt_shm_capacity_get`,
 * `pt_shm_truncated`) become thin wrappers over a DEFAULT static channel —
 * byte-identical behavior/ABI for every existing caller (coverage.nim,
 * fuzzworker.nim, nelli_cov.c, tfuzzcovshm.nim's driver) — so nothing
 * calling them needs to change. G4's cmp-log channel (further below) is a
 * SECOND static channel reached through its own `pt_cmplog_*` names, built
 * on the identical, already-audited push/copy + generation-word protocol. */

typedef struct {
  pt_shm_header* shdr;
  uint8_t* sbuf[2];
  uint32_t cap;
} pt_shm_channel;

static int pt_shm_ch_init(pt_shm_channel* ch, const char* name, uint32_t capacity) {
  if (ch->shdr) return 0;                             /* idempotent: already attached in THIS process */
  if (!name || !name[0] || capacity == 0) return -1;
  size_t sz = sizeof(pt_shm_header) + 2u * (size_t)capacity;
  int fd = shm_open(name, O_CREAT | O_RDWR, 0600);
  if (fd < 0) return -1;
  if (ftruncate(fd, (off_t)sz) != 0) { close(fd); return -1; }
  void* mem = mmap(NULL, sz, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  close(fd);
  if (mem == MAP_FAILED) return -1;
  ch->shdr = (pt_shm_header*)mem;
  ch->sbuf[0] = (uint8_t*)mem + sizeof(pt_shm_header);
  ch->sbuf[1] = ch->sbuf[0] + capacity;
  ch->cap = capacity;
  if (ch->shdr->capacity == 0) {
    /* First process to reach here (the creator, or a racing-but-first
     * attacher of a freshly ftruncate'd all-zero segment) performs the
     * one-time header init. A LATER attacher (e.g. a worker attaching after
     * the orchestrator pre-created the segment) sees `capacity != 0` and
     * skips straight past — never re-zeroing a header a producer may
     * already be publishing through. */
    ch->shdr->capacity = capacity;
    ch->shdr->published = 0;
    ch->shdr->buf_len[0] = 0;
    ch->shdr->buf_len[1] = 0;
    ch->shdr->truncated = 0;
    __atomic_store_n(&ch->shdr->generation, 0u, __ATOMIC_RELAXED);
  }
  return 0;
}

static uint32_t pt_shm_ch_capacity_get(pt_shm_channel* ch) { return ch->shdr ? ch->shdr->capacity : 0; }
static int pt_shm_ch_truncated(pt_shm_channel* ch) { return ch->shdr ? (int)ch->shdr->truncated : 0; }

static void pt_shm_slow_zero(uint8_t* p, uint32_t n);   /* forward decl; defined below */

static void pt_shm_ch_reset_buffer(pt_shm_channel* ch) {
  if (!ch->shdr) return;
  unsigned int target = 1u - ch->shdr->published;
  pt_shm_slow_zero(ch->sbuf[target], ch->cap);
  ch->shdr->buf_len[target] = 0;
  pt_dumped = 0;                                       /* re-arm LAST */
}

static int pt_shm_ch_begin(pt_shm_channel* ch, uint8_t** outPtr, uint32_t* outCapacity) {
  if (!ch->shdr || pt_dumped) return 0;
  pt_dumped = 1;
  unsigned int target = 1u - ch->shdr->published;
  *outPtr = ch->sbuf[target];
  *outCapacity = ch->cap;
  return 1;
}

static void pt_shm_ch_commit(pt_shm_channel* ch, uint32_t totalLen) {
  if (!ch->shdr) return;
  unsigned int target = 1u - ch->shdr->published;
  uint32_t len = totalLen;
  if (len > ch->cap) { len = ch->cap; ch->shdr->truncated = 1; }
  ch->shdr->buf_len[target] = len;
  ch->shdr->published = target;                        /* plain store */
  uint32_t g = __atomic_load_n(&ch->shdr->generation, __ATOMIC_RELAXED);
  __atomic_store_n(&ch->shdr->generation, g + 1, __ATOMIC_RELEASE);
}

static void pt_shm_ch_publish_bytes(pt_shm_channel* ch, const uint8_t* data, uint32_t len) {
  uint8_t* p; uint32_t cap;
  if (!pt_shm_ch_begin(ch, &p, &cap)) return;
  uint32_t n = len < cap ? len : cap;
  memcpy(p, data, n);
  pt_shm_ch_commit(ch, len);
}

static int pt_shm_ch_read(pt_shm_channel* ch, uint8_t* out, uint32_t outCap, uint32_t* outLen) {
  if (!ch->shdr) return 0;
  uint32_t g1 = __atomic_load_n(&ch->shdr->generation, __ATOMIC_ACQUIRE);
  if (g1 == 0) { *outLen = 0; return 1; }
  for (int attempt = 0; attempt < 4; attempt++) {
    unsigned int a = ch->shdr->published;               /* plain load; safe — happens-after the acquire above */
    uint32_t len = ch->shdr->buf_len[a];
    uint32_t n = len < outCap ? len : outCap;
    memcpy(out, ch->sbuf[a], n);
    uint32_t g2 = __atomic_load_n(&ch->shdr->generation, __ATOMIC_ACQUIRE);
    if (g2 == g1) { *outLen = n; return 1; }             /* stable: no publish raced this copy */
    g1 = g2;                                             /* a publish landed mid-copy: retry against the new generation */
  }
  return 0;
}

/* ---- default channel: the ORIGINAL names, unchanged behavior/ABI --------- */

static pt_shm_channel pt_default_channel = { NULL, { NULL, NULL }, 0 };

int pt_shm_init(const char* name, uint32_t capacity) {
  return pt_shm_ch_init(&pt_default_channel, name, capacity);
}
uint32_t pt_shm_capacity_get(void) { return pt_shm_ch_capacity_get(&pt_default_channel); }
int pt_shm_truncated(void) { return pt_shm_ch_truncated(&pt_default_channel); }

static void pt_shm_slow_zero(uint8_t* p, uint32_t n) {
  /* A plain per-byte `volatile` store loop rather than `memset`. Production
   * capacities here are small (an 8 KB `{.cover.}` bitmap, a modest sancov
   * map) so this costs nothing that matters; what it buys is a zero that
   * genuinely takes measurable, roughly-linear time for ANY capacity,
   * including a large TEST-chosen one — `memset` on most libcs is fast
   * enough (vectorized/`rep stos`) that a signal has essentially no window
   * to land mid-zero even at several MB, which would make the "signal
   * mid-reset" hazard untestable without an implausibly large buffer. The
   * `volatile` qualifier blocks the compiler from recognizing this loop as
   * memset and re-vectorizing it back into an effectively-atomic write. */
  volatile uint8_t* vp = p;
  for (uint32_t i = 0; i < n; i++) vp[i] = 0;
}

void pt_shm_reset_buffer(void) {
  /* Generic staging-buffer reset — see the module doc above for why
   * re-arming `pt_dumped` LAST is what makes this safe against a signal
   * landing mid-zero. Callable directly (e.g. via Nim `importc`) by a
   * producer whose live counters live outside this file (the in-process Nim
   * `{.cover.}` bitmap, which resets its OWN counters via `resetCoverage`
   * first — see `coverage.nim`'s `shmProbe`/worker wiring, E2b C3). */
  pt_shm_ch_reset_buffer(&pt_default_channel);
}

int pt_shm_begin(uint8_t** outPtr, uint32_t* outCapacity) {
  /* Low-level publish half 1/2: gate-check + hand the caller a direct
   * pointer to the staging buffer to fill (possibly via several partial
   * writes — nelli_cov.c's clang multi-region gather does this). Returns 0
   * (caller must not write or call `pt_shm_commit`) if shm isn't
   * initialized or this run already published. */
  return pt_shm_ch_begin(&pt_default_channel, outPtr, outCapacity);
}

void pt_shm_commit(uint32_t totalLen) {
  /* Low-level publish half 2/2: finalize the staging buffer `pt_shm_begin`
   * handed out — clamp/flag truncation, then the atomic release-store
   * handoff (`generation`) that makes it the published, reader-trusted
   * buffer. */
  pt_shm_ch_commit(&pt_default_channel, totalLen);
}

void pt_shm_publish_bytes(const uint8_t* data, uint32_t len) {
  /* Convenience wrapper over begin/commit for a single contiguous source —
   * what a Nim caller (a single `seq[uint8]` bitmap) uses directly. */
  pt_shm_ch_publish_bytes(&pt_default_channel, data, len);
}

int pt_shm_read(uint8_t* out, uint32_t outCap, uint32_t* outLen) {
  /* Acquire-before-trust reader, safe from a DIFFERENT process. Returns 1
   * with `*outLen == 0` if nothing has ever been published (never touches
   * `out` in that case) — absent, never stale/torn. Returns 0 only if a
   * publish kept racing the read past the retry bound (never returns a
   * torn buffer). */
  return pt_shm_ch_read(&pt_default_channel, out, outCap, outLen);
}

/* ---- cmp-log channel (RFC-fuzzer-nextgen G4 C2): a SECOND, independent
 * shm segment for the comparison operand-pair log — same protocol, own
 * static state, own name, so it never collides with the coverage channel
 * above even when BOTH are attached in the same process (a real persistent
 * worker with $NELLI_COV_SHM and $NELLI_CMP_SHM both set). ------------- */

static pt_shm_channel pt_cmplog_channel = { NULL, { NULL, NULL }, 0 };

int pt_cmplog_init(const char* name, uint32_t capacity) {
  return pt_shm_ch_init(&pt_cmplog_channel, name, capacity);
}
void pt_cmplog_reset_buffer(void) { pt_shm_ch_reset_buffer(&pt_cmplog_channel); }
void pt_cmplog_publish_bytes(const uint8_t* data, uint32_t len) {
  pt_shm_ch_publish_bytes(&pt_cmplog_channel, data, len);
}
int pt_cmplog_read(uint8_t* out, uint32_t outCap, uint32_t* outLen) {
  return pt_shm_ch_read(&pt_cmplog_channel, out, outCap, outLen);
}
uint32_t pt_cmplog_capacity_get(void) { return pt_shm_ch_capacity_get(&pt_cmplog_channel); }
