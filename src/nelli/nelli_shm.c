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
 * RFC-fuzzer-nextgen E4b: Windows has no `shm_open`/`mmap` — the identical
 * push/copy + generation-word protocol above is retargeted onto
 * `CreateFileMapping`/`MapViewOfFile`/`UnmapViewOfFile`/`CloseHandle`
 * (`pt_shm_ch_init`'s `#ifdef _WIN32` arm, below). `CreateFileMapping(
 * INVALID_HANDLE_VALUE, ..., name)` already implements create-or-open by
 * name in ONE call (the first caller creates a zero-initialized
 * pagefile-backed section; every later caller with the same name attaches
 * to the SAME section, ignoring its own size argument) — the direct
 * Windows analog of `shm_open(name, O_CREAT | O_RDWR, ...)`, so no separate
 * `OpenFileMapping` probe-then-fallback is needed (and would only add a
 * TOCTOU race between the probe and a subsequent create). Unlike the POSIX
 * arm (which closes its `fd` immediately after `mmap` — the kernel keeps
 * the mapping alive via the VMA alone), the Windows arm KEEPS its
 * `HANDLE` open in `pt_shm_channel.hMap` for as long as the segment stays
 * attached: Microsoft's own "fully close" sequence requires BOTH
 * `UnmapViewOfFile` AND `CloseHandle` (in either order) before a named
 * section is released, so re-attaching to a DIFFERENT name (the same
 * "don't leak one mapping per distinct name visited" concern the POSIX
 * `munmap` comment above already documents) must call both, mirrored
 * exactly below.
 *
 * Naming: a POSIX segment name looks like `"/nelli_..."` (a leading `/`,
 * exactly what every existing shm-name caller in this codebase already
 * uses unchanged on Windows — coverage.nim/fuzzworker.nim never
 * special-case the platform when choosing a name). An unqualified Windows
 * kernel-object name is scoped to the caller's own Terminal-Services
 * session by default, which already matches this codebase's only topology
 * (an orchestrator and the worker process IT spawned, always in the same
 * session); `pt_shm_win_name` (below) is the ONE function that derives the
 * Windows object name from that same nominal name — strip the leading
 * `/`, prefix `"Local\\"` to make that session-local scoping explicit
 * rather than implicit. Every caller of `pt_shm_ch_init` on Windows
 * funnels through this one function, so the
 * orchestrator and worker process can never independently compute two
 * different object names for what Nim believes is the same segment.
 * Deliberately compiled UNCONDITIONALLY (not `#ifdef`-gated to `_WIN32`)
 * so it is a plain, syscall-free string transform a POSIX-run test can
 * call directly (via a thin Nim `importc`) and pin byte-for-byte, rather
 * than trusting it un-exercised until a Windows CI push — see
 * `tests/tfuzzwinshm.nim`'s un-gated naming-function suite.
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
#include <stdlib.h>    /* getenv — the NELLI_COV_DEBUG channel below */
#include <stdio.h>     /* snprintf — pt_shm_win_name only, but kept unconditional
                        * so that function compiles (and is Nim-testable) on every
                        * platform, not just under _WIN32 — see its own comment.
                        * Also fprintf, for the debug channel below. */
#include <signal.h>    /* sig_atomic_t only — no handlers installed here */
#ifdef _WIN32
#include <windows.h>
#else
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#endif

/* RFC-fuzzer-nextgen E4c C3 round 2: the shm-side half of nelli_cov.c's
 * opt-in `NELLI_COV_DEBUG` channel (see that file's module doc for the full
 * motivation — a `fuzzer-windows` CI failure this repo's local mingw
 * toolchain cannot reproduce: no Windows-targeted clang exists locally to
 * probe whether the gap is in trace-cmp instrumentation or here, in the
 * actual `CreateFileMapping`/`MapViewOfFile` attach). Independently checked/
 * cached here (a separate translation unit from nelli_cov.c, deliberately —
 * see this file's own module doc on why it stays dependency-free) rather
 * than sharing a flag across files. Zero-cost when unset. */
static int pt_debug_enabled(void) {
  static int v = -1;
  if (v < 0) {
    const char* e = getenv("NELLI_COV_DEBUG");
    v = (e && e[0]) ? 1 : 0;
  }
  return v;
}
#define PT_DBG(...) do { if (pt_debug_enabled()) { fprintf(stderr, "[nelli_shm] " __VA_ARGS__); fflush(stderr); } } while (0)

#ifdef __cplusplus
extern "C" {
  /* RFC-fuzzer-nextgen E4b: this file is designed as a plain-C module with
   * C linkage throughout (every Nim `importc` below expects the PLAIN,
   * unmangled names `pt_shm_init`/`pt_shm_win_name`/etc.) — but a `nim cpp`
   * build's toolchain selection can compile a `{.compile: "nelli_shm.c".}`
   * source through the C++ front end for a GIVEN target configuration
   * (observed on the Windows cross-compile leg, where the mingw C++ driver
   * is registered as the backend's compiler; not observed natively on
   * Linux, where the same `nim cpp` build already links this file's
   * symbols correctly — see `tests/tfuzzwinshm.nim`'s POSIX suite passing
   * under both `c` and `cpp` backends). Guarding the whole file in
   * `extern "C"` when compiled as C++ keeps every symbol's linkage name
   * identical to a plain-C compile regardless of which front end a given
   * target configuration happens to route it through — a standard,
   * zero-cost C/C++ interop guard, not new coupling to any platform.
   */
#endif

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
  unsigned int generation;    /* accessed ONLY via pt_gen_load/pt_gen_store, below; 0 == never published */
} pt_shm_header;

/* `generation`'s load/store operations, factored out of the call sites
 * below (RFC-fuzzer-nextgen: MSVC parity). GCC/Clang's arm calls the EXACT
 * same `__atomic_load_n`/`__atomic_store_n` builtins, with the SAME memory-
 * order constant at each call site, this file always used -- unchanged
 * codegen from before this shim existed. MSVC's C compiler has no
 * `__atomic_*` builtin (and C11 `<stdatomic.h>` support is inconsistent
 * across the cl.exe versions this repo might build with), so its arm uses
 * `_InterlockedCompareExchange`/`_InterlockedExchange` from `<intrin.h>` --
 * both compile to a `lock`-prefixed instruction on x86/x64, a full
 * (sequentially-consistent) fence that is a strict superset of every
 * ordering requested below (relaxed, acquire, or release) -- so using it
 * uniformly for all three call sites is strictly STRONGER, never weaker,
 * than what each site asks for; the `acquire`/`release` parameters are
 * simply ignored on that arm. `generation` itself stays a plain,
 * non-`_Atomic`, non-`volatile` `unsigned int` in the struct on BOTH
 * toolchains, so the shared-memory header's layout/size is identical
 * regardless of which side built a given process -- only the OPERATIONS on
 * it differ. */
#if defined(_MSC_VER)
#include <intrin.h>
static uint32_t pt_gen_load(unsigned int* p, int acquire) {
  (void)acquire;
  return (uint32_t)_InterlockedCompareExchange((volatile long*)p, 0, 0);
}
static void pt_gen_store(unsigned int* p, uint32_t v, int release) {
  (void)release;
  (void)_InterlockedExchange((volatile long*)p, (long)v);
}
#else
static uint32_t pt_gen_load(unsigned int* p, int acquire) {
  return acquire ? __atomic_load_n(p, __ATOMIC_ACQUIRE)
                  : __atomic_load_n(p, __ATOMIC_RELAXED);
}
static void pt_gen_store(unsigned int* p, uint32_t v, int release) {
  if (release) __atomic_store_n(p, v, __ATOMIC_RELEASE);
  else __atomic_store_n(p, v, __ATOMIC_RELAXED);
}
#endif

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
  volatile sig_atomic_t* dumped;
    /* RFC-fuzzer-nextgen G4: each channel's OWN "published at most once
     * this run" gate — NOT necessarily the same variable across channels.
     * The default channel points at the process-wide `pt_dumped` (below),
     * preserving its EXISTING cross-file coupling with nelli_cov.c's
     * file-dump gate (the two are deliberately unified: a real external
     * target publishes coverage via file XOR shm, never both, so they
     * share one flag). The cmp-log channel points at its OWN independent
     * static gate instead — it has no file-dump alternative to unify
     * with, and sharing the coverage channel's gate would be a genuine
     * bug: whichever channel published FIRST in a given run would leave
     * `pt_dumped` set, silently starving the OTHER channel's publish for
     * the rest of that run. */
  char attached_name[256];
  size_t mapped_size;
    /* RFC-fuzzer-nextgen G4 C3: which segment (if any) is CURRENTLY
     * mapped, and how big that mapping is — see `pt_shm_ch_init`'s
     * re-attach handling below for why this pair is needed, not just the
     * `shdr != NULL` check the original single-segment-per-process design
     * got away with. */
#ifdef _WIN32
  HANDLE hMap;
    /* RFC-fuzzer-nextgen E4b: the file-mapping HANDLE the current `shdr`
     * view came from — POSIX has no equivalent field because its `fd` is
     * closed right after `mmap` (see the module doc comment's "unlike the
     * POSIX arm" note); Windows must keep this open until re-attach/never,
     * to fully release the named section via `CloseHandle`. */
#endif
} pt_shm_channel;

void pt_shm_win_name(const char* name, char* out, size_t outCap) {
  /* The ONE naming function — see the module doc comment. Compiled on every
   * platform (no Windows-only dependency: it's a plain string transform;
   * non-`static` so a POSIX-run test can `importc` and pin it directly via
   * `tests/tfuzzwinshm.nim`'s un-gated suite) — only the `#ifdef _WIN32` arm
   * of `pt_shm_ch_init` below actually calls it for real. */
  if (outCap == 0) return;
  const char* base = name ? name : "";
  if (base[0] == '/') base++;
  int n = snprintf(out, outCap, "Local\\%s", base);
  if (n < 0) out[0] = 0;
}

static int pt_shm_ch_init(pt_shm_channel* ch, const char* name, uint32_t capacity) {
  if (!name || !name[0] || capacity == 0) return -1;
  if (ch->shdr) {
    if (strcmp(ch->attached_name, name) == 0) return 0;
      /* idempotent: already attached to THIS SAME segment — the common
       * case every existing caller relies on (coverage.nim's
       * shmReset/Publish/Read all re-`init` defensively on every call with
       * the SAME name every time). */
    /* A DIFFERENT name: re-attach. Without this, a process that reads (or
     * writes) more than one DISTINCTLY-NAMED segment of the same channel
     * over its lifetime — a test runner moving from one test case's shm
     * name to the next; an orchestrator reading several workers' own
     * per-worker segments — would silently keep the FIRST segment it ever
     * attached to forever, returning that stale segment's contents for
     * every later name as if it were the one just asked for. Unmap the
     * stale mapping first so a long-lived reader (the orchestrator case)
     * doesn't leak one mapping per distinct name it ever visits. */
#ifdef _WIN32
    UnmapViewOfFile((LPCVOID)ch->shdr);
    if (ch->hMap) CloseHandle(ch->hMap);
    ch->hMap = NULL;
#else
    munmap(ch->shdr, ch->mapped_size);
#endif
    ch->shdr = NULL;
  }
  size_t sz = sizeof(pt_shm_header) + 2u * (size_t)capacity;
  void* mem;
#ifdef _WIN32
  char winName[300];
  pt_shm_win_name(name, winName, sizeof(winName));
  PT_DBG("pt_shm_ch_init: name=\"%s\" -> transformed=\"%s\" size=%llu\n",
         name, winName, (unsigned long long)sz);
  DWORD szHigh = (DWORD)(((unsigned long long)sz >> 32) & 0xFFFFFFFFull);
  DWORD szLow  = (DWORD)((unsigned long long)sz & 0xFFFFFFFFull);
  HANDLE hMap = CreateFileMappingA(INVALID_HANDLE_VALUE, NULL, PAGE_READWRITE,
                                    szHigh, szLow, winName);
    /* Create-or-open in one call — see the module doc comment for why no
     * separate `OpenFileMapping` probe is needed. A second/later attacher
     * gets a handle to the SAME existing section; its own `sz` here is
     * ignored by Windows in that case (the section keeps the size the
     * FIRST creator gave it), matching the POSIX arm's own
     * already-the-same-size `ftruncate` no-op on a second attacher. */
  if (!hMap) {
    PT_DBG("pt_shm_ch_init: CreateFileMappingA(\"%s\") FAILED, GetLastError=%lu\n",
           winName, (unsigned long)GetLastError());
    return -1;
  }
  mem = MapViewOfFile(hMap, FILE_MAP_ALL_ACCESS, 0, 0, sz);
  if (!mem) {
    PT_DBG("pt_shm_ch_init: MapViewOfFile(\"%s\") FAILED, GetLastError=%lu\n",
           winName, (unsigned long)GetLastError());
    CloseHandle(hMap);
    return -1;
  }
  PT_DBG("pt_shm_ch_init: CreateFileMappingA + MapViewOfFile succeeded for \"%s\"\n", winName);
  ch->hMap = hMap;
#else
  int fd = shm_open(name, O_CREAT | O_RDWR, 0600);
  if (fd < 0) return -1;
  if (ftruncate(fd, (off_t)sz) != 0) { close(fd); return -1; }
  mem = mmap(NULL, sz, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  close(fd);
  if (mem == MAP_FAILED) return -1;
#endif
  ch->shdr = (pt_shm_header*)mem;
  ch->sbuf[0] = (uint8_t*)mem + sizeof(pt_shm_header);
  ch->sbuf[1] = ch->sbuf[0] + capacity;
  ch->cap = capacity;
  ch->mapped_size = sz;
  {
    size_t n = strlen(name);
    if (n >= sizeof(ch->attached_name)) n = sizeof(ch->attached_name) - 1;
    memcpy(ch->attached_name, name, n);
    ch->attached_name[n] = 0;
  }
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
    pt_gen_store(&ch->shdr->generation, 0u, 0 /* relaxed */);
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
  *ch->dumped = 0;                                     /* re-arm LAST */
}

static int pt_shm_ch_begin(pt_shm_channel* ch, uint8_t** outPtr, uint32_t* outCapacity) {
  if (!ch->shdr || *ch->dumped) return 0;
  *ch->dumped = 1;
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
  uint32_t g = pt_gen_load(&ch->shdr->generation, 0 /* relaxed */);
  pt_gen_store(&ch->shdr->generation, g + 1, 1 /* release */);
}

static void pt_shm_ch_publish_bytes(pt_shm_channel* ch, const uint8_t* data, uint32_t len) {
  uint8_t* p; uint32_t cap;
  if (!pt_shm_ch_begin(ch, &p, &cap)) {
    PT_DBG("pt_shm_ch_publish_bytes: pt_shm_ch_begin refused (shdr=%s, already dumped this generation=%s) -- len=%u NOT published\n",
           ch->shdr ? "attached" : "NULL/never attached", (ch->shdr && *ch->dumped) ? "yes" : "no", len);
    return;
  }
  uint32_t n = len < cap ? len : cap;
  memcpy(p, data, n);
  pt_shm_ch_commit(ch, len);
  PT_DBG("pt_shm_ch_publish_bytes: published %u bytes (cap=%u) to \"%s\"\n", n, cap, ch->attached_name);
}

static int pt_shm_ch_read(pt_shm_channel* ch, uint8_t* out, uint32_t outCap, uint32_t* outLen) {
  if (!ch->shdr) return 0;
  uint32_t g1 = pt_gen_load(&ch->shdr->generation, 1 /* acquire */);
  if (g1 == 0) { *outLen = 0; return 1; }
  for (int attempt = 0; attempt < 4; attempt++) {
    unsigned int a = ch->shdr->published;               /* plain load; safe — happens-after the acquire above */
    uint32_t len = ch->shdr->buf_len[a];
    uint32_t n = len < outCap ? len : outCap;
    memcpy(out, ch->sbuf[a], n);
    uint32_t g2 = pt_gen_load(&ch->shdr->generation, 1 /* acquire */);
    if (g2 == g1) { *outLen = n; return 1; }             /* stable: no publish raced this copy */
    g1 = g2;                                             /* a publish landed mid-copy: retry against the new generation */
  }
  return 0;
}

/* ---- default channel: the ORIGINAL names, unchanged behavior/ABI --------- */

static pt_shm_channel pt_default_channel = { NULL, { NULL, NULL }, 0, &pt_dumped };

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

static volatile sig_atomic_t pt_cmplog_dumped = 0;
  /* The cmp-log channel's OWN "published at most once this run" gate —
   * deliberately NOT `pt_dumped` (see `pt_shm_channel.dumped`'s doc above)
   * so a coverage publish and a cmp-log publish in the same run never
   * starve each other. */
static pt_shm_channel pt_cmplog_channel = { NULL, { NULL, NULL }, 0, &pt_cmplog_dumped };

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

#ifdef __cplusplus
}  /* extern "C" */
#endif
