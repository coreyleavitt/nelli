## RFC-fuzzer-nextgen E4c: Job Object memory limits on the Windows persistent-
## worker tier — `fuzzworker.nim`'s `spawnWorkerProcess`/`reapWorkerWithLimits`
## consuming `workerproto.JobLimitPolicy`/`verdictForJobLimit` (E4a C1,
## already unit-tested in `tests/tfuzzworkerproto.nim` over synthetic
## values) through a REAL `CreateJobObject`/`SetInformationJobObject`/
## `GetQueuedCompletionStatus` round-trip, driven through the real `fuzz(...)`
## macro call site the way an actual campaign would.
##
## Windows-only (Job Objects have no POSIX equivalent; the persistent-worker
## tier has never had `ResourceLimits` wired in on POSIX either — out of
## scope for this slice, see `fuzzworker.nim`'s POSIX `spawnWorkerProcess`,
## unchanged). Build-checked only on this (Linux) dev host via
## `dt-crosswin.sh` — no local Windows RUN channel exists
## (`docs/RFC-fuzzer-nextgen.windows-capability.md`); RUN-verified via the
## `fuzzer-windows` CI leg this glob (`tfuzz*`) is discovered by.
##
## One call site only (see `tests/tfuzzworkerprocess.nim`'s module doc for
## the full discriminating argument against a second one in the same binary).
##
## Discriminator shape: a magic INPUT VALUE (`joblimitMagic`), exactly
## mirroring `tests/tfuzzwinworker.nim`'s `sentinelProp` (`if n == -13:
## quit(7)`) — chosen over branching on `nelliWorkerModeId` directly, since
## a construction closure the SAME parser below also traces sees it either
## way; the value-discriminator keeps this property's SHAPE as close as
## possible to `sentinelProp`'s already-proven-compiling one. The front
## door's own in-process run (`FuzzSettings(seed: 1, maxIterations: 1)`)
## draws SOME `n` in `joblimitStrategy`'s wide range; landing on the exact
## magic value by chance is astronomically unlikely (and even if it did, a
## one-time 512 MiB allocation in the unconstrained front-door process is
## survivable, not a correctness issue — `sentinelProp`'s own `n == -13`
## discriminator carries the identical, already-accepted risk profile).
##
## Allocation mechanism: raw C `malloc`/`memset`/`free` (`cMalloc`/`cMemset`/
## `cFree`, declared `importc` with NO Nim body), NOT `system.newSeq[byte]`
## or `system.alloc0`. Both were tried first and BOTH broke the compile-time
## concolic-bridge DSL parser every `fuzz(...)` call site also compiles
## through (`smt/dsl_typebridge.nim`): `newSeq[byte](n)` inside a `{.cover.}`
## property hit "node has no type" in `classifyType` (a generic,
## GC-integrated instantiation the parser's callee-walk — `ensureProcRegistered`/
## `parseCalleeImpl` — could not classify); `alloc0` hit a DIFFERENT gap,
## walking the allocator's own internal `when`-branched record type
## ("Expected a node of kind nnkIdentDefs, got nnkRecWhen"). Neither failure
## is Windows-specific — no existing `{.cover.}` property in this codebase
## had ever called `newSeq`/`alloc0` before, POSIX included, so this is a
## previously-latent parser gap this slice's local `dt-crosswin.sh` checking
## surfaced for the first time, not a regression. A leaf `importc` proc (no
## Nim-visible body to recurse into) sidesteps both — the same shape
## `quit()` already has in `sentinelProp`. `tests/tfuzzwinshm.nim`'s module
## doc documents the same family of parser gaps and the same fix: reshape
## the property around a proven-compiling pattern rather than fight the
## parser.
##
## Threshold choice: `joblimitBytes` (32 MiB) must comfortably exceed an
## ordinary `nelli` test binary's OWN baseline committed memory at worker-loop
## entry (this binary links the full `nelli` surface, including the
## symex/Z3 FFI layer other suites in this repo exercise — but Z3 itself is
## loaded via `softlink`/`dlopen`, not linked eagerly, and this property never
## calls into it) — a worker that dies before ever reaching `joblimitProp`'s
## deliberate over-allocation would still report `vResourceExceeded`, but
## would NOT be proof that a fuzzed input's OWN behavior (not just process
## startup) is what the Job Object caught; `joblimitOverAllocBytes` (512 MiB)
## is chosen to be unambiguously, overwhelmingly larger than any plausible
## startup footprint, so the two thresholds cannot be confused. If a real
## Windows CI run shows this baseline assumption wrong (the RFC's own
## push-and-wait discipline), the fix is raising `joblimitBytes`, not
## abandoning the mechanism.

import std/[unittest, options, strutils]
import nelli
import nelli/[datasource, rng, serialize]

disableParamFiltering()

when defined(windows):
  const joblimitBytes = 32 * 1024 * 1024
    ## The Job Object's `ProcessMemoryLimit` this test's spawn installs.
  const joblimitOverAllocBytes = 512 * 1024 * 1024
    ## Deliberately, unambiguously larger than `joblimitBytes` (see module
    ## doc) — `joblimitProp` `malloc`s AND `memset`s this many bytes, so the
    ## memory is genuinely COMMITTED (touched), not just reserved, before the
    ## Job Object's `ProcessMemoryLimit` is checked against it.
  const joblimitMagic = 999_999
    ## The discriminator value — see module doc for why an input VALUE, not
    ## `nelliWorkerModeId`, gates the over-allocation.

  proc joblimitStrategy(): Strategy[int] = integers(0, 1_000_000)

  # Raw C-level `malloc`/`memset`/`free`, declared as opaque `importc` leaves
  # with NO Nim-visible body — deliberately NOT `system.newSeq`/`system.alloc0`
  # (both tried first; both broke the compile-time concolic-bridge DSL parser
  # every `fuzz(...)` call site also compiles through: `newSeq[T]`'s generic
  # GC-integrated instantiation hit "node has no type" in `classifyType`;
  # `alloc0` hit a DIFFERENT parser gap walking the allocator's own internal
  # `when`-branched record type, "Expected a node of kind nnkIdentDefs, got
  # nnkRecWhen". An `importc` proc with no Nim body gives the parser NOTHING
  # to recurse into — the same leaf-call shape `quit()` already has in
  # `tests/tfuzzwinworker.nim`'s proven-compiling `sentinelProp`).
  proc cMalloc(size: csize_t): pointer {.importc: "malloc", header: "<stdlib.h>".}
  proc cMemset(p: pointer; value: cint; size: csize_t) {.importc: "memset", header: "<string.h>".}
  proc cFree(p: pointer) {.importc: "free", header: "<stdlib.h>".}

  proc joblimitProp(n: int) {.cover.} =
    if n == joblimitMagic:
      let p = cMalloc(csize_t(joblimitOverAllocBytes))
      cMemset(p, 1.cint, csize_t(joblimitOverAllocBytes))   # force the commit, not just a reservation
      cFree(p)
    doAssert n != joblimitMagic,
      "unreachable: the Job Object memory limit should kill this process before this line"

  proc drawUntil(lo, hi: int; seedBase: uint64; pred: proc(n: int): bool): tuple[val: int, choices: ChoiceSeq] =
    ## Draw a value matching `pred` through the REAL `integers(lo, hi)`
    ## strategy (never hand-build a `ChoiceNode` — replay must stay
    ## strategy-valid). Identical to `tests/tfuzzwinworker.nim`'s own helper.
    for attempt in 0'u64 ..< 10_000'u64:
      var ds = newDataSource(initSplitMix64(seedBase + attempt))
      let v = integers(lo, hi).generate(ds)
      if pred(v): return (v, ds.recorded)
    doAssert false, "could not draw a value matching the predicate"

  suite "fuzz: Windows Job Object memory limit (RFC-fuzzer-nextgen E4c)":
    test "a worker that over-allocates past its Job Object memory limit is vResourceExceeded, not a hang or an ordinary crash":
      discard fuzz(joblimitStrategy(), joblimitProp, FuzzSettings(maxIterations: 1, seed: 1))
      let id = nelliLastFuzzCallSiteId
      check id.len > 0

      let (_, choices) = drawUntil(0, 1_000_000, 0xC0FFEE'u64, proc(n: int): bool = n == joblimitMagic)

      var frontier = newCoverageFrontier()
      let worker = newProcessWorker[int](id, ResourceLimits(addressSpaceBytes: joblimitBytes))
      let orch = newOrchestrator(worker, frontier)
      let obs = orch.run(choices)

      check obs.verdict == vResourceExceeded
      check obs.crash.isSome
      check obs.crash.get.kind == ckWinException
      check obs.crash.get.code == uint32(ord(jlkMemory))
      check "memory" in obs.crash.get.message
else:
  echo "SKIP (windows-only; Job Objects have no POSIX equivalent — see fuzzworker.nim's POSIX spawnWorkerProcess, unchanged): Job Object memory limit suite"
