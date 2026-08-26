## Coverage instrumentation runtime and `{.cover.}` source pragma.
##
## A leaf module — depends on nothing else in nelli. Both the fuzz
## runner (`fuzz.nim`) and, when `Settings.coverageGuided` is on, the
## PBT engine (`engine.nim`) consume it. Splitting it out is what makes
## #107 coverage-as-PBT-target buildable without a fuzz↔engine cycle.
##
## **Runtime gate (#106).** `recordEdge` is a no-op until the caller sets
## `setCoverageMode(cmRecording)`. The default is `cmOff` so a
## `{.cover.}`'d proc costs nothing for callers who haven't opted in.
## Both runners flip the mode on entry and restore it on exit so the
## recording state is scoped to a session.
##
## **Bitmap semantics.** AFL-style fixed-size bitmap (8192 slots) keyed
## by `(file, line, column)` hash of each branch. Collisions are
## tolerated; only the *first* hit of an edge updates the cached count
## so re-hits in tight loops don't inflate the score. Per-thread.
##
## **Why 8192, and how it converges (#C2).** The slot count is a fixed
## power of two so slot selection is a single `and coverageEdgeMask`
## (no modulo), the map is one contiguous cache-friendly 8 KiB array,
## and no global edge counter or registration pass is needed — an edge's
## slot is a pure function of its source hash. The cost of a fixed map is
## *convergence under collision*: distinct edges alias onto shared slots
## as the branch count grows. Inserting `E` distinct edges into `M = 8192`
## slots occupies, in expectation, `M·(1 − e^(−E/M))` of them — so the
## observed coverage is collision-free only while `E ≪ √M ≈ 90`, is
## already ~5% aliased by `E ≈ M/2`, and *converges* toward `M` (new edges
## almost never raise a fresh slot) as `E` approaches and passes `M`.
## Two consequences follow: `currentCoverage()` is a monotone *lower*
## bound on the true distinct-edge count, and two colliding edges are
## indistinguishable to the frontier. This is deliberately a non-issue at
## nelli's scale — a single SUT under test has far fewer than 8192
## branch points, keeping every real target in the collision-sparse
## regime — and the AFL literature confirms a few-K-slot map suffices
## until a program has tens of thousands of edges.
##
## **The real lever is C1, not a bigger map.** Growing `coverageEdgeCount`
## only pushes the asymptote out; it does not make collisions *visible*.
## The slot→`file:line:col` side-table (`registerEdgeSource` /
## `edgeSources` / `uncoveredSources`, below) does: a slot that carries
## more than one location in `edgeSources` *is* a collision you can now
## see and name, and `uncoveredSources` turns unhit slots into concrete
## source lines. So the response to a target that outgrows 8192 is to
## consult the side-table (and, if truly needed, bump this power-of-two
## count — the hashing and mask adapt automatically), never to silently
## live with an aliased signal.

import std/[macros, hashes, tables, sets]

# --- runtime -----------------------------------------------------------------

# `coverageEdgeCount` is fixed and a power of two on purpose — see the
# "Why 8192, and how it converges (#C2)" note in the module header for the
# occupancy/convergence analysis and why C1's side-table, not a larger map,
# is the lever when collisions start to matter.
const coverageEdgeCount* = 8192
const coverageEdgeMask = coverageEdgeCount - 1

var coverageBitmap {.threadvar.}: array[coverageEdgeCount, uint8]
var coverageHitsCached {.threadvar.}: int

type CoverageMode* = enum
  ## Runtime gate on the coverage bitmap. Default is `cmOff` so a
  ## `{.cover.}`'d proc imposes zero runtime cost on callers who haven't
  ## opted in. The fuzz runner and (when `Settings.coverageGuided` is on,
  ## per #107) the PBT engine flip to `cmRecording` for the duration of
  ## their session, then restore the prior mode.
  cmOff,
  cmRecording

var coverageMode {.threadvar.}: CoverageMode  # zero-init = cmOff

proc setCoverageMode*(mode: CoverageMode) =
  ## Set the per-thread coverage recording mode. See `CoverageMode`.
  coverageMode = mode

proc currentCoverageMode*(): CoverageMode =
  ## Current per-thread coverage mode.
  coverageMode

proc resetCoverage*() =
  ## Zero the per-thread coverage bitmap and hit count. The fuzz runner
  ## calls this before each session; the PBT engine calls it before each
  ## coverage-guided run so growth measures *that run's* contribution.
  for i in 0 ..< coverageEdgeCount:
    coverageBitmap[i] = 0
  coverageHitsCached = 0

proc recordEdge*(id: int) {.inline.} =
  ## Mark edge `id` as hit. `id mod coverageEdgeCount` is the bitmap
  ## slot; collisions are tolerated (AFL convention). Only the first
  ## hit of an edge updates the count, so re-hits in a tight loop
  ## don't inflate the score.
  ##
  ## Gated on `coverageMode`: returns immediately when the mode is
  ## `cmOff` so consumers of `{.cover.}`'d code pay nothing unless
  ## they've opted into recording via `setCoverageMode(cmRecording)`.
  if coverageMode == cmOff: return
  let slot = id and coverageEdgeMask
  if coverageBitmap[slot] == 0:
    coverageBitmap[slot] = 1
    inc coverageHitsCached

proc currentCoverage*(): int =
  ## Number of distinct edges hit since the last `resetCoverage`.
  ## O(1) — we maintain a running cached count.
  coverageHitsCached

# --- edge source-location side-table (#C1) -----------------------------------
#
# `{.cover.}` expansion hashes each branch's `(file, line, column)` into a
# bitmap slot and then discards the location. That makes an unhit slot
# unreportable in source terms. This table is the other half: slot -> the
# source location(s) that hash to it, populated once at module init (see the
# `cover` macro below) so a coverage-gap report can name real source lines.
#
# Module-global, NOT threadvar: this mirrors static program structure (which
# source locations exist and what they hash to), identical across threads —
# unlike `coverageBitmap`, which records *hits* and is genuinely per-thread.
#
# Values are `OrderedSet[string]` because bitmap collisions are real and
# expected (8192 slots, AFL convention): multiple distinct source locations
# can legitimately share a slot. `OrderedSet` dedups idempotent re-registration
# and keeps first-seen order for deterministic reports.
#
# Single-threaded by contract, like the rest of this module's mutable state:
# no lock guards this table, and none is added — coverage recording assumes
# one thread drives instrumentation/eval at a time, so a lock would be dead
# weight against a race that the module's calling contract already rules out.
#
# `registerEdgeSource` re-runs on every evaluation of an already-instrumented
# `{.cover.}` proc (the registration calls are emitted as top-level siblings
# of the proc, so they fire each time that definition executes — see `cover`
# below). That's intentionally cheap to leave alone: the `OrderedSet` value
# makes repeat `(slot, loc)` registration a no-op set-merge, so the redundant
# calls cost an idempotent insert, not unbounded growth or corruption.
var edgeSourceTable: Table[int, OrderedSet[string]]

proc registerEdgeSource*(slot: int; loc: string) =
  ## Record that source location `loc` (a `"file:line:col"` string) hashes to
  ## bitmap `slot`. Idempotent: re-registering the same `(slot, loc)` pair
  ## (e.g. a proc definition re-executed, or a module re-imported) is a no-op
  ## beyond the first time — see `edgeSourceTable` above. Called from
  ## `{.cover.}`-expanded code, not normally by hand.
  ##
  ## Internal — not part of the caller-facing API; callers want
  ## `uncoveredSources()` instead. It is exported for direct test
  ## introspection (`tests/tcovsourcetable.nim` calls it to register
  ## synthetic locations and exercise slot-collision behavior), NOT because
  ## the `cover` macro needs it exported: the macro's generated calls
  ## resolve this proc via `bindSym`, which binds to the module-local symbol
  ## regardless of its export marker, since `cover` is itself defined in
  ## this module.
  let s = slot and coverageEdgeMask
  edgeSourceTable.withValue(s, locs):
    locs[].incl loc
  do:
    edgeSourceTable[s] = toOrderedSet([loc])

proc edgeSources*(slot: int): seq[string] =
  ## Source locations registered against `slot`, in first-registered order.
  ## Empty if nothing has been registered for `slot` (e.g. no `{.cover.}`'d
  ## code hashes there).
  ##
  ## Internal — a low-level accessor onto `edgeSourceTable`; not intended for
  ## ordinary caller use. Callers want `uncoveredSources()` instead. Exported
  ## solely for direct test introspection (`tests/tcovsourcetable.nim` reads
  ## it to assert exactly what got registered per slot, including
  ## deliberately forced collisions).
  let s = slot and coverageEdgeMask
  if edgeSourceTable.hasKey(s):
    for loc in edgeSourceTable[s]:
      result.add loc

proc uncoveredSources*(): seq[string] =
  ## Source-mapped coverage-gap report: the locations of every REGISTERED
  ## slot whose current bitmap byte is 0 (unhit), in ascending slot order.
  ##
  ## Collision honesty: a slot with N colliding locations is reported here
  ## iff ALL N are jointly unhit — hitting any one of them marks the whole
  ## slot covered, so this can under-report (miss a location that happens to
  ## share a slot with one that *was* hit). That's inherent to the fixed
  ## 8192-slot bitmap, not a bug; C1 does not attempt to disambiguate
  ## collisions.
  for slot in 0 ..< coverageEdgeCount:
    if coverageBitmap[slot] == 0 and edgeSourceTable.hasKey(slot):
      for loc in edgeSourceTable[slot]:
        result.add loc

# --- {.cover.} pragma --------------------------------------------------------
#
# Walks a proc's body AST and injects `recordEdge(id)` at the start of
# every branch arm (the `then` and `else` of an `if`, every arm of a
# `case`, the body of a `while`). Edge IDs are the source location hash
# (file + line + column) modulo `coverageEdgeCount`, so they're stable
# across runs and don't require a global counter — but collisions are
# tolerated per the AFL convention.

proc edgeIdFromLineInfo(n: NimNode): int =
  let li = n.lineInfoObj
  let h = hash(li.filename) !& hash(li.line) !& hash(li.column)
  abs(!$h) and (coverageEdgeCount - 1)

proc edgeLocFromLineInfo(n: NimNode): string =
  ## `"file:line:col"` for `n` — built from the SAME `lineInfoObj` that
  ## `edgeIdFromLineInfo` hashes, so a branch's registered location always
  ## matches the slot its edge ID lands on.
  let li = n.lineInfoObj
  li.filename & ":" & $li.line & ":" & $li.column

proc queueRegistration(n: NimNode; edgeId: int; regs: var seq[NimNode]) =
  ## Queue a `registerEdgeSource(edgeId, loc)` call (emitted by the `cover`
  ## macro as a sibling of the instrumented proc/lambda, so it runs once at
  ## definition time — see `cover` below) recording `n`'s source location
  ## against `edgeId`.
  regs.add newCall(bindSym"registerEdgeSource", newLit(edgeId),
                    newLit(edgeLocFromLineInfo(n)))

proc instrumentNode(n: NimNode; regs: var seq[NimNode]): NimNode =
  ## Recursive AST rewrite. Branch nodes (`if`, `case`, `while`) get
  ## `recordEdge` injected into each arm; all other nodes are walked
  ## structurally so nested branches deeper in the body are also
  ## instrumented. Each branch's edge ID and source location are also
  ## queued into `regs` for the `cover` macro to emit as
  ## `registerEdgeSource` calls (#C1).
  case n.kind
  of nnkIfStmt, nnkIfExpr, nnkWhenStmt:
    result = n.copyNimNode
    for branch in n:
      let edgeId = edgeIdFromLineInfo(branch)
      case branch.kind
      of nnkElifBranch, nnkElifExpr:
        queueRegistration(branch, edgeId, regs)
        let cond = branch[0]
        let body = instrumentNode(branch[1], regs)
        let wrapped = newStmtList(
          newCall(bindSym"recordEdge", newLit(edgeId)), body)
        result.add nnkElifBranch.newTree(cond, wrapped)
      of nnkElse, nnkElseExpr:
        queueRegistration(branch, edgeId, regs)
        let body = instrumentNode(branch[0], regs)
        let wrapped = newStmtList(
          newCall(bindSym"recordEdge", newLit(edgeId)), body)
        result.add nnkElse.newTree(wrapped)
      else:
        result.add branch  # unexpected; preserve verbatim
  of nnkCaseStmt:
    result = n.copyNimNode
    result.add n[0]  # selector
    for i in 1 ..< n.len:
      let branch = n[i]
      let edgeId = edgeIdFromLineInfo(branch)
      queueRegistration(branch, edgeId, regs)
      let newBranch = branch.copyNimNode
      for j in 0 ..< branch.len - 1:
        newBranch.add branch[j]
      let body = instrumentNode(branch[^1], regs)
      newBranch.add newStmtList(
        newCall(bindSym"recordEdge", newLit(edgeId)), body)
      result.add newBranch
  of nnkWhileStmt:
    let edgeId = edgeIdFromLineInfo(n)
    queueRegistration(n, edgeId, regs)
    let cond = n[0]
    let body = instrumentNode(n[1], regs)
    let wrapped = newStmtList(
      newCall(bindSym"recordEdge", newLit(edgeId)), body)
    result = nnkWhileStmt.newTree(cond, wrapped)
  else:
    result = n.copyNimNode
    for child in n:
      result.add instrumentNode(child, regs)

macro cover*(procDef: untyped): untyped =
  ## Pragma macro: rewrite the proc's body so each branch point records an
  ## edge hit, and emit a `registerEdgeSource` call per branch so the edge's
  ## bitmap slot maps back to its `file:line:col` (#C1). Use as
  ## `proc f(x: int) {.cover.} = ...`. The instrumentation is source-level
  ## (Nim's compiler doesn't expose a sanitizer-coverage hook); each `if` /
  ## `case` / `while` branch gets a unique ID derived from its source
  ## location.
  ##
  ## For a `proc`/`func`, the registration calls are emitted as top-level
  ## statements alongside the (unchanged) proc definition, so they run once
  ## wherever that definition executes (module init, for the common
  ## top-level case). A `lambda` is an expression, not a statement, so
  ## there's no statement list to append to: the registrations and the
  ## lambda are instead wrapped in a `block`-like expression
  ## (`nnkStmtListExpr`) that runs the registrations and evaluates to the
  ## lambda value.
  expectKind procDef, {nnkProcDef, nnkFuncDef, nnkLambda}
  var regs: seq[NimNode] = @[]
  procDef[^1] = instrumentNode(procDef[^1], regs)
  if regs.len == 0:
    result = procDef
  elif procDef.kind == nnkLambda:
    result = nnkStmtListExpr.newTree(regs & @[procDef])
  else:
    result = newStmtList(@[procDef] & regs)

# --- external-target coverage: value + frontier (FUZZ_PLAN D6/D9) ------------
#
# A backend-agnostic layer over a run's coverage map (clang per-edge counters or
# the gcc PC-hash bitmap — both arrive as a byte-per-slot array via the dump
# runtime). The frontier accumulates the campaign's coverage and answers the one
# question the fuzz loop asks per input: "did this raise a new edge bucket?"

type
  Coverage* = object
    ## One run's observation — a byte per slot (counter, or 0/1 for the in-process
    ## bitmap). Value type, no history. Read by a `CoverageProbe` (D9).
    counters*: seq[uint8]

func bucketOf*(count: uint8): uint8 =
  ## AFL 8-bucket classifier (D6). INVARIANT: `bucketOf(0) == 0` is the unique
  ## "unseen" bucket and `bucketOf(n) >= 1` for any `n >= 1` — any execution at all
  ## outranks unseen, or first-execution edges would never be admitted. Bucketing
  ## (vs raw counts) is what makes "100 vs 128 iterations" not look like new coverage.
  if count == 0: 0'u8
  elif count == 1: 1'u8
  elif count == 2: 2'u8
  elif count == 3: 3'u8
  elif count <= 7: 4'u8
  elif count <= 15: 5'u8
  elif count <= 31: 6'u8
  elif count <= 127: 7'u8
  else: 8'u8

type
  Admission* = object
    ## Result of folding one `Coverage` into the frontier (D9): the decision plus the
    ## numbers the report and the power schedule consume, in one return.
    interesting*: bool   ## raised at least one slot's bucket → keep the input
    newEdges*: int       ## slots whose bucket this run raised
    globalEdges*: int    ## frontier population (distinct slots ever seen) after folding

  CoverageFrontier* = object
    ## The accumulated bucket map for one campaign/target. `accum[i]` is the highest
    ## bucket ever seen for slot `i` (0 = unseen). `targetId` (D12) keys persistence;
    ## a map of a different size than `accum` is a different target/backend.
    targetId*: string
    accum: seq[uint8]

proc newCoverageFrontier*(targetId = ""): CoverageFrontier =
  CoverageFrontier(targetId: targetId, accum: @[])

proc coveredEdges*(f: CoverageFrontier): int =
  ## Distinct slots ever observed (bucket > 0) — the frontier population.
  for b in f.accum:
    if b > 0'u8: inc result

proc totalEdges*(f: CoverageFrontier): int =
  ## Total slots in the map (the target's edge/bitmap size).
  f.accum.len

proc admit*(f: var CoverageFrontier; c: Coverage): Admission =
  ## Fold `c` into the frontier. An edge is NEW iff its bucket THIS run exceeds the
  ## stored bucket — order-independent (D6): re-observing a slot at a lower count
  ## never lowers its stored bucket and never flips admission. Grows the map if a
  ## later observation has more slots (a newly-loaded module).
  if f.accum.len < c.counters.len:
    f.accum.setLen(c.counters.len)
  for i in 0 ..< c.counters.len:
    let b = bucketOf(c.counters[i])
    if b > f.accum[i]:
      f.accum[i] = b
      inc result.newEdges
  result.interesting = result.newEdges > 0
  result.globalEdges = f.coveredEdges

proc score*(f: CoverageFrontier; c: Coverage): int =
  ## RFC-fuzzer-nextgen E3a (C2) / Appendix C: a NON-MUTATING peek at how many
  ## of `c`'s slots would raise `f`'s stored bucket if folded via `admit` — `>
  ## 0` mirrors `Admission.interesting` without ever touching `f`. This is
  ## what lets a caller (the Orchestrator's re-verify pre-filter) cheaply ask
  ## "does this candidate look worth a fresh spawn?" against a candidate's
  ## own (possibly contaminated) coverage without ever recording it into the
  ## frontier — only a fresh, authoritative re-observation is ever admitted.
  for i in 0 ..< c.counters.len:
    let stored = if i < f.accum.len: f.accum[i] else: 0'u8
    if bucketOf(c.counters[i]) > stored: inc result

# --- coverage probe (FUZZ_PLAN D9) ------------------------------------------

type
  CoverageProbe* = object
    ## Reads the map a just-finished run produced — the only execution-mode-
    ## polymorphic surface (D9). `resetsPerRun`: true if the underlying map is
    ## cumulative and the harness must clear it before each run (the in-process
    ## bitmap, D8); false if each `read()` is a self-contained absolute snapshot
    ## (an external fresh-exec dump).
    read*: proc(): Coverage {.closure.}
    resetsPerRun*: bool

proc snapshotCoverage*(): Coverage =
  ## The current in-process {.cover.} bitmap as a `Coverage` value (one byte per
  ## edge slot, 0/1). Pairs with `resetCoverage` for per-run isolation.
  result.counters = newSeq[uint8](coverageEdgeCount)
  for i in 0 ..< coverageEdgeCount:
    result.counters[i] = coverageBitmap[i]

proc inProcessProbe*(): CoverageProbe =
  ## A `CoverageProbe` over the in-process {.cover.} bitmap. `resetsPerRun = true`:
  ## the bitmap is session-cumulative, so the harness (inProcessTarget, Phase 4)
  ## clears it before each run; `read()` snapshots the post-run bitmap.
  CoverageProbe(read: snapshotCoverage, resetsPerRun: true)

# --- shm coverage probe (RFC-fuzzer-nextgen E2b) -----------------------------
#
# The third `CoverageProbe` impl, and the first whose producer (a persistent
# worker process) can genuinely be mid-write at `read()` time from the
# READER's (the orchestrator's) point of view — `inProcessProbe` is
# same-address-space, `sancovFileProbe` reads only after `waitpid` (the child
# is already dead). See `nelli_shm.c`'s module doc for the full push/copy +
# atomic-generation-word protocol this wraps; that file is compiled in here
# WITHOUT `nelli_cov.c` (deliberately — see its header) so this never installs
# nelli_cov.c's process-wide signal handlers into a caller's binary.
#
# `resetsPerRun = false`: like `sancovFileProbe`, each `read()` is already a
# complete, independent per-run snapshot by the time the orchestrator asks
# for it. The reset/publish cycle is entirely WORKER-internal
# (`shmResetCoverage`/`shmPublishCoverage`, called by `fuzzworker.nim`'s
# worker loop before/after each input, unprompted by the orchestrator) —
# `CoverageProbe.resetsPerRun` stays a pure capability flag; there is no
# orchestrator-triggered reset verb. This is safe under the
# read-before-redispatch invariant: an `Orchestrator`'s `probe.read()` for
# input K always completes (the process `Worker[T]`'s `submit` blocks for the
# worker's result frame) before the SAME worker is ever dispatched input
# K+1 — true under the synchronous request-response pipe seam.
when defined(posix):
  {.compile: "nelli_shm.c".}

  proc ptShmInit(name: cstring; capacity: uint32): cint {.importc: "pt_shm_init".}
  proc ptShmResetBuffer() {.importc: "pt_shm_reset_buffer".}
  proc ptShmPublishBytes(data: ptr uint8; len: uint32) {.importc: "pt_shm_publish_bytes".}
  proc ptShmRead(outp: ptr uint8; outCap: uint32; outLen: ptr uint32): cint {.importc: "pt_shm_read".}

  proc shmResetCoverage*(shmName: string) =
    ## WORKER-side per-input reset (called BEFORE running an input): zero
    ## the Nim `{.cover.}` bitmap (`resetCoverage`, the existing per-run
    ## isolation primitive `inProcessProbe` also relies on) AND the shm
    ## staging buffer (`pt_shm_reset_buffer`), re-arming the shm publish
    ## gate. Attaches (idempotent) to `shmName`, sized to `coverageEdgeCount`
    ## — a FIXED capacity, chosen once by the orchestrator; dlopen is a
    ## non-issue for this producer (the Nim bitmap is not dynamically-
    ## registered sancov state, unlike an external C target's counters —
    ## see nelli_shm.c's dlopen note).
    discard ptShmInit(shmName.cstring, uint32(coverageEdgeCount))
    resetCoverage()
    ptShmResetBuffer()

  proc shmPublishCoverage*(shmName: string; cov: Coverage) =
    ## WORKER-side per-input publish (called AFTER running an input, with
    ## the SAME `Coverage` value `observeInProcess` already computed for
    ## this run via `inProcessProbe`/`snapshotCoverage` — no re-snapshot,
    ## no second source of truth). A no-op if `cov` is somehow empty (never
    ## the case for a real `{.cover.}` bitmap snapshot, which is always
    ## exactly `coverageEdgeCount` bytes; defensive only).
    if cov.counters.len == 0: return
    discard ptShmInit(shmName.cstring, uint32(coverageEdgeCount))
    var counters = cov.counters
    ptShmPublishBytes(addr counters[0], uint32(counters.len))

  proc shmReadCoverage(shmName: string): Coverage =
    discard ptShmInit(shmName.cstring, uint32(coverageEdgeCount))
    result.counters = newSeq[uint8](coverageEdgeCount)
    var outLen: uint32 = 0
    let ok = ptShmRead(addr result.counters[0], uint32(coverageEdgeCount), addr outLen)
    if ok == 0 or outLen == 0: result.counters = @[]
    elif int(outLen) < coverageEdgeCount: result.counters.setLen(int(outLen))

  proc shmProbe*(shmName: string): CoverageProbe =
    ## A `CoverageProbe` reading a persistent worker's shm-published
    ## coverage. `read()` attaches (idempotent) and asks `pt_shm_read` for
    ## the currently-published snapshot; the acquire-before-trust generation
    ## check lives there. An UNPUBLISHED region (a worker that has not yet
    ## completed its first input) reads as empty coverage — absent, never
    ## stale, matching `sancovFileProbe`'s D7 discipline.
    CoverageProbe(
      read: proc(): Coverage = shmReadCoverage(shmName),
      resetsPerRun: false)
