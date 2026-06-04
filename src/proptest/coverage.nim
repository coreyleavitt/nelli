## Coverage instrumentation runtime and `{.cover.}` source pragma.
##
## A leaf module — depends on nothing else in proptest. Both the fuzz
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

import std/[macros, hashes]

# --- runtime -----------------------------------------------------------------

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

proc instrumentNode(n: NimNode): NimNode =
  ## Recursive AST rewrite. Branch nodes (`if`, `case`, `while`) get
  ## `recordEdge` injected into each arm; all other nodes are walked
  ## structurally so nested branches deeper in the body are also
  ## instrumented.
  case n.kind
  of nnkIfStmt, nnkIfExpr, nnkWhenStmt:
    result = n.copyNimNode
    for branch in n:
      let edgeId = edgeIdFromLineInfo(branch)
      case branch.kind
      of nnkElifBranch, nnkElifExpr:
        let cond = branch[0]
        let body = instrumentNode(branch[1])
        let wrapped = newStmtList(
          newCall(bindSym"recordEdge", newLit(edgeId)), body)
        result.add nnkElifBranch.newTree(cond, wrapped)
      of nnkElse, nnkElseExpr:
        let body = instrumentNode(branch[0])
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
      let newBranch = branch.copyNimNode
      for j in 0 ..< branch.len - 1:
        newBranch.add branch[j]
      let body = instrumentNode(branch[^1])
      newBranch.add newStmtList(
        newCall(bindSym"recordEdge", newLit(edgeId)), body)
      result.add newBranch
  of nnkWhileStmt:
    let edgeId = edgeIdFromLineInfo(n)
    let cond = n[0]
    let body = instrumentNode(n[1])
    let wrapped = newStmtList(
      newCall(bindSym"recordEdge", newLit(edgeId)), body)
    result = nnkWhileStmt.newTree(cond, wrapped)
  else:
    result = n.copyNimNode
    for child in n:
      result.add instrumentNode(child)

macro cover*(procDef: untyped): untyped =
  ## Pragma macro: rewrite the proc's body so each branch point records
  ## an edge hit. Use as `proc f(x: int) {.cover.} = ...`. The
  ## instrumentation is source-level (Nim's compiler doesn't expose a
  ## sanitizer-coverage hook); each `if` / `case` / `while` branch gets
  ## a unique ID derived from its source location.
  expectKind procDef, {nnkProcDef, nnkFuncDef, nnkLambda}
  result = procDef
  result[^1] = instrumentNode(procDef[^1])

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
