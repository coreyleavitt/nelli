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
