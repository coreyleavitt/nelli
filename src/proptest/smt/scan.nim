## Phase 12 cycle 4 — IR scan helpers for auto-discovery.
##
## Layer 1 of `symexFindAllWitnesses` walks the SUT's IR at macro
## time to figure out which symex targets are even applicable. The
## four target-relevant IR primitives:
##
##   * `isTargetLabel` ← every `symexTarget("name")` opt-in
##   * `isAssert`      ← every `symexAssert(cond)` opt-in
##   * `isIndex`       ← every `arr[i]` / `s[i]` / `t[k]` access
##   * `isVariantField`← every variant arm-field read
##
## Each scanner walks the SUT's body AND descends into callee
## bodies via `procs[calleeName].body` when encountering `isCall`.
## Bounded by what `parseProc` actually placed in the `procs`
## table — cross-module private helpers and other unsupported
## callees stop the descent (no IR available).
##
## Visited-set guards termination under mutual recursion: each
## callee body is scanned at most once per top-level call.

import std/[tables, sets]
import ./types

# ---- Expression descent ----------------------------------------------------
#
# Targets live in statements (`isTargetLabel`, `isAssert`,
# `isIndex`, `isVariantField`), but a call expression nested in an
# expression-position (`if foo(): …`) reaches a callee body too.
# The current parser A-normalises calls into `isCall` statements,
# so expression-level scanning is unnecessary for the four target
# predicates here. Should the parser ever emit an `isCall` nested
# in an expression we'd revisit; for now the per-stmt scan is
# complete.

# ---- Forward decl for mutual recursion -------------------------------------

proc scanStmt(s: IRStmt, procs: Table[string, ProcSig],
              visited: var HashSet[string],
              found: var (bool, bool, bool),
              labels: var seq[string])

proc scanCall(callee: string, procs: Table[string, ProcSig],
              visited: var HashSet[string],
              found: var (bool, bool, bool),
              labels: var seq[string]) =
  if callee in visited: return        # cycle break
  if callee notin procs: return       # cross-module private — boundary
  visited.incl callee
  scanStmt(procs[callee].body, procs, visited, found, labels)

proc scanStmt(s: IRStmt, procs: Table[string, ProcSig],
              visited: var HashSet[string],
              found: var (bool, bool, bool),
              labels: var seq[string]) =
  if s.isNil: return
  case s.kind
  of isBlock:
    for c in s.stmts: scanStmt(c, procs, visited, found, labels)
  of isIf:
    for br in s.branches: scanStmt(br.body, procs, visited, found, labels)
    if s.elseBody != nil:
      scanStmt(s.elseBody, procs, visited, found, labels)
  of isWhile:
    scanStmt(s.wbody, procs, visited, found, labels)
  of isTry:
    scanStmt(s.tryBody, procs, visited, found, labels)
    for h in s.tryHandlers:
      scanStmt(h.body, procs, visited, found, labels)
    if s.tryFinally != nil:
      scanStmt(s.tryFinally, procs, visited, found, labels)
  of isBreak, isContinue, isReturn, isLet, isAssign,
     isTargetLabel, isRaise, isUnsupported, isVariantReassign,
     isVariantReassignSymbolic, isDeref, isNew, isDerefWrite, isUnsafeCast:
    discard  # leaves; check below (isDeref/isNew: Phase 15 R1a — no recursion;
             # the walker stubs them with heUnresolvedRef; isDerefWrite: Phase 15
             # R3 — no recursion, walker no-ops the stub at R3)
  of isCall:
    scanCall(s.callee, procs, visited, found, labels)
  of isAssert, isIndex, isVariantField:
    discard  # flagged below
  # Mark predicates AFTER recursing so a single-stmt body still
  # registers (e.g. a body that IS one `isAssert`).
  case s.kind
  of isAssert:       found[0] = true
  of isIndex:        found[1] = true
  of isVariantField: found[2] = true
  of isTargetLabel:  labels.add s.tname
  else: discard

# ---- Public scan ----------------------------------------------------------

proc scanAll(body: IRStmt, procs: Table[string, ProcSig]
            ): tuple[hasAssert, hasIndex, hasVariantField: bool,
                    labels: seq[string]] =
  ## One-shot scan: returns all four signals from a single
  ## traversal. The four individual helpers below call this and
  ## return the relevant slice.
  var visited: HashSet[string]
  var found: (bool, bool, bool)
  var labels: seq[string]
  scanStmt(body, procs, visited, found, labels)
  (found[0], found[1], found[2], labels)

proc irHasAssert*(body: IRStmt,
                  procs: Table[string, ProcSig]): bool =
  scanAll(body, procs).hasAssert

proc irHasIndex*(body: IRStmt,
                 procs: Table[string, ProcSig]): bool =
  scanAll(body, procs).hasIndex

proc irHasVariantField*(body: IRStmt,
                        procs: Table[string, ProcSig]): bool =
  scanAll(body, procs).hasVariantField

proc scanAssertDefect(s: IRStmt, procs: Table[string, ProcSig],
                      visited: var HashSet[string], found: var bool) =
  ## Phase 15 E6. Detect the implicit `AssertionDefect` raise that a raw
  ## `assert cond, msg` lowers to (parser-emitted `isRaise` with
  ## `raiseTypeId == "AssertionDefect"`), so auto-discovery can add a
  ## `tRaisedExn("AssertionDefect")` target. (The `symexAssert(...)` MARKER
  ## still lowers to `isAssert` and is discovered via `irHasAssert`.)
  if s.isNil or found: return
  case s.kind
  of isBlock:
    for c in s.stmts: scanAssertDefect(c, procs, visited, found)
  of isIf:
    for br in s.branches: scanAssertDefect(br.body, procs, visited, found)
    if s.elseBody != nil: scanAssertDefect(s.elseBody, procs, visited, found)
  of isWhile:
    scanAssertDefect(s.wbody, procs, visited, found)
  of isTry:
    scanAssertDefect(s.tryBody, procs, visited, found)
    for h in s.tryHandlers: scanAssertDefect(h.body, procs, visited, found)
    if s.tryFinally != nil: scanAssertDefect(s.tryFinally, procs, visited, found)
  of isCall:
    if s.callee notin visited and s.callee in procs:
      visited.incl s.callee
      scanAssertDefect(procs[s.callee].body, procs, visited, found)
  of isRaise:
    if s.raiseTypeId == "AssertionDefect": found = true
  else: discard

proc irHasAssertDefect*(body: IRStmt,
                        procs: Table[string, ProcSig]): bool =
  ## Phase 15 E6. True iff the SUT (transitively) contains a raw-`assert`
  ## implicit `AssertionDefect` raise.
  var visited: HashSet[string]
  var found = false
  scanAssertDefect(body, procs, visited, found)
  found

proc irCollectLabels*(body: IRStmt,
                      procs: Table[string, ProcSig]): seq[string] =
  scanAll(body, procs).labels
