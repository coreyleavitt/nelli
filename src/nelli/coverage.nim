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

import std/[macros, hashes, tables, sets, math]

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

# RFC-fuzzer-nextgen G3fix. `symex/smt/dsl_parser.nim`'s `hasSymexOpaquePragma`
# recognizes a `{.symexOpaque.}` pragma purely BY NAME (it never checks which
# module defines the symbol), so a private local pragma template here is
# sufficient — this module stays a true leaf (no `nelli/symex` import, which
# would drag Z3 into `coverage.nim` and, through it, into `fuzz.nim`, which
# imports this module and must stay Z3-free). `symex.nim` separately exports
# its own public `symexOpaque*` for user-defined opaque procs (same name, same
# contract, unrelated declaration) — the two never collide because this one is
# never exported.
template symexOpaque() {.pragma.}

proc recordEdge*(id: int) {.inline, symexOpaque.} =
  ## Mark edge `id` as hit. `id mod coverageEdgeCount` is the bitmap
  ## slot; collisions are tolerated (AFL convention). Only the first
  ## hit of an edge updates the count, so re-hits in a tight loop
  ## don't inflate the score.
  ##
  ## Gated on `coverageMode`: returns immediately when the mode is
  ## `cmOff` so consumers of `{.cover.}`'d code pay nothing unless
  ## they've opted into recording via `setCoverageMode(cmRecording)`.
  ##
  ## RFC-fuzzer-nextgen G3fix: `{.symexOpaque.}` keeps the symex walker OUT of
  ## this body. Every real in-process `fuzz()` target is `{.cover.}`-
  ## instrumented (this IS how it gets coverage), so once G3's concolic bridge
  ## walks a real target, it walks a call to `recordEdge` too — descending
  ## into this body previously crashed the walker with an uncaught `KeyError`
  ## on the free-standing `coverageMode` threadvar reference below (`env` has
  ## no binding for a module-level threadvar; the walker only knows params and
  ## locals). `recordEdge` is a pure side-effect with zero bearing on the
  ## property's symbolic path — exactly the RFC #137 "opaque effectful call"
  ## shape `echo`/`writeFile` already get — so the fix is to make it opaque,
  ## not to teach the walker to model a threadvar it doesn't own.
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

## --- comparison-operand log + `{.covercmp.}` pragma (RFC-fuzzer-nextgen G4) -
##
## A `{.cover.}`-SIBLING, not an extension of it: `{.covercmp.}` walks a
## proc's body for comparison-operator expressions (`==`/`!=`/`<`/`<=`/`>`/
## `>=`) and rewrites each into a form that logs the operand pair through
## `logCmp` before performing the (unchanged) comparison. Composes cleanly
## with `{.cover.}` on the same proc — the two touch disjoint AST positions
## (branch bodies vs. comparison expressions), so `{.cover, covercmp.}` is
## just two independent structural rewrites, applied in pragma-list order.
##
## **Typed, not byte-level (§G-cmp).** `logCmp` is an OVERLOADED proc, one
## arm per type family nelli's choice nodes carry (`SomeInteger` ~ `ckInt`,
## `string` ~ `ckString`, `seq[byte]` ~ `ckBytes`), plus a generic `[T]`
## catch-all no-op so a comparison on any OTHER type (bool, float, enum,
## object `==`, char, ...) still compiles — it just isn't logged. Nim's
## overload resolution picks the most specific match at the (fully-typed)
## call site, which is why the macro can emit an UNTYPED call
## (`bindSym"logCmp"`, a closed symbol choice) without itself knowing the
## operand types — the same "no type info needed at macro-expansion time"
## property `{.cover.}`'s `recordEdge` injection already relies on.
##
## **`{.symexOpaque.}` (mandatory, not optional).** Every `logCmp` overload
## carries the SAME local `symexOpaque` pragma template `recordEdge` uses
## (G3fix) — without it, a property that is both `{.cover.}`'d (or walked at
## all) and `{.covercmp.}`'d would have the walker descend into `logCmp`'s
## body and crash on `cmpLogMode`'s free-standing threadvar reference,
## exactly the `recordEdge`/`coverageMode` crash G3fix fixed. `logCmp` is a
## pure side-effecting instrumentation call with zero bearing on the
## property's symbolic path — the RFC #137 "opaque effectful call" shape.

type
  CmpOp* = enum
    ## Which comparison operator produced a `CmpLogEntry` — carried so a
    ## future I2S consumer (G5) can tell an equality gate from an ordering
    ## gate without re-deriving it from context.
    coEq, coNe, coLt, coLe, coGt, coGe
    coUnknown
      ## RFC-fuzzer-nextgen G4 C3: the external `trace-cmp` tier's honest
      ## limitation — `-fsanitize-coverage=trace-cmp`'s
      ## `__sanitizer_cov_trace_cmp*` ABI passes only the operand PAIR, never
      ## which comparison operator triggered the call (upstream RedQueen/
      ## AFL++ implementations have the same gap). Appended LAST so the
      ## Nim-tier's six existing ordinals (`coEq`..`coGe`, already
      ## serialized by any prior `{.covercmp.}` log) are unchanged.

  CmpLogEntryKind* = enum
    ## Mirrors the choice-node type families §G-cmp scopes this to:
    ## `clkInt` ~ `ckInteger`, `clkBytes` ~ `ckBytes`, `clkString` ~
    ## `ckString`. No catch-all "other" kind — types outside this set are
    ## never logged at all (see `logCmp[T]`'s no-op fallback), so there is
    ## nothing to tag them with.
    clkInt, clkBytes, clkString

  CmpLogEntry* = object
    ## One logged comparison's operand pair, typed. `op` is common to every
    ## kind (hoisted above the `case`), so a consumer can filter/group by
    ## operator without a `case` dispatch first.
    op*: CmpOp
    case kind*: CmpLogEntryKind
    of clkInt:
      width*: int
        ## Operand byte-width (1/2/4/8 — `sizeof(T)` of the compared
        ## `SomeInteger` type), so a consumer can tell an 8-bit gate from a
        ## 32-bit one even though both operands are widened into `uint64`
        ## fields below.
      lhsInt*, rhsInt*: uint64
        ## The raw operand bit pattern, sign-extended (signed `T`) or
        ## zero-extended (unsigned `T`) to 64 bits — the natural C-style
        ## widening, not a value-preserving reinterpretation choice. A
        ## consumer that needs the original signed value back reads
        ## `width` and re-narrows.
    of clkBytes:
      lhsBytes*, rhsBytes*: seq[byte]
    of clkString:
      lhsStr*, rhsStr*: string

proc cmpOpFromStr(op: string): CmpOp =
  case op
  of "==": coEq
  of "!=": coNe
  of "<":  coLt
  of "<=": coLe
  of ">":  coGt
  of ">=": coGe
  else:
    ## Defensive default — `instrumentCmpNode` (below) only ever passes one
    ## of the six literals above, so this arm is unreachable in practice,
    ## not a silent-corruption path for real instrumented code.
    coEq

var cmpLogMode {.threadvar.}: bool
  ## Runtime gate on `logCmp`, the SAME zero-cost-until-opted-in discipline
  ## as `coverageMode` — `false` (off) by default so a `{.covercmp.}`'d proc
  ## costs nothing for a caller who never calls `setCmpLogMode(true)`. A
  ## bare `bool` rather than a mirror of `CoverageMode`: there is only ever
  ## "off" or "recording" here (no third state), so a dedicated two-value
  ## enum would just be a `bool` with extra ceremony.
var cmpLogBuf {.threadvar.}: seq[byte]
  ## The per-thread serialized operand-pair log, append-only within a
  ## `setCmpLogMode(true)` session — cleared by `resetCmpLog` (the cmp-log
  ## analog of `resetCoverage`), called before each run for per-run
  ## isolation.

proc setCmpLogMode*(recording: bool) =
  ## Set the per-thread comparison-log recording gate. `false` (off) is
  ## the zero-init default.
  cmpLogMode = recording

const clOff* = false
const clRecording* = true
  ## Named aliases for `setCmpLogMode`'s two states — read naturally at a
  ## call site (`setCmpLogMode(clRecording)`) without the ceremony of a
  ## dedicated enum type for what is otherwise a plain on/off switch.

proc currentCmpLogMode*(): bool =
  ## Current per-thread cmp-log recording gate. See `setCmpLogMode`.
  cmpLogMode

proc resetCmpLog*() =
  ## Clear the per-thread operand-pair log. Call before each run for
  ## per-run isolation — the cmp-log analog of `resetCoverage`.
  cmpLogBuf.setLen(0)

proc currentCmpLog*(): seq[byte] =
  ## The raw serialized log accumulated since the last `resetCmpLog` —
  ## parse with `parseCmpLog`. Exposed raw (not pre-parsed) so this is the
  ## SAME byte payload the shm transport (below) publishes, keeping one
  ## wire format for both the in-process and shm-mediated readers.
  cmpLogBuf

# --- minimal local binary primitives -----------------------------------------
#
# `coverage.nim` is a leaf module (see the file header) — deliberately NOT
# importing `binaryio.nim` (which would be the natural shared helper) to
# preserve that invariant. These four helpers are the small subset this
# wire format actually needs; duplicated rather than shared for that reason.

proc appendU8(buf: var seq[byte]; x: uint8) = buf.add x
proc appendU32(buf: var seq[byte]; x: uint32) =
  for i in 0 ..< 4: buf.add byte((x shr (8 * i)) and 0xFF'u32)
proc appendU64(buf: var seq[byte]; x: uint64) =
  for i in 0 ..< 8: buf.add byte((x shr (8 * i)) and 0xFF'u64)

proc readU8(data: openArray[byte]; pos: var int): uint8 =
  result = data[pos]; inc pos
proc readU32(data: openArray[byte]; pos: var int): uint32 =
  for i in 0 ..< 4: result = result or (uint32(data[pos + i]) shl (8 * i))
  pos += 4
proc readU64(data: openArray[byte]; pos: var int): uint64 =
  for i in 0 ..< 8: result = result or (uint64(data[pos + i]) shl (8 * i))
  pos += 8

proc recordCmpEntry(e: CmpLogEntry) =
  if not cmpLogMode: return
  cmpLogBuf.appendU8(uint8(ord(e.kind)))
  cmpLogBuf.appendU8(uint8(ord(e.op)))
  case e.kind
  of clkInt:
    cmpLogBuf.appendU8(uint8(e.width))
    cmpLogBuf.appendU64(e.lhsInt)
    cmpLogBuf.appendU64(e.rhsInt)
  of clkBytes:
    cmpLogBuf.appendU32(uint32(e.lhsBytes.len))
    cmpLogBuf.add e.lhsBytes
    cmpLogBuf.appendU32(uint32(e.rhsBytes.len))
    cmpLogBuf.add e.rhsBytes
  of clkString:
    cmpLogBuf.appendU32(uint32(e.lhsStr.len))
    for c in e.lhsStr: cmpLogBuf.add byte(c)
    cmpLogBuf.appendU32(uint32(e.rhsStr.len))
    for c in e.rhsStr: cmpLogBuf.add byte(c)

proc parseCmpLog*(data: openArray[byte]): seq[CmpLogEntry] =
  ## Decode a serialized operand-pair log (from `currentCmpLog()` or a shm
  ## read) into typed entries. **Gracefully truncates**, never raises: a
  ## record cut short (the shm transport's fixed-capacity clamp can land
  ## mid-record, same hazard `Coverage`'s dumps don't have but a growing
  ## append-log does) is simply dropped, not fabricated from partial bytes
  ## — matching G1b's "graceful truncation past the cap" precedent rather
  ## than raising `DbCorrupt`-style (this is a best-effort observability
  ## log, not a durable/replayed format that needs to fail loudly).
  var pos = 0
  while pos + 2 <= data.len:
    let kindB = data[pos]
    if kindB > uint8(ord(high(CmpLogEntryKind))): break   # not a valid tag — stop, don't misparse
    let opB = data[pos + 1]
    if opB > uint8(ord(high(CmpOp))): break
    let kind = CmpLogEntryKind(kindB)
    let op = CmpOp(opB)
    var p = pos + 2
    case kind
    of clkInt:
      if p + 1 + 8 + 8 > data.len: break
      let width = int(readU8(data, p))
      let lhs = readU64(data, p)
      let rhs = readU64(data, p)
      result.add CmpLogEntry(kind: clkInt, op: op, width: width, lhsInt: lhs, rhsInt: rhs)
      pos = p
    of clkBytes:
      if p + 4 > data.len: break
      let llen = int(readU32(data, p))
      if p + llen + 4 > data.len: break
      let lhs = data[p ..< p + llen]
      p += llen
      let rlen = int(readU32(data, p))
      if p + rlen > data.len: break
      let rhs = data[p ..< p + rlen]
      p += rlen
      result.add CmpLogEntry(kind: clkBytes, op: op, lhsBytes: lhs, rhsBytes: rhs)
      pos = p
    of clkString:
      if p + 4 > data.len: break
      let llen = int(readU32(data, p))
      if p + llen + 4 > data.len: break
      var lhs = newString(llen)
      for i in 0 ..< llen: lhs[i] = char(data[p + i])
      p += llen
      let rlen = int(readU32(data, p))
      if p + rlen > data.len: break
      var rhs = newString(rlen)
      for i in 0 ..< rlen: rhs[i] = char(data[p + i])
      p += rlen
      result.add CmpLogEntry(kind: clkString, op: op, lhsStr: lhs, rhsStr: rhs)
      pos = p

proc logCmp*[T: SomeInteger](lhs, rhs: T; op: string) {.symexOpaque.} =
  ## `ckInteger`-typed operand-pair hook. `T`'s `sizeof` is the logged
  ## width; the value is widened to `uint64` (sign-extended for a signed
  ## `T`, zero-extended for an unsigned one) — see `CmpLogEntry.lhsInt`'s
  ## doc.
  if not cmpLogMode: return
  let lhsWide = when T is SomeUnsignedInt: uint64(lhs) else: cast[uint64](int64(lhs))
  let rhsWide = when T is SomeUnsignedInt: uint64(rhs) else: cast[uint64](int64(rhs))
  recordCmpEntry(CmpLogEntry(kind: clkInt, op: cmpOpFromStr(op), width: sizeof(T),
                             lhsInt: lhsWide, rhsInt: rhsWide))

proc logCmp*(lhs, rhs: string; op: string) {.symexOpaque.} =
  ## `ckString`-typed operand-pair hook.
  if not cmpLogMode: return
  recordCmpEntry(CmpLogEntry(kind: clkString, op: cmpOpFromStr(op), lhsStr: lhs, rhsStr: rhs))

proc logCmp*(lhs, rhs: seq[byte]; op: string) {.symexOpaque.} =
  ## `ckBytes`-typed operand-pair hook.
  if not cmpLogMode: return
  recordCmpEntry(CmpLogEntry(kind: clkBytes, op: cmpOpFromStr(op), lhsBytes: lhs, rhsBytes: rhs))

proc logCmp*[T](lhs, rhs: T; op: string) {.symexOpaque.} =
  ## Catch-all no-op for any comparison type outside the `SomeInteger`/
  ## `string`/`seq[byte]` scope §G-cmp defines (bool, float, enum, char,
  ## object `==`, ...) — keeps a `{.covercmp.}`'d proc that happens to also
  ## compare, say, two floats or two bools COMPILING (overload resolution
  ## always has a match), it just logs nothing for that comparison. A
  ## narrower `T` overload above always wins when it applies (Nim prefers a
  ## concrete/constrained match over a bare generic), so this only ever
  ## fires for genuinely out-of-scope types.
  discard

const cmpOps = ["==", "!=", "<", "<=", ">", ">="]

proc instrumentCmpNode(n: NimNode): NimNode =
  ## Recursive AST rewrite: every `nnkInfix` node whose operator is one of
  ## the six comparison operators becomes a block that evaluates both
  ## operands ONCE into temporaries, logs the pair via `logCmp`, then
  ## performs the (unchanged) comparison on those same temporaries — so a
  ## side-effecting operand expression is never evaluated twice just
  ## because it's now also being logged. All other nodes are walked
  ## structurally so a comparison nested anywhere in the body (not just a
  ## branch condition) is still found.
  ##
  ## `nnkWhenStmt` is the one required exception (mirrors why `{.cover.}`
  ## never touches an `if`/`when`'s CONDITION, only its branch bodies —
  ## though for a different reason here): a `when` condition is evaluated
  ## at COMPILE time, so rewriting a comparison in it into a runtime
  ## `logCmp` call would make the condition no longer const-evaluable and
  ## break compilation. Branch BODIES of a `when` are ordinary runtime code
  ## and are still walked. `nnkConstSection` is excluded for the same
  ## reason (a `const`'s initializer must stay compile-time-foldable).
  case n.kind
  of nnkInfix:
    let opName = if n[0].kind in {nnkIdent, nnkSym}: n[0].strVal else: ""
    if opName in cmpOps:
      let lhs = instrumentCmpNode(n[1])
      let rhs = instrumentCmpNode(n[2])
      let lTmp = genSym(nskLet, "cmpL")
      let rTmp = genSym(nskLet, "cmpR")
      result = nnkStmtListExpr.newTree(
        newLetStmt(lTmp, lhs),
        newLetStmt(rTmp, rhs),
        newCall(bindSym"logCmp", lTmp, rTmp, newLit(opName)),
        nnkInfix.newTree(n[0], lTmp, rTmp))
    else:
      result = n.copyNimNode
      for child in n: result.add instrumentCmpNode(child)
  of nnkWhenStmt:
    result = n.copyNimNode
    for branch in n:
      case branch.kind
      of nnkElifBranch, nnkElifExpr:
        result.add nnkElifBranch.newTree(branch[0], instrumentCmpNode(branch[1]))
      of nnkElse, nnkElseExpr:
        result.add nnkElse.newTree(instrumentCmpNode(branch[0]))
      else:
        result.add branch
  of nnkConstSection:
    result = n  # left entirely untouched — see the doc comment above
  else:
    result = n.copyNimNode
    for child in n: result.add instrumentCmpNode(child)

macro covercmp*(procDef: untyped): untyped =
  ## Pragma macro: rewrite the proc's body so each comparison operator logs
  ## its typed operand pair via `logCmp`. Use as `proc f(x: int)
  ## {.covercmp.} = ...`, or combine with `{.cover.}` on the same proc — the
  ## two rewrites are orthogonal (see the module doc above).
  expectKind procDef, {nnkProcDef, nnkFuncDef, nnkLambda}
  procDef[^1] = instrumentCmpNode(procDef[^1])
  result = procDef

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

  FrontierStats* = object
    ## RFC-fuzzer-nextgen S1 (ADR-0031 D4): the ONE incrementally-maintained
    ## sub-object of per-slot frontier statistics, folded in at the single
    ## `admit` fold below — never rescanned, so no consumer can ever read a
    ## snapshot that disagrees with `admit` about update timing (the exact
    ## hazard the round-3 breadth fix on S1/G3 named).
    ##
    ## **Extensibility contract for G3 (round-3 breadth fix):** G3's
    ## orchestrator-wide staleness/stall-detection state is a derived
    ## statistic over this SAME `CoverageFrontier`, so it belongs on this
    ## SAME object, not a sibling one — add G3's fields here and fold their
    ## updates into the SAME loop in `admit`, never a second update site.
    hitCounts: seq[int]
      ## S1: per-slot count of `admit` calls whose `Coverage` touched slot
      ## `i` (`counters[i] > 0`) — the "abundance" S1's rarity weight is
      ## shaped over. Counts EVERY folded run, not only ones that raised
      ## the slot's bucket (rarity is about how many of the campaign's
      ## executions ever REACH a slot, not how many improved it) and not
      ## only ones retained in the corpus (`admit` is called for every
      ## non-rejected run the loop drives, corpus-admitted or not) —
      ## matching Böhme's/AFL's abundance measured over the full execution
      ## history, not just the surviving corpus.
    totalAdmitted*: int
      ## S1: total `admit` calls folded so far — the rarity denominator.
    lastImprovedSeq: seq[int]
      ## S1: the `totalAdmitted` sequence number at which slot `i`'s bucket
      ## last ROSE (0 = never, i.e. still at its construction-time value).
      ## Region = coverage slot, the same indexing as `accum` below.
    lastGlobalImprovedSeq: int
      ## RFC-fuzzer-nextgen G3: the `totalAdmitted` sequence number at
      ## which the frontier's coverage last improved AT ALL (any slot's
      ## bucket rose) — folded at the SAME `admit` fold below, per the
      ## extensibility contract above (never a second update site). This
      ## is ONE counter for the whole campaign, not per-slot: `stalled`
      ## reads it as the orchestrator-WIDE staleness signal (round-2 depth
      ## fix — a per-worker view would fire the concolic bridge for an
      ## edge a sibling worker is concurrently covering by mutation, the
      ## "solved-but-superseded" waste a shared-frontier counter avoids).

  CoverageFrontier* = object
    ## The accumulated bucket map for one campaign/target. `accum[i]` is the highest
    ## bucket ever seen for slot `i` (0 = unseen). `targetId` (D12) keys persistence;
    ## a map of a different size than `accum` is a different target/backend.
    targetId*: string
    accum: seq[uint8]
    stats*: FrontierStats
      ## RFC-fuzzer-nextgen S1: see `FrontierStats` — maintained by `admit`
      ## alongside `accum`, in lockstep, at the same fold.

proc hitCount*(stats: FrontierStats; slot: int): int =
  ## S1: how many `admit` calls have touched `slot` — 0 for an out-of-range
  ## or never-touched slot (never negative, never an index error).
  if slot < 0 or slot >= stats.hitCounts.len: 0
  else: stats.hitCounts[slot]

proc lastImprovedAt*(stats: FrontierStats; slot: int): int =
  ## S1: the `totalAdmitted` sequence number `slot`'s bucket last rose at —
  ## 0 for an out-of-range or never-improved slot.
  if slot < 0 or slot >= stats.lastImprovedSeq.len: 0
  else: stats.lastImprovedSeq[slot]

proc rarityWeight*(stats: FrontierStats; slot: int): float =
  ## RFC-fuzzer-nextgen S1: the Entropic (Böhme information-gain) rarity
  ## weight for `slot` — `-log2(hits/totalAdmitted)`, the Shannon
  ## self-information of `slot` having been reached at all, over every
  ## admitted (non-rejected) run so far. Chosen over a raw `1/hits`
  ## weighting because it degrades smoothly (`1/hits` halves discontinuously
  ## between hits=1 and hits=2; `-log2` grows gently as abundance shrinks)
  ## and is the direct information-theoretic quantity Böhme's Entropic
  ## schedule is named for, rather than an ad-hoc reciprocal.
  ##
  ## 0 (never negative — `hits <= totalAdmitted` always) when EVERY
  ## admitted run has hit `slot` (no information in seeing it again); 0,
  ## not NaN/Inf, when there's no signal yet (`totalAdmitted == 0`) or the
  ## slot has never been hit.
  let hits = hitCount(stats, slot)
  if stats.totalAdmitted <= 0 or hits <= 0: return 0.0
  result = -log2(hits.float / stats.totalAdmitted.float)

proc staleness*(stats: FrontierStats): int =
  ## RFC-fuzzer-nextgen G3: admits since the frontier's coverage last
  ## improved AT ALL (any slot's bucket rose) — 0 when the very last
  ## admit improved it, or when nothing has been admitted yet.
  stats.totalAdmitted - stats.lastGlobalImprovedSeq

proc stalled*(f: CoverageFrontier; k: int): bool =
  ## RFC-fuzzer-nextgen G3: true iff at least `k` admits have passed since
  ## the frontier's coverage last improved — the orchestrator-wide stall
  ## signal border-selection/concolic-bridge invocation gates on. Reads
  ## the ONE shared `FrontierStats`, never a per-worker count (see
  ## `lastGlobalImprovedSeq`'s doc). `k <= 0` never stalls — the disabled/
  ## inert default, matching every other additive knob's convention in
  ## this codebase (`stormWindow`, `reVerify`, ...).
  k > 0 and staleness(f.stats) >= k

proc frontierStatsSnapshot*(stats: FrontierStats):
    tuple[hitCounts, lastImprovedSeq: seq[int], totalAdmitted, lastGlobalImprovedSeq: int] =
  ## RFC-fuzzer-nextgen S6: read-only access to every `FrontierStats` field
  ## for checkpoint serialization (`nelli/learnedstate`). `hitCounts`/
  ## `lastImprovedSeq` are otherwise private — a serializer outside this
  ## module has no other way to reach them.
  (hitCounts: stats.hitCounts, lastImprovedSeq: stats.lastImprovedSeq,
   totalAdmitted: stats.totalAdmitted,
   lastGlobalImprovedSeq: stats.lastGlobalImprovedSeq)

proc restoreFrontierStats*(hitCounts, lastImprovedSeq: seq[int];
                           totalAdmitted, lastGlobalImprovedSeq: int): FrontierStats =
  ## RFC-fuzzer-nextgen S6: the inverse of `frontierStatsSnapshot` — rebuild
  ## a `FrontierStats` from a checkpoint's decoded fields. Trusts the
  ## caller (the checkpoint decoder already bounds-checked the raw bytes);
  ## `admit`'s own `hitCounts.len < c.counters.len` growth check tolerates
  ## whatever length is restored here (0 for a checkpoint saved before the
  ## first admit, or exactly `coverageEdgeCount` afterward — see the module
  ## doc's "slot layout is fixed" note).
  FrontierStats(hitCounts: hitCounts, lastImprovedSeq: lastImprovedSeq,
                totalAdmitted: totalAdmitted,
                lastGlobalImprovedSeq: lastGlobalImprovedSeq)

proc coveredSlots*(c: Coverage): seq[int] =
  ## RFC-fuzzer-nextgen S1: the sparse nonzero-slot index list of `c`.
  ## `entropicEnergy` walks this instead of the full (up to
  ## `coverageEdgeCount`-slot) `counters` array, so per-candidate energy
  ## recomputation — needed every parent-selection tick, since the rarity
  ## denominator keeps moving as the campaign runs — stays cheap even as
  ## the corpus and iteration count grow.
  for i, b in c.counters:
    if b > 0'u8: result.add i

const
  entropicBaseEnergy* = 1.0
    ## S1: additive floor so `entropicEnergy` is always strictly positive —
    ## no corpus entry (not even one covering zero rare edges) is ever
    ## permanently starved of a nonzero selection probability.
  entropicCostSizeScale* = 64.0
    ## S1: input size (choice-node count) at which the size term contributes
    ## a full unit of cost — the exec-cost term is a plain fraction of this,
    ## no running corpus average needed (unlike AFL's `avg_bitmap_size`),
    ## which keeps the schedule a pure function of ONE candidate.
  entropicCostTimeScale* = 1_000_000.0
    ## S1: nanoseconds (1ms) at which the timing term contributes a full
    ## unit of cost.

proc executionCostFactor*(sizeChoices: int; execNanos: int64): float =
  ## RFC-fuzzer-nextgen S1's exec-cost term: favors fast, small inputs.
  ## Always in `(0, 1]` — a pure discount, never a bonus, and never zero
  ## (an unboundedly large/slow input asymptotically approaches, never
  ## reaches, zero cost-factor). `execNanos <= 0` means "no timing signal
  ## available" (only a `Target` that actually measures wall time sets
  ## `Observation.runResult.durationNs`) — degrades to size-only cost,
  ## never penalizes a candidate for missing data it was never given.
  let sizeCost = sizeChoices.float / entropicCostSizeScale
  let timeCost = if execNanos > 0: execNanos.float / entropicCostTimeScale else: 0.0
  1.0 / (1.0 + sizeCost + timeCost)

proc entropicEnergy*(coveredSlots: seq[int]; stats: FrontierStats;
                     sizeChoices: int; execNanos: int64 = 0): float =
  ## RFC-fuzzer-nextgen S1 (ADR-0031 D4): the Entropic power-schedule energy
  ## for a candidate covering `coveredSlots`, replacing the old coarse
  ## recency/lineage `2.0`/`+1.0` scheme. `energy ∝ Σ rarityWeight(slot) for
  ## slot in coveredSlots`, scaled by the exec-cost discount — a rare-edge-
  ## covering, fast/small input scores highest; a common-edges-only,
  ## slow/large one scores lowest, but never zero (`entropicBaseEnergy`).
  var raritySum = 0.0
  for slot in coveredSlots: raritySum += rarityWeight(stats, slot)
  (entropicBaseEnergy + raritySum) * executionCostFactor(sizeChoices, execNanos)

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
  ##
  ## RFC-fuzzer-nextgen S1: this is also the ONE site `FrontierStats` is
  ## folded at — `f.stats.hitCounts`/`totalAdmitted`/`lastImprovedSeq` are
  ## updated here, in the same pass as `accum`, never rescanned elsewhere.
  if f.accum.len < c.counters.len:
    f.accum.setLen(c.counters.len)
  if f.stats.hitCounts.len < c.counters.len:
    f.stats.hitCounts.setLen(c.counters.len)
    f.stats.lastImprovedSeq.setLen(c.counters.len)
  inc f.stats.totalAdmitted
  for i in 0 ..< c.counters.len:
    if c.counters[i] > 0'u8:
      inc f.stats.hitCounts[i]
    let b = bucketOf(c.counters[i])
    if b > f.accum[i]:
      f.accum[i] = b
      inc result.newEdges
      f.stats.lastImprovedSeq[i] = f.stats.totalAdmitted
  result.interesting = result.newEdges > 0
  result.globalEdges = f.coveredEdges
  if result.newEdges > 0:
    f.stats.lastGlobalImprovedSeq = f.stats.totalAdmitted

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

  # RFC-fuzzer-nextgen G4 C2: the cmp-log's OWN shm channel (`nelli_shm.c`'s
  # `pt_cmplog_*`) — independent static state from the `pt_shm_*` coverage
  # channel above, so both can be attached in the same process at once.
  proc ptCmplogInit(name: cstring; capacity: uint32): cint {.importc: "pt_cmplog_init".}
  proc ptCmplogResetBuffer() {.importc: "pt_cmplog_reset_buffer".}
  proc ptCmplogPublishBytes(data: ptr uint8; len: uint32) {.importc: "pt_cmplog_publish_bytes".}
  proc ptCmplogRead(outp: ptr uint8; outCap: uint32; outLen: ptr uint32): cint {.importc: "pt_cmplog_read".}

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

  # --- cmp-log shm transport (RFC-fuzzer-nextgen G4 C2) ----------------------
  #
  # The SAME push/copy + generation-word protocol as the coverage probe
  # above, over `nelli_shm.c`'s SECOND, independent channel (`pt_cmplog_*` —
  # see that file's G4 comment for why a second channel, not a second
  # `pt_shm_init` call, was needed). A persistent worker resets before each
  # input and publishes after (mirroring `shmResetCoverage`/
  # `shmPublishCoverage`'s own per-run discipline, wired at the SAME call
  # sites in `fuzzworker.nim`); the orchestrator reads back independently of
  # the pipe-carried `Observation` (coverage's own established shape: a
  # shm-transported per-run artifact is read via its OWN probe, never folded
  # into the wire-frame result — see E2a C2's `Observation` field note).

  const cmpLogShmCapacity* = 65536
    ## Fixed per-run byte capacity for the cmp-log shm channel — generous
    ## relative to a typical property's per-run comparison count; a run that
    ## exceeds it is gracefully clamped (`pt_shm_commit`'s existing
    ## truncation clamp) and `parseCmpLog` drops the cut-off trailing
    ## record rather than misparsing it (see its doc comment).

  proc shmResetCmpLog*(shmName: string) =
    ## WORKER-side per-input reset (called BEFORE running an input): clear
    ## the in-process log (`resetCmpLog`) AND the shm staging buffer
    ## (`pt_cmplog_reset_buffer`), re-arming the publish gate — the cmp-log
    ## analog of `shmResetCoverage`.
    discard ptCmplogInit(shmName.cstring, uint32(cmpLogShmCapacity))
    resetCmpLog()
    ptCmplogResetBuffer()

  proc shmPublishCmpLog*(shmName: string) =
    ## WORKER-side per-input publish (called AFTER running an input):
    ## publishes whatever `logCmp` accumulated into `cmpLogBuf` THIS run
    ## (no separate snapshot parameter, unlike `shmPublishCoverage` — the
    ## live per-thread buffer IS this run's complete log by publish time,
    ## nothing else could have appended to it since the last
    ## `shmResetCmpLog`). A no-op if nothing was logged (never the case for
    ## a `{.covercmp.}`'d property mid-recording that hit at least one
    ## comparison; defensive only, matching `shmPublishCoverage`'s own
    ## empty-guard).
    discard ptCmplogInit(shmName.cstring, uint32(cmpLogShmCapacity))
    if cmpLogBuf.len == 0: return
    var buf = cmpLogBuf
    ptCmplogPublishBytes(addr buf[0], uint32(buf.len))

  proc shmReadCmpLogBytes*(shmName: string): seq[byte] =
    ## Raw serialized bytes of a persistent worker's shm-published cmp log
    ## — parse with `parseCmpLog`, or use `shmReadCmpLog` for the
    ## already-parsed form.
    discard ptCmplogInit(shmName.cstring, uint32(cmpLogShmCapacity))
    result = newSeq[byte](cmpLogShmCapacity)
    var outLen: uint32 = 0
    let ok = ptCmplogRead(addr result[0], uint32(cmpLogShmCapacity), addr outLen)
    if ok == 0 or outLen == 0: result = @[]
    elif int(outLen) < cmpLogShmCapacity: result.setLen(int(outLen))

  proc shmReadCmpLog*(shmName: string): seq[CmpLogEntry] =
    ## The orchestrator-side read: a persistent worker's shm-published cmp
    ## log, already decoded into typed entries. An UNPUBLISHED region (no
    ## input completed yet) reads as an empty seq — absent, never stale,
    ## matching `shmReadCoverage`'s discipline.
    parseCmpLog(shmReadCmpLogBytes(shmName))
