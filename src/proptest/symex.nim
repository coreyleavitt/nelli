## proptest/symex — public-API entry for the symbolic-execution capability.
##
## See:
##   * docs/SYMEX_PLAN.md     — build plan + scope
##   * docs/symex/ADR-0001-integer-semantics.md
##   * docs/symex/ADR-0002-dsl-factoring.md
##
## Phase 1 supports a small Nim fragment: int/bool params + locals,
## arithmetic + comparison + boolean, `if` / `elif` / `else`, the
## three body markers below. Each later phase widens the fragment.
##
## Body markers — these are templates so that the same SUT is
## simultaneously walkable by symex AND runnable under random PBT
## without source duplication. Outside symex:
##
##   * `symexTarget(name)`  — no-op (it's a coverage label)
##   * `symexAssert(cond)`  — `doAssert cond` (it's a stated invariant)
##   * `symexAssume(cond)`  — early return if violated (filter the
##                            execution to satisfying inputs)

import std/[macros, sets, tables, algorithm, options]
import z3
export z3.z3FullVersion
import ./choice
export choice
import ./smt/dsl
export dsl
import ./smt/scan
import ./engine/types as engineTypes
export engineTypes.SymexFinding, engineTypes.SymexFindingStatus

# ---- Witness → ChoiceNode bridge -------------------------------------------
#
# A symex witness is a Nim tuple (the proc's parameter list). Phase 7
# linearises it into a `seq[ChoiceNode]` so the same regression-seed
# substrate proptest already uses for random examples can carry
# symex-derived counterexamples. The encoding is deterministic and
# length-prefixed for variable-cardinality container shapes.

const sxIntMin = low(int64)
const sxIntMax = high(int64)
const sxLenMax = high(int64)

proc sortedKeysOf[K, V](t: Table[K, V]): seq[K] =
  ## Returns `t`'s keys in deterministic ascending order. Used by
  ## `renderAsChoices` to defeat Nim's undefined hash-iteration
  ## order so identical witnesses produce identical choice
  ## sequences. Local helper to dodge z3's shadowing of
  ## `tables.keys` at the `renderAsChoices` call-site scope.
  for k, _ in t: result.add k
  sort(result)

proc sortedElemsOf[E](s: HashSet[E]): seq[E] =
  ## HashSet counterpart of `sortedKeysOf`.
  for e in s: result.add e
  sort(result)

proc renderAsChoices*[T](w: T): seq[ChoiceNode] =
  when T is bool:
    result.add booleanChoice(w, 0.5)
  elif T is SomeFloat:
    # Phase 15 F7: a symex float witness rides as a single `floatChoice`.
    # The constraint window is fully permissive — `[-Inf, +Inf]`, `allowNan
    # = true`, `smallestNonzeroMagnitude = 0.0` — so any IEEE-754 bit pattern
    # (NaN, ±Inf, subnormals, ±0) passes `permits` and round-trips through the
    # choice IR / `floats` replay strategy. `floatVal` is a float64, so a
    # float32 witness widens losslessly on the way in and narrows back on read.
    result.add floatChoice(float64(w), -Inf, Inf, allowNan = true,
                           smallestNonzeroMagnitude = 0.0)
  elif T is SomeSignedInt:
    result.add integerChoice(int64(w), sxIntMin, sxIntMax, 0'i64)
  elif T is SomeUnsignedInt:
    # Symex's uint widths fit in int64 modulo width; cast for the
    # constraint window. Witness values are non-negative.
    result.add integerChoice(int64(w), 0'i64, sxIntMax, 0'i64)
  elif T is string:
    # Full Unicode minus the UTF-16 surrogate block — `intervals`
    # rejects any range intersecting `[surrogateLo, surrogateHi]`.
    result.add stringChoice(w,
      intervals(@[(0'i32, surrogateLo - 1),
                   (surrogateHi + 1, maxCodepoint)]),
      0, w.len)
  elif T is array:
    for e in w:
      result.add renderAsChoices(e)
  elif T is seq:
    # Continue-boolean protocol matching `lists`/`tables`/`sets`
    # strategies (strategy.nim:406-475): each element preceded by
    # `drawBoolean(0.9)` = true, list terminated by a final false.
    # The old length-prefix encoding was incompatible with replay
    # through these strategies; renderAsChoicesVersion bumps "1"
    # → "2" to invalidate stale collection witnesses in the DB.
    for e in w:
      result.add booleanChoice(true, 0.9)
      result.add renderAsChoices(e)
    result.add booleanChoice(false, 0.9)
  elif T is HashSet:
    # Sort by element before iterating: Nim's HashSet iteration
    # order is undefined, and the cache key is content-addressed on
    # the choice sequence — same logical witness must round-trip to
    # identical choices across runs.
    for e in sortedElemsOf(w):
      result.add booleanChoice(true, 0.9)
      result.add renderAsChoices(e)
    result.add booleanChoice(false, 0.9)
  elif T is Table:
    # Sort by key for the same determinism reason.
    for k in sortedKeysOf(w):
      result.add booleanChoice(true, 0.9)
      result.add renderAsChoices(k)
      result.add renderAsChoices(w[k])
    result.add booleanChoice(false, 0.9)
  elif T is tuple:
    for f in fields(w):
      result.add renderAsChoices(f)
  elif T is enum:
    # Phase 11 cycle 8 — enums (and variant discriminators) ride as
    # integer choices keyed on ordinal value. shrinkTowards points
    # at low(T) so the shrinker collapses to the first enum
    # constant by convention.
    result.add integerChoice(int64(ord(w)),
                              int64(ord(low(T))), int64(ord(high(T))),
                              int64(ord(low(T))))
  elif T is object:
    # For variant objects, Nim's `fields(w)` iterates the
    # discriminator plus only the *active arm's* fields — inactive
    # arms are skipped. Result: positional order is [discriminator,
    # active-arm field 1, active-arm field 2, …], which matches
    # Phase 11 cycle 8's contract.
    for f in fields(w):
      result.add renderAsChoices(f)
  else:
    {.error: "renderAsChoices: unsupported witness shape".}

# ---- assertCoveredBy capture context ----------------------------------------
#
# Phase 7's `assertCoveredBy` proves that a user-supplied `testFn`
# exercises a symex-reachable target on its concrete witness. The
# coverage signal is the same `symexTarget(name)` markers the parser
# already recognizes — outside symex they were no-ops, now they
# additionally feed a thread-local hit-set when an `assertCoveredBy`
# capture is active. The cost when no capture is active is one
# threadvar load + branch.

type SymexCaptureCtx* = ref object
  active*:           bool
  hits*:             HashSet[string]

var symexCapture* {.threadvar.}: SymexCaptureCtx

proc symexCaptureBegin*() =
  if symexCapture.isNil:
    symexCapture = SymexCaptureCtx()
  symexCapture.active = true
  symexCapture.hits.clear()

proc symexCaptureEnd*(): HashSet[string] =
  ## Returns the set of `symexTarget` names hit during the capture.
  ## After this call the context is inactive again.
  result = symexCapture.hits
  symexCapture.active = false
  symexCapture.hits.clear()

proc symexCaptureRecord*(name: string) {.inline.} =
  if not symexCapture.isNil and symexCapture.active:
    symexCapture.hits.incl(name)

# ---- SymexFinding sink (relocated to engine/types in Phase 12 cycle 1) ------
#
# The threadvar + recordSymexFinding + consumeSymexFindings live in
# `engine/types.nim` so phase modules can record findings without a
# circular import into the full symex+z3 stack. They're re-exported
# below for callers that imported them from `proptest/symex`.
export engineTypes.symexFindings,
       engineTypes.recordSymexFinding,
       engineTypes.consumeSymexFindings

proc describeTarget*(t: SymexTarget): string =
  case t.kind
  of stkLabel:              "label(\"" & t.label & "\")"
  of stkAssertionViolation: "assertion-violation"
  of stkIndexError:         "index-error"
  of stkFieldDefect:        "field-defect"
  of stkRaisedExn:                                       ## Phase 15 E2a
    if t.typeFilter.len == 0: "raised-exn(any)"
    else:                     "raised-exn(" & t.typeFilter & ")"

# ---- Content-addressed DB persistence ---------------------------------------
#
# Symex witnesses persist under a content-addressed key derived from
# (canonical SUT IR, target, witness-relevant settings, Z3 version,
# Nim version, walker version). Identical inputs → identical key;
# any change to *anything that affects the witness* rotates the key
# so stale entries become invisible. See docs/symex/determinism.md
# and proptest/smt/canonicalize.nim for the canonical-encoding
# contract and the proof obligations on each input.
import ./db
export db
import ./strategy
import ./engine
import ./engine/phases
import ./engine/pipeline
import ./optbox
import ./smt/canonicalize
export canonicalize.symexCacheKey, canonicalize.symexWalkerVersion,
       canonicalize.renderAsChoicesVersion, canonicalize.canonicalize,
       canonicalize.cacheKeySat, canonicalize.cacheKeyUnsat,
       canonicalize.cacheKeyUnknown, canonicalize.cacheKeyRaised,
       canonicalize.verdictCacheMaxEntries

proc saveSymexWitnessImpl*(db: ExampleDatabase, prog: SymexProgram,
                           target: SymexTarget, settings: SymexSettings,
                           finding: SymexFinding,
                           errors: var seq[string],
                           maxEntries = 64) =
  ## Runtime body of `saveSymexWitness`. Skips non-Sat findings (no
  ## witness to persist), otherwise saves the choice array under the
  ## content-addressed key with `:sat` suffix.
  ##
  ## DB save errors are appended to `errors` and the call returns
  ## normally — symmetric with `saveSymexVerdictImpl`. Closes a
  ## pre-existing inconsistency where `db.nim`'s module promise
  ## ("errors flow to Report.dbErrors") was violated here by
  ## propagating exceptions. Callers route `errors` into
  ## `Report.dbErrors`.
  if finding.status != sfSat: return
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & cacheKeySat
  try:
    db.save(key, finding.witnessChoices, maxEntries)
  except CatchableError as e:
    errors.add "saveSymexWitnessImpl: " & $e.name & ": " & e.msg

proc loadSymexWitnessesImpl*(db: ExampleDatabase, prog: SymexProgram,
                             target: SymexTarget,
                             settings: SymexSettings,
                             errors: var seq[string]
                            ): seq[seq[ChoiceNode]] =
  ## Runtime body of `loadSymexWitnesses`. Returns the persisted
  ## witnesses for *exactly* this SUT/target/settings/Z3/Nim/walker
  ## combination. Mismatched key → empty seq.
  ##
  ## Load errors append to `errors` and the call degrades to an
  ## empty seq (treated as "miss") — symmetric with
  ## `loadSymexVerdictImpl`. The cache is best-effort.
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & cacheKeySat
  try:
    db.loadPrimary(key)
  except CatchableError as e:
    errors.add "loadSymexWitnessesImpl: " & $e.name & ": " & e.msg
    @[]

proc saveSymexVerdictImpl*(db: ExampleDatabase, prog: SymexProgram,
                            target: SymexTarget, settings: SymexSettings,
                            status: SymexFindingStatus,
                            errors: var seq[string]) =
  ## Phase 13 cycle 3. Persist a non-SAT verdict (sfUnsat /
  ## sfUnknown) under the content-addressed key with the
  ## appropriate suffix. The stored value is the sentinel empty
  ## `seq[ChoiceNode]`; `verdictCacheMaxEntries = 1` keeps the
  ## slot to a single entry so the positional load invariant
  ## `result[0] == @[]` cannot break.
  ##
  ## No-op for `sfSat` (use `saveSymexWitnessImpl`) and for
  ## `sfNotApplicable` (verdict is local context, not a Z3 outcome
  ## worth caching).
  ##
  ## DB save errors are appended to `errors` and the call returns
  ## normally. The cache is best-effort: a failure to persist must
  ## never abort the analysis. Callers route `errors` into
  ## `Report.dbErrors` per the documented `db.nim` contract.
  let suffix =
    case status
    of sfUnsat:   cacheKeyUnsat
    of sfUnknown: cacheKeyUnknown
    of sfSat, sfNotApplicable, sfReplayMiss: return
      # `sfReplayMiss` (Phase 14 B5) is a per-replay diagnostic;
      # it's not a verdict and has no cache representation.
    of sfRaised: return
      # Phase 15 E2a. An `sfRaised` finding carries a per-type id and is
      # persisted by `saveSymexRaisedImpl` (multi-finding protocol), not by
      # this single-sentinel verdict path. No-op here.
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion) & suffix
  try:
    db.save(key, @[], verdictCacheMaxEntries)
  except CatchableError as e:
    errors.add "saveSymexVerdictImpl: " & $e.name & ": " & e.msg

proc loadSymexVerdictImpl*(db: ExampleDatabase, prog: SymexProgram,
                            target: SymexTarget, settings: SymexSettings,
                            errors: var seq[string]
                           ): Option[SymexFindingStatus] =
  ## Phase 13 cycle 3. Cache lookup for non-SAT verdicts. Checks
  ## the `:unsat` suffix first, then `:unk` — UNSAT-first
  ## **load-order** tie-break: when both verdicts have been
  ## persisted under the same `H` (possible across `queryRLimit`
  ## bumps that turned a prior UNKNOWN into UNSAT), the stronger
  ## verdict wins regardless of save order.
  ##
  ## Returns `some(sfUnsat)` / `some(sfUnknown)` on hit; `none`
  ## on full miss. Never exposes the raw `seq[seq[ChoiceNode]]`
  ## to callers — the sentinel must not leak into any code path
  ## that might pass it to `db.removeMany`.
  ##
  ## Load errors are appended to `errors` and the call degrades
  ## to a miss so the analysis can re-derive cold.
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  template tryLoad(suffix: string, verdict: SymexFindingStatus): untyped =
    try:
      let entries = db.loadPrimary(baseKey & suffix)
      if entries.len == 1 and entries[0].len == 0:
        return some(verdict)
    except CatchableError as e:
      errors.add "loadSymexVerdictImpl: " & $e.name & ": " & e.msg
  tryLoad(cacheKeyUnsat, sfUnsat)
  tryLoad(cacheKeyUnknown,   sfUnknown)
  none(SymexFindingStatus)

const cacheKeyRaisedIndex = ":raised"
  ## Phase 15 E2a. Index slot for the multi-`sxRaised` cache protocol. The
  ## per-type sentinels live under `cacheKeyRaised(typeId)` (e.g.
  ## `:raised:ValueError`); the index here enumerates which type ids were
  ## persisted (the general example-DB has no key-prefix scan, so the set of
  ## raised types must be recorded explicitly to be reloadable).

proc saveSymexRaisedImpl*(db: ExampleDatabase, prog: SymexProgram,
                          target: SymexTarget, settings: SymexSettings,
                          found: seq[RawResult],
                          errors: var seq[string]) =
  ## Phase 15 E2a. Persist every `sxRaised` finding in `found` under the
  ## content-addressed key. STRUCTURAL multi-finding protocol: each distinct
  ## raised type id is written
  ##   (a) as a per-type sentinel under `cacheKeyRaised(typeId)` (RFC: one DB
  ##       slot per `(exnType)` finding), and
  ##   (b) as an index entry under `cacheKeyRaisedIndex` so `loadSymexRaisedImpl`
  ##       can enumerate the persisted type ids without a DB key-prefix scan.
  ## A SUT with two distinct raise paths (e.g. ValueError, IOError) round-trips
  ## both findings through save/load. No witness is stored in E2a (the structural
  ## walker emits no witness); E2b populates witnesses.
  ##
  ## DB save errors are appended to `errors` and the call returns normally — the
  ## cache is best-effort (symmetric with `saveSymexVerdictImpl`).
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  # Distinct type ids in first-seen order (duplicate raise paths of the same
  # type collapse to a single DB slot — the per-type key is the unit of record).
  var typeIds: seq[string] = @[]
  for raw in found:
    if raw.status != sxRaised: continue
    if raw.raisedTypeId notin typeIds:
      typeIds.add raw.raisedTypeId
  if typeIds.len == 0: return
  try:
    for tid in typeIds:
      # (a) per-type sentinel slot.
      db.save(baseKey & cacheKeyRaised(tid), @[], verdictCacheMaxEntries)
      # (b) index entry: the type id encoded as its raw bytes.
      db.save(baseKey & cacheKeyRaisedIndex,
              @[bytesChoice(cast[seq[byte]](tid), 0, tid.len)],
              typeIds.len)
  except CatchableError as e:
    errors.add "saveSymexRaisedImpl: " & $e.name & ": " & e.msg

proc loadSymexRaisedImpl*(db: ExampleDatabase, prog: SymexProgram,
                          target: SymexTarget, settings: SymexSettings,
                          errors: var seq[string]): seq[RawResult] =
  ## Phase 15 E2a. Reconstruct the full `seq[RawResult]` of `sxRaised` findings
  ## from the DB without re-invoking Z3. Reads the index slot
  ## (`cacheKeyRaisedIndex`) to enumerate the persisted type ids and rebuilds one
  ## `RawResult{status: sxRaised, raisedTypeId}` per entry. The per-type sentinel
  ## slots (`cacheKeyRaised(typeId)`) are confirmatory; the index is the
  ## enumeration source. Returns `@[]` on a full miss.
  ##
  ## Load errors are appended to `errors` and the call degrades to a miss
  ## (symmetric with `loadSymexVerdictImpl`). Best-effort.
  let baseKey = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  try:
    let entries = db.loadPrimary(baseKey & cacheKeyRaisedIndex)
    for entry in entries:
      if entry.len == 1 and entry[0].kind == ckBytes:
        let tid = cast[string](entry[0].bytesVal)
        result.add RawResult(status: sxRaised, raisedTypeId: tid)
  except CatchableError as e:
    errors.add "loadSymexRaisedImpl: " & $e.name & ": " & e.msg
    result = @[]

proc toFindingStatus*(s: SymexStatusKind): SymexFindingStatus =
  case s
  of sxSat:     sfSat
  of sxUnsat:   sfUnsat
  of sxUnknown: sfUnknown
  of sxRaised:  sfRaised   ## Phase 15 E2a

# ---- Layer 2 — forAllWithSymexSeeds ----------------------------------------
#
# The engine entry that lifts symex witnesses into the random-PBT
# loop as forced seeds. `symexSeedPhase` is slotted between
# `explicit` (user-pinned regression seeds, no shrinking) and
# `random` (fresh exploration). Seeds that falsify carry their
# choice sequence forward to `shrinkPhase` for minimisation —
# Z3 returns *some* satisfying assignment, not a minimal one.

proc forAllWithSymexSeeds*[T](seeds: seq[seq[ChoiceNode]],
                              s: Strategy[T], prop: proc(x: T),
                              settings: Settings = defaultSettings()
                             ): Report[T] =
  ## Run `prop` against `s` with `seeds` as forced replays before
  ## the random phase. Falsifications discovered from a seed flow
  ## through the same `shrinkPhase → finalizePhase` chain a random
  ## falsification would. Returns the terminal `Report[T]`.
  let phases = @[
    Phase[T](name: "dbReuse",   run: dbReusePhase[T]),
    Phase[T](name: "explicit",  run: explicitExamplesPhase[T]),
    symexSeedPhase[T](seeds),
    Phase[T](name: "random",    run: randomPhase[T]),
    Phase[T](name: "targeted",  run: targetedPhase[T]),
    Phase[T](name: "shrink",    run: shrinkPhase[T]),
    Phase[T](name: "explain",   run: explainPhase[T]),
    Phase[T](name: "finalize",  run: finalizePhase[T]),
  ]
  runForAllPipelineWithPhases(
    inMemoryDatabase(), dbEnabled = false,
    s, prop, settings, toExamples[T](@[]), phases)

# ---- Layer 3 — symexForAll sugar -------------------------------------------
#
# One-call entry: `symexForAll(strategy, fn, db)` discovers all
# auto-targets in `fn`, runs symex per target (Layer 1), seeds the
# random-PBT loop with the SAT witnesses (Layer 2), and threads
# the per-target findings into the resulting Report's
# `symexFindings` field for caller-side auditing.
#
# The SUT proc `fn` plays both roles: it is the property the
# engine runs against random + symex-seeded draws, AND the body
# the IR scan inspects for `symexTarget` / `symexAssert` / `arr[i]`
# / variant-field reads.

macro symexForAll*(s: typed, fn: typed,
                   db: ExampleDatabase,
                   symexSettings: static SymexSettings =
                     defaultSymexSettings(),
                   forAllSettings: Settings = defaultSettings(),
                   excludeTargets: seq[SymexTarget] = @[]
                  ): untyped =
  ## Run symex against every auto-discovered target in `fn`, then
  ## drive the random PBT loop on `s` with the symex-derived
  ## witnesses as forced seeds. The terminal Report carries both
  ## the random-run verdict and the per-target symex findings.
  ##
  ## Returns `untyped` matching the `symexFind` macro shape; the
  ## emitted expression has type `Report[T]` where `T` is the
  ## strategy's element type.
  # Inspect `fn`'s formal-param count at macro time to decide
  # whether to pass `fn` directly as the property (single-arg) or
  # wrap it in a tuple-splatting lambda (multi-arg). The strategy
  # `s`'s element type comes from `getTypeInst(s)[1]` — for
  # `Strategy[T]` that's `T` (`int` for `integers()`,
  # `(int, bool)` for `map(integers(), booleans())`).
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("symexForAll: expected a `proc` symbol for `fn`", fn)
  if impl[2].kind != nnkEmpty:
    error("symexForAll: generic procs are not supported as `fn` " &
          "(witness reconstruction has no type to bind generics to)",
          fn)
  let formalParams = impl[3]
  let nParams = formalParams.len - 1   # [0] is the return type
  let prop =
    if nParams <= 1:
      fn      # single-arg: `fn` IS the property
    else:
      # Multi-arg: emit `proc(t: T) = fn(t[0], t[1], …)`. Type
      # comes from `getTypeInst(s)[1]` — the strategy's element
      # type. Nim verifies field-types vs param-types when the
      # emitted call compiles, so a mismatch surfaces as a typed
      # error at the splat site rather than buried inside the
      # macro.
      let sTypeNode = newCall(bindSym"getTypeInst", s)
      # `sTypeNode` evaluates to a NimNode at *macro-time*; we
      # however need a `typedesc` *at call site* so the wrapper's
      # param type is a real type. Use a type alias via `type X =
      # typeof((default(...)))` — no, simpler — extract the
      # element-type expression directly from `s.getTypeInst` at
      # macro time and splice it as a type.
      let sTypeInst = s.getTypeInst
      if sTypeInst.kind != nnkBracketExpr or not sTypeInst[0].eqIdent("Strategy"):
        error("symexForAll: expected `s` to have type Strategy[T] " &
              "(got " & $sTypeInst.repr & ")", s)
      let elemTy = sTypeInst[1]
      # Reject named-field tuples — `map(s1, s2)` produces an
      # anonymous positional tuple (nnkTupleConstr). Named-field
      # tuple strategies are deferred to a future cycle.
      if elemTy.kind == nnkTupleTy:
        error("symexForAll: named-field tuple strategies are not " &
              "supported as `s` for multi-arg `fn`; use the " &
              "anonymous `map(s1, s2, …)` form", s)
      let tId = genSym(nskParam, "t")
      var splat = newCall(fn)
      for i in 0 ..< nParams:
        splat.add nnkBracketExpr.newTree(tId, newLit(i))
      let lam = newProc(
        params = @[ident"void",
                   newIdentDefs(tId, elemTy)],
        body = splat, procType = nnkLambda)
      lam

  result = quote do:
    block:
      let findings = symexFindAllWitnesses(`fn`, `db`, `symexSettings`,
                                            `excludeTargets`)
      var seeds: seq[seq[ChoiceNode]] = @[]
      for f in findings:
        if f.status == sfSat:
          seeds.add f.witnessChoices
      var report = forAllWithSymexSeeds(seeds, `s`, `prop`,
                                         `forAllSettings`)
      # Drain the sink — picks up Layer 1's deposits PLUS any
      # sfNotApplicable findings symexSeedPhase deposited for
      # shape-mismatched seeds during Layer 2 — into the Report
      # so the audit trail flows back to the caller without a
      # separate `consumeSymexFindings()` call.
      for f in consumeSymexFindings():
        report.symexFindings.add f
      report


# ---- Macro helpers (at module scope so they can recurse cleanly) ----------

proc primTyAndReader(ty: IRType): (string, string) =
  case ty.kind
  of itBool: ("bool", "readBool")
  of itInt:
    if ty.signed:
      case ty.width
      of 8:  ("int8",  "readInt8")
      of 16: ("int16", "readInt16")
      of 32: ("int32", "readInt32")
      of 64: ("int",   "readInt")
      else: ("int", "readInt")
    else:
      case ty.width
      of 8:  ("uint8",  "readUInt8")
      of 16: ("uint16", "readUInt16")
      of 32: ("uint32", "readUInt32")
      of 64: ("uint",   "readUInt")
      else: ("uint", "readUInt")
  of itFloat32: ("float32", "readFloat32")   ## Phase 15 F1
  of itFloat64: ("float",   "readFloat")     ## Phase 15 F1
  else: ("", "")

proc emitTyAndReader*(ty: IRType, path: string, witId: NimNode): (NimNode, NimNode) =
  ## Recursive: returns (Nim type AST, witness-construction expression).
  case ty.kind
  of itUninterp:
    if ty.uninterpName == "__closure":
      # Phase 15 Cluster C (C2a, Invariant 3). A closure as a top-level SUT
      # param/result type is unsupported: a proc value cannot be reconstructed
      # as a concrete witness. Emit a `proc` placeholder + a compile-time
      # `{.warning.}` (classified, not a silent crash). Closures are constructed
      # IN-BODY (C2a) but never reach the witness reader as a top-level type.
      let placeholder = quote do:
        block:
          {.warning: "symex: a closure as a top-level SUT param/result type " &
                     "is unsupported; witness rendering yields a nil proc " &
                     "placeholder (Phase 15 Cluster C / Invariant 3).".}
          (proc (): void = discard)
      return (nnkProcTy.newTree(nnkFormalParams.newTree(newEmptyNode()),
                                newEmptyNode()), placeholder)
    raise newException(ValueError,
      "emitTyAndReader(itUninterp): opaque-ref witness reader lands with cluster E")
  of itDistinct:
    # Phase 15 G4 (Breadth-CRIT-1). A `distinct T` param renders through the
    # eject-then-base-reader chain: extract the BASE value at the SAME path
    # (the runtime's `extractFromSymVal(svDistinct)` populated it from
    # `eject_T(distinctConst)`), then wrap it in the distinct type's
    # converter `DistinctName(baseValue)`. Without this the distinct param
    # would produce a silent empty reader.
    let (_, baseReader) = emitTyAndReader(ty.distinctBase, path, witId)
    (ident(ty.distinctName), newCall(ident(ty.distinctName), baseReader))
  of itBool, itInt, itFloat32, itFloat64:
    let (tyName, readerName) = primTyAndReader(ty)
    (ident(tyName), newCall(ident(readerName), witId, newLit(path)))
  of itTuple:
    if ty.objectName.len > 0:
      # Nominal object. For variant objects (heuristic: any of the
      # later fields would conflict with earlier branches), Nim's
      # constructor rejects per-field initialisation. Phase 5+ ships
      # a stub that returns `default(Object)` for variant cases —
      # downstream user code can examine `r.status` to verify
      # reachability. Variant-aware witness reconstruction is a
      # follow-up (#141 phase 2).
      let objTyId = ident(ty.objectName)
      # Check for variant: the discriminator name on the parsed
      # object is conventionally "kind" + fields after position 0
      # that would be ambiguous to construct all at once.
      let isLikelyVariant = ty.fields.len > 2 and ty.fieldNames.len > 0 and
                            ty.fieldNames[0] == "kind"
      if isLikelyVariant:
        (objTyId, newCall(ident("default"), objTyId))
      else:
        var objVal = newTree(nnkObjConstr, objTyId)
        for i, fty in ty.fields:
          let suffix = "." & ty.fieldNames[i]
          let (_, sv) = emitTyAndReader(fty, path & suffix, witId)
          objVal.add newTree(nnkExprColonExpr,
            ident(ty.fieldNames[i]), sv)
        (objTyId, objVal)
    else:
      # Anonymous: nnkTupleConstr (positional) or nnkTupleTy (named).
      let named = ty.fieldNames.len > 0 and ty.fieldNames[0].len > 0
      var subTy = if named: newTree(nnkTupleTy) else: newTree(nnkTupleConstr)
      var subVal = newTree(nnkTupleConstr)
      for i, fty in ty.fields:
        let suffix = if ty.fieldNames[i].len > 0: "." & ty.fieldNames[i]
                     else: "." & $i
        let (st, sv) = emitTyAndReader(fty, path & suffix, witId)
        if named:
          subTy.add newTree(nnkIdentDefs,
            ident(ty.fieldNames[i]), st, newEmptyNode())
          subVal.add newTree(nnkExprColonExpr,
            ident(ty.fieldNames[i]), sv)
        else:
          subTy.add st
          subVal.add sv
      (subTy, subVal)
  of itArray:
    let (elemTyNode, _) = emitTyAndReader(ty.elemTy, path & ".0", witId)
    let arrTy = newTree(nnkBracketExpr,
      ident("array"), newLit(ty.size), elemTyNode)
    var arrLit = newTree(nnkBracket)
    for i in 0 ..< ty.size:
      let (_, sv) = emitTyAndReader(ty.elemTy, path & "." & $i, witId)
      arrLit.add sv
    (arrTy, arrLit)
  of itString:
    (ident("string"), newCall(ident("readString"), witId, newLit(path)))
  of itSeq:
    # Phase 5 cycle 1: only seq[int] tested; specialised reader.
    if ty.seqElemTy.kind == itInt and ty.seqElemTy.signed and
       ty.seqElemTy.width == 64:
      (newTree(nnkBracketExpr, ident("seq"), ident("int")),
       newCall(ident("readSeqInt"), witId, newLit(path)))
    elif ty.seqElemTy.kind == itFloat64:   ## Phase 15 F9b
      (newTree(nnkBracketExpr, ident("seq"), ident("float")),
       newCall(ident("readSeqFloat64"), witId, newLit(path)))
    elif ty.seqElemTy.kind == itFloat32:   ## Phase 15 F9b
      (newTree(nnkBracketExpr, ident("seq"), ident("float32")),
       newCall(ident("readSeqFloat32"), witId, newLit(path)))
    else:
      error("symex Phase 5: seq witness reader for " & $ty &
            " not yet implemented")
  of itTable:
    # Phase 5 cycle 5: Table[string, int] only.
    if ty.tabKeyTy.kind == itString and
       ty.tabValTy.kind == itInt and ty.tabValTy.signed and
       ty.tabValTy.width == 64:
      let tabTy = newTree(nnkBracketExpr,
        ident("Table"), ident("string"), ident("int"))
      (tabTy, newCall(ident("readTableStrInt"), witId, newLit(path)))
    else:
      error("symex Phase 5: only Table[string, int] supported (got " &
            $ty & ")")
  of itSet:
    if ty.setElemTy.kind == itInt and ty.setElemTy.signed and
       ty.setElemTy.width == 64:
      let setTy = newTree(nnkBracketExpr, ident("HashSet"), ident("int"))
      (setTy, newCall(ident("readSetInt"), witId, newLit(path)))
    else:
      error("symex Phase 5: only HashSet[int] supported")
  of itVariant:
    # Phase 11 cycle 7 + plain-field sharing (post-cycle-12) —
    # construct the variant on the arm Z3 picked. Witness layout
    # written by `extractFromSymVal`:
    #   <path>.<discName>            discriminator value
    #   <path>.<plainFieldName>      plain (shared) field values
    #   <path>.@<tagOrdinal>.<field> arm-specific field values
    # Plain fields appear in every arm's constructor at their
    # shared witness path — so the same value is read from the
    # same path in every case branch, which Nim's runtime sees as
    # one shared symbolic value (matching Nim's variant memory
    # layout where plain fields are always-present and shared).
    let objTyId = ident(ty.vObjectName)
    let discPath = path & "." & ty.vDiscName
    let (discTyId, discReaderExpr) =
      emitTyAndReader(ty.vDiscTy, discPath, witId)
    var caseStmt = newTree(nnkCaseStmt, discReaderExpr)
    # Identify the else arm (if any). Phase 14 cycle A2 (ADR-0003 D2):
    # the else arm cannot be rendered as a static-disc nnkObjConstr
    # because its discriminator is dynamic. Render it via
    # `block: var w: V; w.kind = readDisc; w.<plain> = ...; w.<armF> = ...; w`
    # which Nim accepts since each assignment respects the at-that-
    # moment arm shape.
    var elseArm: VariantArm
    var hasElse = false
    for arm in ty.vArms:
      if arm.isElse: elseArm = arm; hasElse = true
    for arm in ty.vArms:
      if arm.isElse: continue
      let tagLit = newCall(discTyId, newLit(arm.tagOrdinal))
      var ctor = newTree(nnkObjConstr, objTyId)
      # Plain fields first (in source order).
      for i, fname in ty.vPlainFieldNames:
        let fty = ty.vPlainFieldTypes[i]
        let plainPath = path & "." & fname
        let (_, fReader) = emitTyAndReader(fty, plainPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      # Discriminator literal. Non-enum discs (Phase 14 A3) carry an
      # empty tagName — Nim accepts an int literal for `range`-typed
      # fields, so fall back to `newLit(tagOrdinal)`.
      let discValExpr =
        if arm.tagName.len > 0: ident(arm.tagName)
        else: newLit(arm.tagOrdinal)
      ctor.add nnkExprColonExpr.newTree(
        ident(ty.vDiscName), discValExpr)
      # Arm-specific fields.
      for j, fname in arm.fieldNames:
        let fty = arm.fieldTypes[j]
        let armPath = path & ".@" & $arm.tagOrdinal & "." & fname
        let (_, fReader) = emitTyAndReader(fty, armPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      caseStmt.add nnkOfBranch.newTree(tagLit, ctor)
    if hasElse:
      # For each disc-enum ordinal NOT covered by a non-else arm,
      # emit one `of <tagName>:` branch with a static discriminator
      # literal. Static-disc construction sidesteps the runtime
      # discriminant transition check that breaks the `var w` path.
      # `vDiscTags` carries the enum's full (name, ord) domain so we
      # have a concrete Nim identifier for each else-covered value.
      var nonElseOrds: seq[int]
      for arm in ty.vArms:
        if not arm.isElse: nonElseOrds.add arm.tagOrdinal
      for dt in ty.vDiscTags:
        if dt.ord in nonElseOrds: continue
        let tagLit = newCall(discTyId, newLit(dt.ord))
        var ctor = newTree(nnkObjConstr, objTyId)
        for i, fname in ty.vPlainFieldNames:
          let (_, fReader) = emitTyAndReader(
            ty.vPlainFieldTypes[i], path & "." & fname, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        ctor.add nnkExprColonExpr.newTree(
          ident(ty.vDiscName), ident(dt.name))
        for j, fname in elseArm.fieldNames:
          let armPath = path & ".@" & $elseArm.tagOrdinal & "." & fname
          let (_, fReader) = emitTyAndReader(
            elseArm.fieldTypes[j], armPath, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        caseStmt.add nnkOfBranch.newTree(tagLit, ctor)
    caseStmt.add nnkElse.newTree(newCall(ident"default", objTyId))
    (objTyId, caseStmt)
  of itMultiVariant:
    # Phase 14 cycle A1d per ADR-0003 D1. Emit nested case
    # statements — one per axis, outer to inner — and at the
    # deepest level construct the object with plain fields + each
    # axis's chosen disc + that axis's active-arm fields. Witness
    # paths must match what `extractFromSymVal` writes for
    # svMultiVariant (runtime.nim ~1364-1374):
    #   <path>.<plainName>                         plain (shared)
    #   <path>.<discName>                          axis discriminator
    #   <path>.<discName>.@<tagOrdinal>.<fname>    arm-specific
    # `fields(w)` on the constructed object iterates active-arm
    # order: plain..., axis1, arm1-fields, axis2, arm2-fields...
    # which matches `renderAsChoices`'s iteration contract.
    let objTyId = ident(ty.mvObjectName)
    type AxisBind = tuple[
      discName: string,
      tagName: string,
      armFieldNames: seq[string],
      armFieldReaders: seq[NimNode]]
    proc emitMVBranch(axisIdx: int,
                      chosen: seq[AxisBind]): NimNode =
      if axisIdx == ty.mvAxes.len:
        var ctor = newTree(nnkObjConstr, objTyId)
        for i, fname in ty.mvPlainFieldNames:
          let (_, fReader) = emitTyAndReader(
            ty.mvPlainFieldTypes[i], path & "." & fname, witId)
          ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
        for ab in chosen:
          ctor.add nnkExprColonExpr.newTree(
            ident(ab.discName), ident(ab.tagName))
          for j, fn in ab.armFieldNames:
            ctor.add nnkExprColonExpr.newTree(
              ident(fn), ab.armFieldReaders[j])
        return ctor
      let ax = ty.mvAxes[axisIdx]
      let discPath = path & "." & ax.discName
      let (discTyId, discReaderExpr) =
        emitTyAndReader(ax.discTy, discPath, witId)
      var caseStmt = newTree(nnkCaseStmt, discReaderExpr)
      for arm in ax.arms:
        let tagLit = newCall(discTyId, newLit(arm.tagOrdinal))
        var armReaders: seq[NimNode]
        for j, fn in arm.fieldNames:
          let armPath = path & "." & ax.discName &
                        ".@" & $arm.tagOrdinal & "." & fn
          let (_, fr) = emitTyAndReader(arm.fieldTypes[j], armPath, witId)
          armReaders.add fr
        let body = emitMVBranch(axisIdx + 1, chosen & @[
          (discName: ax.discName, tagName: arm.tagName,
           armFieldNames: arm.fieldNames, armFieldReaders: armReaders)])
        caseStmt.add nnkOfBranch.newTree(tagLit, body)
      # Else covers any out-of-set disc value; same defensive
      # fallback as itVariant (line 599).
      caseStmt.add nnkElse.newTree(newCall(ident"default", objTyId))
      caseStmt
    (objTyId, emitMVBranch(0, @[]))

# ---- Body markers -----------------------------------------------------------

## Body markers are procs (not templates) so semcheck doesn't elide
## the call site before the symex parser sees it. The parser
## recognizes the call by callee name; outside symex these run as
## ordinary procs whose body provides the dual-mode semantics.

# ---- Extension pragma -------------------------------------------------------

## Phase 9 user-extension hook. Attach to a proc the walker should
## not enter: `proc readSensor(): int {.symexOpaque.} = ...`.
## Inside symex, calls to the proc become fresh symbolic returns
## and the path is marked uncertain (same semantics as built-in
## opaque-effectful procs like `echo`). Outside symex the pragma
## is a no-op and the proc executes normally.
template symexOpaque*() {.pragma.}

proc symexTarget*(name: string) {.inline.} =
  ## Marker: a coverage target for `symexFind(..., tLabel(name))`.
  ## Outside symex, calling this is a no-op — unless an
  ## `assertCoveredBy` capture is active on this thread, in which
  ## case `name` is recorded as hit. Phase 7.
  symexCaptureRecord(name)

proc symexAssert*(cond: bool) {.inline.} =
  ## Marker: an invariant the user claims always holds. Outside
  ## symex, asserted at runtime via `doAssert` so random PBT also
  ## catches violations. Inside symex, the parser maps this to an
  ## IR node the walker treats as a fork point for
  ## `tAssertionViolation` searches.
  doAssert cond, "symexAssert violated"

proc symexAssume*(cond: bool) {.inline.} =
  ## Marker: a precondition restricting the input domain. Phase 1
  ## ships with no-op outside symex (the richer "early-return on
  ## violation" semantics is deferred until needed — `symexAssume`'s
  ## body markers in Phase 1 are recognized by the parser but don't
  ## yet affect the SUT's normal-run behavior). Inside symex, the
  ## walker conjoins `cond` into the path condition.
  discard cond

# ---- The driver macro -------------------------------------------------------

macro symexFind*(fn: typed,
                 target: static SymexTarget,
                 settings: static SymexSettings = defaultSymexSettings()
                ): untyped =
  ## Symbolically execute `fn` searching for an input that reaches `target`.
  ## Returns `SymexResult[ParamTuple]` where `ParamTuple` is the proc's
  ## parameter list as a Nim tuple.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("symexFind: expected a `proc` symbol", fn)
  let parsed = parseProc(impl, settings.maxInstantiationsPerProc)

  # Build the tuple type and witness-construction tuple. We genSym a
  # local name for the RawWitness so the witness-constructor calls
  # share an identity-equal NimNode with the `let` that binds it.
  let witId = genSym(nskLet, "rawWit")
  var tupleTy = newTree(nnkTupleConstr)
  var witnessTup = newTree(nnkTupleConstr)
  for p in parsed.params:
    let (pTy, pVal) = emitTyAndReader(p.ty, p.name, witId)
    tupleTy.add pTy
    witnessTup.add pVal

  # `(int,)` is a syntactic 1-tuple; nnkTupleConstr with one child
  # renders correctly for both the type and the value.

  let bodyExpr   = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode
  let procsExpr  = parsed.procsNimNode
  let uxhExpr    = parsed.userExnHierarchyNimNode  ## Phase 15 E4a
  let peExpr     = parsed.parseErrorsNimNode       ## Phase 15 G1c

  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`,
                              userExnHierarchy: `uxhExpr`,
                              parseErrors: `peExpr`)
      let raw = runSymex(prog, `target`, `settings`)
      case raw.status
      of sxSat:
        let `witId` = raw.witness
        SymexResult[`tupleTy`](status: sxSat, witness: `witnessTup`,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               fromCache: false)
      of sxUnsat:
        SymexResult[`tupleTy`](status: sxUnsat,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               fromCache: false)
      of sxUnknown:
        SymexResult[`tupleTy`](status: sxUnknown,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               fromCache: false)
      of sxRaised:
        # Phase 15 E2b. The walker reached a reachable `raise`; surface the
        # raised type id PLUS the reconstructed witness that reaches it (solved
        # from the raise-path condition). `witId` binds `raw.raisedWitness` so
        # the shared `witnessTup` reader reconstructs the SUT input tuple exactly
        # as on the `sxSat` path.
        let `witId` = raw.raisedWitness
        SymexResult[`tupleTy`](status: sxRaised,
                               raisedTypeId: raw.raisedTypeId,
                               raisedWitness: `witnessTup`,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               fromCache: false)

# ---- assertCoveredBy --------------------------------------------------------

macro assertCoveredBy*(fn: typed,
                       target: static SymexTarget,
                       testFn: typed = nil,
                       settings: static SymexSettings = defaultSymexSettings()
                      ): untyped =
  ## Prove that `testFn`, invoked on the symex witness for `target`
  ## inside `fn`, actually exercises that target. Raises
  ## `AssertionDefect` when symex found a witness (`sxSat`) but the
  ## testFn run did not observe the target. UNSAT vacuously passes;
  ## UNKNOWN raises (cycle 4 will gate this on a setting).
  ##
  ## `testFn` defaults to `fn` itself — the common shape where the
  ## same code under symex is the same code under random PBT.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("assertCoveredBy: expected a `proc` symbol", fn)
  let parsed = parseProc(impl, settings.maxInstantiationsPerProc)

  let actualTestFn =
    if testFn.kind == nnkNilLit: fn else: testFn

  # Splat the witness tuple into testFn's positional params.
  # Phase 14 A7b: wrap each param in a fresh `var` local before the
  # call so `var T` parameters receive an addressable lvalue.
  # Pre-A7b this emitted `testFn(wit[0], wit[1], ...)` which fails
  # to compile for SUTs that take any `var T`. The wrapping is
  # zero-cost for non-var params and idiomatic for var params.
  let witId = genSym(nskLet, "wit")
  var splatPreamble = newStmtList()
  var splat = newCall(actualTestFn)
  for i in 0 ..< parsed.params.len:
    let pvar = genSym(nskVar, "pvar" & $i)
    splatPreamble.add newTree(nnkVarSection,
      newIdentDefs(pvar, newEmptyNode(),
                   nnkBracketExpr.newTree(witId, newLit(i))))
    splat.add pvar
  let splatBlock = newStmtList(splatPreamble, splat)

  # gensym shared identifiers used across the cover-check sub-quote
  # and the main quote — quote-do hygiene would otherwise mint
  # fresh symbols per block.
  let hitsId           = genSym(nskLet, "hits")
  let assertionRaisedId = genSym(nskVar, "assertionRaised")
  let indexRaisedId     = genSym(nskVar, "indexRaised")
  let fieldRaisedId     = genSym(nskVar, "fieldRaised")
  let anyRaisedId       = genSym(nskVar, "anyRaised")        ## Phase 15 E2a

  # We dispatch on `target.kind` at macro time so that only the
  # branch-appropriate field is referenced in the emitted code.
  # Splicing a `static SymexTarget` of a non-stkLabel kind via
  # quote-do would otherwise force Nim to materialise an
  # nnkObjConstr that names every field — but a variant-object's
  # `label` field is invalid under `stkAssertionViolation`.
  let coveredExpr =
    case target.kind
    of stkLabel:
      let labelLit = newLit(target.label)
      quote do: (`labelLit` in `hitsId`)
    of stkAssertionViolation:
      quote do: `assertionRaisedId`
    of stkIndexError:
      quote do: `indexRaisedId`
    of stkFieldDefect:
      quote do: `fieldRaisedId`
    of stkRaisedExn:
      quote do: `anyRaisedId`   ## Phase 15 E2a: covered iff the SUT raised
  let failMsg =
    case target.kind
    of stkLabel:
      newLit("assertCoveredBy: testFn did not reach symexTarget(\"" &
             target.label & "\") on the symex witness")
    of stkAssertionViolation:
      newLit("assertCoveredBy: testFn did not raise AssertionDefect " &
             "on the symex witness (target was tAssertionViolation)")
    of stkIndexError:
      newLit("assertCoveredBy: testFn did not raise IndexDefect " &
             "on the symex witness (target was tIndexError)")
    of stkFieldDefect:
      newLit("assertCoveredBy: testFn did not raise FieldDefect " &
             "on the symex witness (target was tFieldDefect)")
    of stkRaisedExn:
      newLit("assertCoveredBy: testFn did not raise an exception " &
             "on the symex witness (target was tRaisedExn)")
  let targetDescLit = newLit(describeTarget(target))

  # Rebuild the target node from its kind so the spliced AST is
  # always well-formed for the variant.
  let targetExpr =
    case target.kind
    of stkLabel:           newCall(bindSym"tLabel", newLit(target.label))
    of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
    of stkIndexError:      newCall(bindSym"tIndexError")
    of stkFieldDefect:     newCall(bindSym"tFieldDefect")
    of stkRaisedExn:       newCall(bindSym"tRaisedExn", newLit(target.typeFilter))

  result = quote do:
    block:
      let r = symexFind(`fn`, `targetExpr`, `settings`)
      case r.status
      of sxSat:
        let `witId` = r.witness
        symexCaptureBegin()
        var `assertionRaisedId` = false
        var `indexRaisedId` = false
        var `fieldRaisedId` = false
        var `anyRaisedId` = false   ## Phase 15 E2a: any exception raised
        try:
          `splatBlock`
        except AssertionDefect:
          `assertionRaisedId` = true
          `anyRaisedId` = true
        except IndexDefect:
          `indexRaisedId` = true
          `anyRaisedId` = true
        except FieldDefect:
          `fieldRaisedId` = true
          `anyRaisedId` = true
        except CatchableError:
          `anyRaisedId` = true
        let `hitsId` = symexCaptureEnd()
        let covered = `coveredExpr`
        recordSymexFinding(SymexFinding(
          targetDesc:     `targetDescLit`,
          status:         sfSat,
          covered:        covered,
          witnessChoices: renderAsChoices(`witId`),
          z3Version:      z3FullVersion()))
        if not covered:
          raise newException(AssertionDefect, `failMsg`)
      of sxUnsat:
        recordSymexFinding(SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnsat, covered: true,
          z3Version:  z3FullVersion()))
        discard  # vacuous pass
      of sxUnknown:
        recordSymexFinding(SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnknown, covered: false,
          z3Version:  z3FullVersion()))
        let s: SymexSettings = `settings`
        if not s.acceptUnknownAsCovered:
          raise newException(AssertionDefect,
            "assertCoveredBy: symex returned UNKNOWN; cannot prove " &
            "coverage (set acceptUnknownAsCovered = true to downgrade)")
      of sxRaised:
        # Phase 15 E2a (STRUCTURAL). The walker found a reachable raise but
        # produced no witness yet (E2b adds path-constrained witnesses), so
        # there is no input to replay through `testFn`. Record the finding;
        # on a non-`stkRaisedExn` target the raised type is surfaced in the
        # diagnostic. No witness-replay coverage check in E2a.
        recordSymexFinding(SymexFinding(
          targetDesc: `targetDescLit` & " raised(" & r.raisedTypeId & ")",
          status: sfRaised, covered: false,
          z3Version:  z3FullVersion()))

macro assertCoveredBy*(fn: typed,
                       targets: static openArray[SymexTarget],
                       testFn: typed = nil,
                       settings: static SymexSettings = defaultSymexSettings()
                      ): untyped =
  ## Multi-target form: prove `testFn` covers every target. Each
  ## target is dispatched through the single-target `assertCoveredBy`;
  ## failures are accumulated and reported as one aggregate message.
  let failuresId = genSym(nskVar, "failures")
  result = newStmtList()
  result.add quote do:
    var `failuresId`: seq[string] = @[]
  for t in targets:
    let tNode =
      case t.kind
      of stkLabel:              newCall(bindSym"tLabel", newLit(t.label))
      of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
      of stkIndexError:         newCall(bindSym"tIndexError")
      of stkFieldDefect:        newCall(bindSym"tFieldDefect")
      of stkRaisedExn:          newCall(bindSym"tRaisedExn", newLit(t.typeFilter))
    let settingsNode = newLit(settings)
    let inner = newCall(ident"assertCoveredBy", fn, tNode, testFn, settingsNode)
    result.add quote do:
      try:
        `inner`
      except AssertionDefect as e:
        `failuresId`.add e.msg
  let totalLit = newLit(targets.len)
  result.add quote do:
    if `failuresId`.len > 0:
      var msg = "assertCoveredBy (multi): " & $`failuresId`.len &
                " of " & $`totalLit` & " targets uncovered:"
      for f in `failuresId`:
        msg.add "\n  - " & f
      raise newException(AssertionDefect, msg)
  result = nnkBlockStmt.newTree(newEmptyNode(), result)

# ---- Macro forms for the content-addressed DB API ---------------------------
#
# These macros parse the typed SUT to a SymexProgram (so the IR hash
# in the cache key reflects the same IR the walker will see), then
# delegate to the runtime impl. The pure (testable) part of the key
# derivation lives in proptest/smt/canonicalize.

proc rebuildTargetNode(target: SymexTarget): NimNode =
  ## Macro-time fresh constructor call for `target`. Splicing a
  ## `static SymexTarget` of a non-stkLabel kind directly via
  ## `quote do` triggers Nim to materialise an nnkObjConstr that
  ## names every field — invalid for variants. Rebuilding via the
  ## `t*` constructors is always well-formed.
  case target.kind
  of stkLabel:              newCall(bindSym"tLabel", newLit(target.label))
  of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
  of stkIndexError:         newCall(bindSym"tIndexError")
  of stkFieldDefect:        newCall(bindSym"tFieldDefect")
  of stkRaisedExn:          newCall(bindSym"tRaisedExn", newLit(target.typeFilter))

macro symexCacheKeyForFn*(fn: typed,
                           target: static SymexTarget,
                           settings: static SymexSettings =
                             defaultSymexSettings()
                          ): string =
  ## Phase 13 cycle 2 — test helper. Emits a runtime expression
  ## that evaluates to the bare content-addressed key (no
  ## `:sat`/`:unsat`/`:unk` suffix) for `fn` + `target` + `settings`
  ## under the current Z3 / Nim / walker / rendering versions.
  ##
  ## Tests use this to probe `db.loadPrimary` directly without
  ## reconstructing `SymexProgram` by hand, while still pinning the
  ## suffix participation contract. NOT intended for production
  ## consumers — they should use `saveSymexWitness` /
  ## `loadSymexWitnesses` which encapsulate the suffix.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("symexCacheKeyForFn: expected a `proc` symbol", fn)
  let parsed = parseProc(impl, settings.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      symexCacheKey(prog, `targetExpr`, `settings`,
                    z3Version        = z3FullVersion(),
                    nimVersion       = NimVersion,
                    walkerVersion    = symexWalkerVersion,
                    renderingVersion = renderAsChoicesVersion)

macro saveSymexWitness*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings,
                        finding: SymexFinding,
                        maxEntries: int = 64): untyped =
  ## Persist `finding`'s witness under the content-addressed cache
  ## key derived from `fn`'s IR, the target, the witness-relevant
  ## subset of `settings`, and the current Z3/Nim/walker versions.
  ## Non-Sat findings are skipped.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("saveSymexWitness: expected a `proc` symbol", fn)
  let parsed = parseProc(impl, settings.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      saveSymexWitnessImpl(`db`, prog, `targetExpr`, `settings`,
                            `finding`, dbErrors, `maxEntries`)
      # `dbErrors` is captured in this scope so the macro emission
      # type-checks; Phase 13 cycle 7 wires the engine flow that
      # threads these errors into Report.dbErrors. Until then the
      # public macro form discards them — matching the pre-RFC
      # behavior of silently swallowing rare DB failures.

macro loadSymexWitnesses*(db: ExampleDatabase, fn: typed,
                          target: static SymexTarget,
                          settings: static SymexSettings
                         ): untyped =
  ## Load previously-persisted witnesses for *exactly* this
  ## SUT/target/settings/Z3/Nim/walker combination. Mismatched
  ## key → empty seq.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("loadSymexWitnesses: expected a `proc` symbol", fn)
  let parsed = parseProc(impl, settings.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      loadSymexWitnessesImpl(`db`, prog, `targetExpr`, `settings`, dbErrors)

# ---- Verdict macro forms (Phase 13 cycle 10) -------------------------------
#
# Mirror `saveSymexWitness` / `loadSymexWitnesses` for non-SAT
# verdicts. `status: SymexFindingStatus` is a runtime value, not
# static — the suffix (`:unsat` vs `:unk`) is dispatched at
# runtime inside `saveSymexVerdictImpl`. Error accumulation is
# internal and discarded (the user-facing macro doesn't carry a
# Report); callers wanting error reporting use the `*Impl` procs
# directly with their own `errors` seq.

macro saveSymexVerdict*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings,
                        status: SymexFindingStatus): untyped =
  ## Persist a non-SAT verdict (sfUnsat / sfUnknown) for `fn`'s
  ## content-addressed key. No-op for sfSat (use
  ## `saveSymexWitness`) and sfNotApplicable.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("saveSymexVerdict: expected a `proc` symbol", fn)
  let parsed = parseProc(impl, settings.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      saveSymexVerdictImpl(`db`, prog, `targetExpr`, `settings`,
                            `status`, dbErrors)

macro loadSymexVerdict*(db: ExampleDatabase, fn: typed,
                        target: static SymexTarget,
                        settings: static SymexSettings
                       ): untyped =
  ## Load a previously-persisted non-SAT verdict for `fn`'s
  ## content-addressed key. Checks `:unsat` then `:unk`
  ## (UNSAT-first load-order tie-break). Returns
  ## `Option[SymexFindingStatus]`.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("loadSymexVerdict: expected a `proc` symbol", fn)
  let parsed = parseProc(impl, settings.maxInstantiationsPerProc)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      var dbErrors {.used.}: seq[string] = @[]
      loadSymexVerdictImpl(`db`, prog, `targetExpr`, `settings`, dbErrors)

# ---- Layer 1 — symexFindAllWitnesses ---------------------------------------
#
# Phase 12 cycle 7. The Layer-1 primitive: given a SUT and an
# `ExampleDatabase`, run symex against every auto-discovered target
# in the SUT's IR and return one `SymexFinding` per. Each finding
# is also deposited via `recordSymexFinding` so the engine's
# `finalizePhase` later drains them into `Report.symexFindings`.
#
# Cycle 7 covers `tLabel` only — `symexTarget("name")` markers
# extracted via `irCollectLabels` (cycle 4) walking transitively
# through `parseProc`'s callee table. Cycles 8-10 add the three
# auto-included defect targets. Cycle 11 adds `excludeTargets`.
# Cycle 12 wires the DB cache.

macro symexFindAllWitnesses*(fn: typed,
                              db: ExampleDatabase,
                              symexSettings: static SymexSettings =
                                defaultSymexSettings(),
                              # Constructor-form list of targets to suppress
                              # from auto-discovery. Comparison is by
                              # `SymexTargetKind` (label-by-name suppression
                              # is out of scope). Not `static` because Nim 2.2
                              # rejects every viable default expression for a
                              # `static seq[T]` parameter; instead the macro
                              # inspects the call-site AST directly via the
                              # NimNode it receives.
                              excludeTargets: seq[SymexTarget] = @[]
                             ): seq[SymexFinding] =
  ## Run symex against every auto-discovered target in `fn`. Returns
  ## one `SymexFinding` per target, in IR-traversal order; each
  ## finding is also recorded into the per-thread sink so it flows
  ## into `Report.symexFindings` at end-of-run.
  let impl = fn.getImpl
  if impl.kind != nnkProcDef:
    error("symexFindAllWitnesses: expected a `proc` symbol", fn)
  # Phase 14 A7b: the Phase-12 `var T` guard is lifted. Witness
  # semantics: the walker reports the INITIAL value of each `var`
  # param (via `initialEnv`), which the test runtime invokes the
  # SUT with. Mutations are walker-internal symbolic operations
  # with no caller-side identity tracking.
  let parsed = parseProc(impl, symexSettings.maxInstantiationsPerProc)

  let labels = irCollectLabels(parsed.body, parsed.procs)

  # Macro-time filter set: any target kind appearing in
  # `excludeTargets` is dropped, regardless of `label` (per plan:
  # comparison is by kind). Label-by-name suppression is
  # out-of-scope for v1 — the deferrals table tracks it.
  # `excludeTargets` is a NimNode at macro time (the call-site
  # expression). The user writes one of:
  #   * `@[tIndexError(), tLabel("x")]`   — nnkPrefix("@", nnkBracket(...))
  #   * the default `@[]`                  — empty bracket
  # We inspect the AST and translate each constructor call to the
  # corresponding `SymexTargetKind`. Comparison is by kind per the
  # plan: any call to `tIndexError` excludes ALL tIndexError
  # auto-discoveries; any call to `tLabel(...)` excludes ALL labels
  # regardless of name. Label-by-name suppression is a documented
  # deferral.
  # Phase 14 B67: `tLabel("name")` excludes ONLY the named label
  # (previously excluded ALL labels regardless of name).
  # `tAssertionViolation/tIndexError/tFieldDefect` continue to
  # exclude by kind. This is a documented breaking change for
  # users who relied on `tLabel(...)` to mean "all labels."
  var excludedKinds: set[SymexTargetKind]
  var excludedLabels: seq[string]
  proc collectKinds(n: NimNode) =
    case n.kind
    of nnkPrefix:
      if n.len == 2: collectKinds(n[1])
    of nnkBracket:
      for child in n: collectKinds(child)
    of nnkCall, nnkCommand:
      if n.len >= 1 and n[0].kind in {nnkIdent, nnkSym}:
        case n[0].strVal
        of "tLabel":
          if n.len >= 2 and n[1].kind in {nnkStrLit..nnkTripleStrLit}:
            excludedLabels.add n[1].strVal
        of "tAssertionViolation": excludedKinds.incl stkAssertionViolation
        of "tIndexError":         excludedKinds.incl stkIndexError
        of "tFieldDefect":        excludedKinds.incl stkFieldDefect
        of "tRaisedExn":          excludedKinds.incl stkRaisedExn
        else: discard
    else: discard
  collectKinds(excludeTargets)

  # Build the witness-renderer for this proc's parameter tuple
  # exactly as `symexFind` does — the witness reconstruction must
  # produce a typed Nim value so `renderAsChoices` can serialise it
  # into the choice IR for the example DB and report.
  let witId = genSym(nskLet, "rawWit")
  var tupleTy = newTree(nnkTupleConstr)
  var witnessTup = newTree(nnkTupleConstr)
  for p in parsed.params:
    let (pTy, pVal) = emitTyAndReader(p.ty, p.name, witId)
    tupleTy.add pTy
    witnessTup.add pVal

  let bodyExpr   = parsed.bodyNimNode
  let paramsExpr = parsed.paramsNimNode
  let procsExpr  = parsed.procsNimNode
  let peExpr     = parsed.parseErrorsNimNode   ## Phase 15 G1c

  # Compile-time list of target constructors. We materialise them
  # at runtime as a `seq[SymexTarget]` so the runtime loop is a
  # single straight-line walk regardless of label count.
  # Build the runtime target list as a typed `newSeq[SymexTarget]()`
  # plus per-target `.add` calls. Avoids the "cannot infer element
  # type" trap when the SUT exposes zero targets — that case
  # (which cycle 18 promotes to `sfNotApplicable`) still needs to
  # compile cleanly.
  let tsId = genSym(nskVar, "targets")
  var targetsBuild = newStmtList()
  targetsBuild.add quote do:
    var `tsId` = newSeq[SymexTarget]()
  var nTargets = 0
  # Phase 14 B67: per-label exclusion.
  for lbl in labels:
    if lbl in excludedLabels: continue
    let call = newCall(bindSym"tLabel", newLit(lbl))
    targetsBuild.add newCall(bindSym"add", tsId, call)
    inc nTargets
  if stkAssertionViolation notin excludedKinds and
     irHasAssert(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tAssertionViolation"))
    inc nTargets
  if stkIndexError notin excludedKinds and
     irHasIndex(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tIndexError"))
    inc nTargets
  if stkFieldDefect notin excludedKinds and
     irHasVariantField(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tFieldDefect"))
    inc nTargets
  # Phase 15 E6. A raw `assert cond, msg` lowers to an implicit
  # `AssertionDefect` raise; auto-discover it as a `tRaisedExn("AssertionDefect")`
  # target so the reachable defect surfaces in `Report.symexFindings`.
  if stkRaisedExn notin excludedKinds and
     irHasAssertDefect(parsed.body, parsed.procs):
    targetsBuild.add newCall(bindSym"add",
      tsId, newCall(bindSym"tRaisedExn", newLit("AssertionDefect")))
    inc nTargets

  # Zero-targets fallback: the SUT has no symex-relevant constructs
  # (no markers, no asserts, no indexing, no variant arm-field
  # reads) — or `excludeTargets` ruled them all out. Skip Z3
  # entirely; deposit one `sfNotApplicable` audit entry so the
  # eventual Report still carries an honest "we looked, there was
  # nothing to look at" record. The runtime loop falls through
  # cleanly because `tsId` is empty.
  # Zero-targets fallback assembled at macro time: when nothing
  # was discovered (after `excludeTargets` filtering), the macro
  # emits a single `sfNotApplicable` deposit and skips the entire
  # `runSymex` loop — Z3 isn't called, the per-target cache isn't
  # touched. Otherwise the emitted body iterates `tsId` and runs
  # cache-then-symex per target.
  # gensym shared between the outer prog-binding quote and the
  # inner runtime body so they refer to the same NimNode (each
  # `quote do:` mints its own hygienic identifiers otherwise).
  let progId     = genSym(nskLet, "prog")
  let findingsId = genSym(nskVar, "findings")
  let dbErrorsId = genSym(nskVar, "dbErrors")
  let runtimeBody =
    if nTargets == 0:
      quote do:
        let noTargetsFinding = SymexFinding(
          targetDesc: "no-targets-discovered",
          status:     sfNotApplicable,
          covered:    false,
          z3Version:  z3FullVersion())
        recordSymexFinding(noTargetsFinding)
        `findingsId`.add noTargetsFinding
    else:
      quote do:
        for t in `tsId`:
          var f = SymexFinding(
            targetDesc: describeTarget(t),
            covered:    false,
            z3Version:  z3FullVersion(),
            fromCache:  false)
          # Phase 13 cycle 7. Three-level cascade:
          #   1. SAT cache hit → load witness, fromCache=true.
          #   2. Verdict cache hit → load sfUnsat/sfUnknown,
          #      fromCache=true.
          #   3. Cold path → runSymex; save witness or verdict.
          # `recordSymexFinding(f)` stays outside the if-else tree
          # so EVERY path deposits — invariant pinned by cycle 7's
          # `consumeSymexFindings()` assertion.
          let cached = loadSymexWitnessesImpl(`db`, `progId`, t,
                                              `symexSettings`, `dbErrorsId`)
          if cached.len > 0:
            f.status = sfSat
            f.witnessChoices = cached[0]
            f.fromCache = true
          else:
            let cachedVerdict = loadSymexVerdictImpl(`db`, `progId`, t,
                                                     `symexSettings`,
                                                     `dbErrorsId`)
            let cachedRaised = loadSymexRaisedImpl(`db`, `progId`, t,
                                                   `symexSettings`,
                                                   `dbErrorsId`)
            if cachedVerdict.isSome:
              f.status = cachedVerdict.get
              f.fromCache = true
            elif cachedRaised.len > 0:
              # Phase 15 E2a (STRUCTURAL). A reachable raise was persisted for
              # this target; serve it from cache without Z3. (E2b carries the
              # witness; E2a has none, so only the status is reloaded here.)
              f.status = sfRaised
              f.fromCache = true
            else:
              let raw = runSymex(`progId`, t, `symexSettings`)
              f.status = toFindingStatus(raw.status)
              case raw.status
              of sxSat:
                let `witId` {.used.} = raw.witness
                let typedWit: `tupleTy` = `witnessTup`
                f.witnessChoices = renderAsChoices(typedWit)
                saveSymexWitnessImpl(`db`, `progId`, t, `symexSettings`,
                                      f, `dbErrorsId`)
              of sxUnsat, sxUnknown:
                saveSymexVerdictImpl(`db`, `progId`, t, `symexSettings`,
                                      f.status, `dbErrorsId`)
              of sxRaised:
                # Phase 15 E2a (STRUCTURAL). Persist the raised finding via the
                # multi-finding protocol (per-type cache key + index). The
                # collapsed `runSymex` surfaces one raised RawResult per target;
                # wrap it for the seq-based save.
                # Phase 15 E6. Carry the defect type id onto the finding for
                # display when the raised type is a `Defect` subtype.
                if raw.isDefect:
                  f.defectTypeId = raw.raisedTypeId
                saveSymexRaisedImpl(`db`, `progId`, t, `symexSettings`,
                                    @[raw], `dbErrorsId`)
          recordSymexFinding(f)
          `findingsId`.add f

  result = quote do:
    block:
      let `progId` {.used.} = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`,
                              parseErrors: `peExpr`)
      `targetsBuild`
      var `findingsId`: seq[SymexFinding] = @[]
      var `dbErrorsId` {.used.}: seq[string] = @[]
        # Phase 13 cycle 3 — accumulator for DB save/load failures.
        # Phase 14 cycle C2: drained into `engineSymexDbErrors`
        # thread-local sink so `finalizePhase` can append into
        # `Report.dbErrors` at end-of-run.
      `runtimeBody`
      # Phase 14 C2: deposit accumulated DB errors into the
      # engine-side thread-local sink. `recordSymexDbError` is a
      # tiny append; safe to call from any phase.
      for dbErr in `dbErrorsId`:
        recordSymexDbError(dbErr)
      `findingsId`

