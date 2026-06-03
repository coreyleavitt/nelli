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

import std/[macros, sets, tables, algorithm]
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
       canonicalize.renderAsChoicesVersion, canonicalize.canonicalize

proc saveSymexWitnessImpl*(db: ExampleDatabase, prog: SymexProgram,
                           target: SymexTarget, settings: SymexSettings,
                           finding: SymexFinding, maxEntries = 64) =
  ## Runtime body of `saveSymexWitness`. Skips non-Sat findings (no
  ## witness to persist), otherwise saves the choice array under the
  ## content-addressed key.
  if finding.status != sfSat: return
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  db.save(key, finding.witnessChoices, maxEntries)

proc loadSymexWitnessesImpl*(db: ExampleDatabase, prog: SymexProgram,
                             target: SymexTarget,
                             settings: SymexSettings
                            ): seq[seq[ChoiceNode]] =
  ## Runtime body of `loadSymexWitnesses`. Returns the persisted
  ## witnesses for *exactly* this SUT/target/settings/Z3/Nim/walker
  ## combination. Mismatched key → empty seq — stale entries are
  ## silently ignored.
  let key = symexCacheKey(prog, target, settings,
    z3Version        = z3FullVersion(),
    nimVersion       = NimVersion,
    walkerVersion    = symexWalkerVersion,
    renderingVersion = renderAsChoicesVersion)
  db.loadPrimary(key)

proc toFindingStatus*(s: SymexStatusKind): SymexFindingStatus =
  case s
  of sxSat:     sfSat
  of sxUnsat:   sfUnsat
  of sxUnknown: sfUnknown

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
  else: ("", "")

proc emitTyAndReader*(ty: IRType, path: string, witId: NimNode): (NimNode, NimNode) =
  ## Recursive: returns (Nim type AST, witness-construction expression).
  case ty.kind
  of itBool, itInt:
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
    for arm in ty.vArms:
      let tagLit = newCall(discTyId, newLit(arm.tagOrdinal))
      var ctor = newTree(nnkObjConstr, objTyId)
      # Plain fields first (in source order).
      for i, fname in ty.vPlainFieldNames:
        let fty = ty.vPlainFieldTypes[i]
        let plainPath = path & "." & fname
        let (_, fReader) = emitTyAndReader(fty, plainPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      # Discriminator literal.
      ctor.add nnkExprColonExpr.newTree(
        ident(ty.vDiscName), ident(arm.tagName))
      # Arm-specific fields.
      for j, fname in arm.fieldNames:
        let fty = arm.fieldTypes[j]
        let armPath = path & ".@" & $arm.tagOrdinal & "." & fname
        let (_, fReader) = emitTyAndReader(fty, armPath, witId)
        ctor.add nnkExprColonExpr.newTree(ident(fname), fReader)
      caseStmt.add nnkOfBranch.newTree(tagLit, ctor)
    caseStmt.add nnkElse.newTree(newCall(ident"default", objTyId))
    (objTyId, caseStmt)

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
  let parsed = parseProc(impl)

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

  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      let raw = runSymex(prog, `target`, `settings`)
      case raw.status
      of sxSat:
        let `witId` = raw.witness
        SymexResult[`tupleTy`](status: sxSat, witness: `witnessTup`,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats)
      of sxUnsat:
        SymexResult[`tupleTy`](status: sxUnsat,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats)
      of sxUnknown:
        SymexResult[`tupleTy`](status: sxUnknown,
                               abstractions: raw.abstractions,
                               callStats: raw.callStats)

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
  let parsed = parseProc(impl)

  let actualTestFn =
    if testFn.kind == nnkNilLit: fn else: testFn

  # Splat the witness tuple into testFn's positional params.
  let witId = genSym(nskLet, "wit")
  var splat = newCall(actualTestFn)
  for i in 0 ..< parsed.params.len:
    splat.add nnkBracketExpr.newTree(witId, newLit(i))

  # gensym shared identifiers used across the cover-check sub-quote
  # and the main quote — quote-do hygiene would otherwise mint
  # fresh symbols per block.
  let hitsId           = genSym(nskLet, "hits")
  let assertionRaisedId = genSym(nskVar, "assertionRaised")
  let indexRaisedId     = genSym(nskVar, "indexRaised")
  let fieldRaisedId     = genSym(nskVar, "fieldRaised")

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
  let targetDescLit = newLit(describeTarget(target))

  # Rebuild the target node from its kind so the spliced AST is
  # always well-formed for the variant.
  let targetExpr =
    case target.kind
    of stkLabel:           newCall(bindSym"tLabel", newLit(target.label))
    of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
    of stkIndexError:      newCall(bindSym"tIndexError")
    of stkFieldDefect:     newCall(bindSym"tFieldDefect")

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
        try:
          `splat`
        except AssertionDefect:
          `assertionRaisedId` = true
        except IndexDefect:
          `indexRaisedId` = true
        except FieldDefect:
          `fieldRaisedId` = true
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
  let parsed = parseProc(impl)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      saveSymexWitnessImpl(`db`, prog, `targetExpr`, `settings`,
                            `finding`, `maxEntries`)

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
  let parsed = parseProc(impl)
  let paramsExpr = parsed.paramsNimNode
  let bodyExpr   = parsed.bodyNimNode
  let procsExpr  = parsed.procsNimNode
  let targetExpr = rebuildTargetNode(target)
  result = quote do:
    block:
      let prog = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      loadSymexWitnessesImpl(`db`, prog, `targetExpr`, `settings`)

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
  # Check for `var T` parameters directly from the formalParams
  # NimNode — `parseProc` flattens to `IRParam` without preserving
  # the `var` marker, so we look at the raw AST. nnkIdentDefs's
  # type slot is wrapped in nnkVarTy iff the user wrote `var T`.
  let formalParams = impl[3]
  for i in 1 ..< formalParams.len:
    let id = formalParams[i]
    let tyNode = id[id.len - 2]
    if tyNode.kind == nnkVarTy:
      error("symexFindAllWitnesses: `var T` parameters are not " &
            "supported (witness reconstruction has no caller-side " &
            "identity to bind to)", fn)
  let parsed = parseProc(impl)

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
  var excludedKinds: set[SymexTargetKind]
  proc collectKinds(n: NimNode) =
    case n.kind
    of nnkPrefix:
      if n.len == 2: collectKinds(n[1])     # `@` prefix → recurse into bracket
    of nnkBracket:
      for child in n: collectKinds(child)   # `[a, b, c]` → recurse each
    of nnkCall, nnkCommand:
      if n.len >= 1 and n[0].kind in {nnkIdent, nnkSym}:
        case n[0].strVal
        of "tLabel":              excludedKinds.incl stkLabel
        of "tAssertionViolation": excludedKinds.incl stkAssertionViolation
        of "tIndexError":         excludedKinds.incl stkIndexError
        of "tFieldDefect":        excludedKinds.incl stkFieldDefect
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
  if stkLabel notin excludedKinds:
    for lbl in labels:
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
            z3Version:  z3FullVersion())
          # DB cache: per-target load first under the content-
          # addressed key. Hit → bypass symex; miss → run symex
          # and save on Sat. UNSAT/UNKNOWN are not cached
          # (re-derived each call — documented in deferral #9).
          let cached = loadSymexWitnessesImpl(`db`, `progId`, t,
                                              `symexSettings`)
          if cached.len > 0:
            f.status = sfSat
            f.witnessChoices = cached[0]
          else:
            let raw = runSymex(`progId`, t, `symexSettings`)
            f.status = toFindingStatus(raw.status)
            if raw.status == sxSat:
              let `witId` {.used.} = raw.witness
              let typedWit: `tupleTy` = `witnessTup`
              f.witnessChoices = renderAsChoices(typedWit)
              saveSymexWitnessImpl(`db`, `progId`, t, `symexSettings`, f)
          recordSymexFinding(f)
          `findingsId`.add f

  result = quote do:
    block:
      let `progId` {.used.} = SymexProgram(params: `paramsExpr`,
                              body: `bodyExpr`,
                              procs: `procsExpr`)
      `targetsBuild`
      var `findingsId`: seq[SymexFinding] = @[]
      `runtimeBody`
      `findingsId`

