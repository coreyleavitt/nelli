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

import std/[macros, sets, tables]
import z3
export z3.z3FullVersion
import ./choice
export choice
import ./smt/dsl
export dsl
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
    result.add integerChoice(int64(w.len), 0'i64, sxLenMax, 0'i64)
    for e in w:
      result.add renderAsChoices(e)
  elif T is HashSet:
    result.add integerChoice(int64(w.len), 0'i64, sxLenMax, 0'i64)
    for e in w:
      result.add renderAsChoices(e)
  elif T is Table:
    result.add integerChoice(int64(w.len), 0'i64, sxLenMax, 0'i64)
    for k, v in w.pairs:
      result.add renderAsChoices(k)
      result.add renderAsChoices(v)
  elif T is tuple:
    for f in fields(w):
      result.add renderAsChoices(f)
  elif T is object:
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

# ---- SymexFinding sink ------------------------------------------------------
#
# `assertCoveredBy` deposits a `SymexFinding` here so the engine can
# snapshot them into `Report.symexFindings` at finalize time. Drain
# via `consumeSymexFindings()` (clears the buffer atomically).

var symexFindings* {.threadvar.}: seq[SymexFinding]

proc recordSymexFinding*(f: SymexFinding) =
  symexFindings.add f

proc consumeSymexFindings*(): seq[SymexFinding] =
  result = symexFindings
  symexFindings.setLen(0)

proc describeTarget*(t: SymexTarget): string =
  case t.kind
  of stkLabel:              "label(\"" & t.label & "\")"
  of stkAssertionViolation: "assertion-violation"
  of stkIndexError:         "index-error"

# ---- DB persistence with Z3-version tag -------------------------------------
#
# Symex-derived witnesses persist under a derived testId of the form
# `<testId>#symex#<z3Version>`. A Z3 upgrade rotates the bucket, so
# stale witnesses are invisible to the new version — the cheapest
# possible "invalidation" without extending the DB schema, and
# strictly correct because the new Z3 may model BV semantics
# differently.
import ./db
export db

proc symexDbKey*(testId: string, z3Version: string): string {.inline.} =
  testId & "#symex#" & z3Version

proc saveSymexWitness*(db: ExampleDatabase, testId: string,
                       finding: SymexFinding, maxEntries = 64) =
  if finding.status != sfSat: return
  let key = symexDbKey(testId, finding.z3Version)
  db.save(key, finding.witnessChoices, maxEntries)

proc loadSymexWitnesses*(db: ExampleDatabase, testId: string,
                         z3Version: string): seq[seq[ChoiceNode]] =
  ## Returns symex witnesses persisted under `testId` for exactly the
  ## given Z3 version. A mismatched version returns an empty seq —
  ## stale witnesses are silently ignored.
  db.loadPrimary(symexDbKey(testId, z3Version))

proc toFindingStatus*(s: SymexStatusKind): SymexFindingStatus =
  case s
  of sxSat:     sfSat
  of sxUnsat:   sfUnsat
  of sxUnknown: sfUnknown


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
  let targetDescLit = newLit(describeTarget(target))

  # Rebuild the target node from its kind so the spliced AST is
  # always well-formed for the variant.
  let targetExpr =
    case target.kind
    of stkLabel:           newCall(bindSym"tLabel", newLit(target.label))
    of stkAssertionViolation: newCall(bindSym"tAssertionViolation")
    of stkIndexError:      newCall(bindSym"tIndexError")

  result = quote do:
    block:
      let r = symexFind(`fn`, `targetExpr`, `settings`)
      case r.status
      of sxSat:
        let `witId` = r.witness
        symexCaptureBegin()
        var `assertionRaisedId` = false
        var `indexRaisedId` = false
        try:
          `splat`
        except AssertionDefect:
          `assertionRaisedId` = true
        except IndexDefect:
          `indexRaisedId` = true
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
