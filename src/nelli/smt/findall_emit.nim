## nelli/smt/findall_emit -- the body of the `symexFindAllWitnesses` macro:
## every auto-discovered target of an entry routine, symex'd and cached.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The macro (its documented
## signature) stays in `symex.nim` and delegates to `symexFindAllWitnessesImpl`;
## the macro passes its own symbol so the re-expansion still names it.

import std/[macros, sets, tables, algorithm, options, strutils, importutils]
import ../choice
import ../db
import ./dsl
import ./scan
import ./scan_kinds
import ./impl_digest
import ./replayproc
import ./replaywire
import ./replayresult
from ./scoped_names import isModuleGlobal, isRoutineGlobal, globalIRName
import ../engine/types as engineTypes
from ../engine/frame import recordSymexFinding, FindingOrigin
import ./sha256
import ./canonicalize
import ./witness_render
import ./witness_emit
import ./replay_emit
import ./replay_settle
import ./run_replayed
import ./symex_cache

import ./entry_parse
import ./witness_fidelity
import ./replay_footprint
import ./heldset
import ./proc_lift
import ./routine_table
import ./cover_emit

proc symexFindAllWitnessesImpl*(self: NimNode; fn: NimNode; db: NimNode; symexSettings: SymexSettings; excludeTargets: NimNode): NimNode =
  ## RFC-0016 D6: the body of the `symexFindAllWitnesses` macro (`symex.nim`); `self` is the macro's symbol.
  # Phase 14 A7b: the Phase-12 `var T` guard is lifted. Witness
  # semantics: the walker reports the INITIAL value of each `var`
  # param (via `initialEnv`), which the test runtime invokes the
  # SUT with. Mutations are walker-internal symbolic operations
  # with no caller-side identity tracking.
  # RFC-parser-normalization N1: collapses getImpl -> gate -> parseProc.
  # RFC-0010 review round 2: via `parseEntryImplWarned`, so an
  # incoherent `symexSettings` warns here — and, transitively, for
  # `symexForAll`, which emits a call to this macro rather than routing
  # through `symexFind`/`assertCoveredBy` (its own settings never touched
  # `warnIncoherentSettings` before this).
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s, as the cache
  # and DB macros' are, so their keys are the ones written here.
  let e = entryParse(fn, "symexFindAllWitnesses", symexSettings,
    newCall(self, fn, db, newLit(symexSettings),
            excludeTargets))
  if e.again != nil: return e.again
  var parsed = e.parsed  # a copy: a `let` of an object field aliases in the VM (S8x)
  let progExpr = e.prog

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
        of "tUndefined":          excludedKinds.incl stkUndefined
        else: discard
    else: discard
  collectKinds(excludeTargets)

  # Build the witness-renderer for this proc's parameter tuple
  # exactly as `symexFind` does — the witness reconstruction must
  # produce a typed Nim value so `renderAsChoices` can serialise it
  # into the choice IR for the example DB and report.
  let witId = genSym(nskLet, "rawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(parsed.params, witId)
  # RFC-0005 W1: the per-diagnostic reader, as `symexFind` builds it (a
  # distinct gensym so it never shadows `witId`).
  let diagWitId = genSym(nskLet, "diagRawWit")
  let (_, diagWitnessTup) = emitWitnessTuple(parsed.params, diagWitId)
  # A zero-parameter `fn` has the empty tuple `()` as its witness: a value,
  # not a type annotation, so annotate only a non-empty one.
  proc witnessDecl(name, tup: NimNode): NimNode =
    if parsed.params.len == 0:
      quote do:
        let `name` {.used.} = `tup`
    else:
      quote do:
        let `name`: `tupleTy` = `tup`
  let undefWitId = genSym(nskLet, "undefRawWit")   # RFC-0016 K10a-target
  let (_, undefWitnessTup) = emitWitnessTuple(parsed.params, undefWitId)
  let typedUndefWitId = genSym(nskLet, "typedUndefWit")
  let typedDiagWitId = genSym(nskLet, "typedDiagWit")
  let typedWitId = genSym(nskLet, "typedWit")
  let typedRaisedWitId = genSym(nskLet, "typedRaisedWit")
  let typedDiagWitDeclNode = witnessDecl(typedDiagWitId, diagWitnessTup)
  let typedUndefWitDeclNode = witnessDecl(typedUndefWitId, undefWitnessTup)
  let typedWitDeclNode = witnessDecl(typedWitId, witnessTup)
  let typedRaisedWitDeclNode = witnessDecl(typedRaisedWitId, witnessTup)


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
  let loopTarget = genSym(nskForVar, "t")  ## the runtime loop variable below
  let runReplayed = emitRunSymexReplayed(fn, parsed.params, progId,
                                         loopTarget, newLit(symexSettings),
                                         symexSettings.replay,
                                         irCollectProcValueSites(parsed.body,
                                                                 parsed.procs))
  let gapsSym = bindSym"findingGaps"   ## RFC-0005 S11 (private helper)
  let hintsSym = bindSym"findingHints"   ## RFC-0005 W1 (private helper)
  let stampSym = bindSym"stampBuild"     ## RFC-0016 K5a
  let runtimeBody =
    if nTargets == 0:
      # RFC-0005 W1 (§8.1, S11: every finding carries soundness, gaps and
      # annotation violations). Nothing ran, so the run's error list is the
      # parse-time one; its coordinate is derived from it as `runSymex`
      # derives a run's (`runTaintOf`), so the gaps' class join is the
      # `runTaint`, and there is no winning path or replay.
      quote do:
        let noTargetsFinding = SymexFinding(
          targetDesc: "no-targets-discovered",
          status:     sfNotApplicable,
          covered:    false,
          z3Version:  z3FullVersion(),
          # Review R1-16: settled by construction -- nothing ran, so there
          # is no claim to replay.
          soundness:  Soundness(runTaint: runTaintOf(`progId`.parseErrors),
                                replay: rsNotNeeded),
          bounds:     `symexSettings`.budget,       ## review R1-17
          gaps:       `gapsSym`(`progId`.parseErrors),
          hints:      `hintsSym`(`progId`.parseErrors),
          annotationViolations: `progId`.annotationViolations)
        `findingsId`.add noTargetsFinding
    else:
      quote do:
        for `loopTarget` in `tsId`:
          var f = SymexFinding(
            targetDesc: describeTarget(`loopTarget`),
            covered:    false,
            z3Version:  z3FullVersion(),
            fromCache:  false,
            # Review R1-17: the budget; a cache hit's key was derived from
            # it (every field is keyed), so the stored verdict ran under it.
            bounds:     `symexSettings`.budget,
            # RFC-0005 S11: parse-time facts, so a cache hit has them too.
            annotationViolations: `progId`.annotationViolations)
          # Phase 13 cycle 7. Three-level cascade:
          #   1. SAT cache hit → load witness, fromCache=true.
          #   2. Verdict cache hit → load sfUnsat/sfUnknown,
          #      fromCache=true.
          #   3. Cold path → runSymex; save witness or verdict.
          # `findingsId.add f` stays outside the if-else tree so EVERY
          # path returns a finding.
          let cached = loadSymexWitnessesImpl(`db`, `progId`, `loopTarget`,
                                              `symexSettings`, `dbErrorsId`)
          if cached.len > 0:
            f.status = sfSat
            f.witnessChoices = cached[0].choices
            f.soundness = cached[0].soundness   ## RFC-0005 S11: served unchanged
            f.gaps = cached[0].gaps             ## RFC-0005 S8az
            f.fromCache = true
          else:
            let cachedVerdict = loadSymexVerdictImpl(`db`, `progId`, `loopTarget`,
                                                     `symexSettings`,
                                                     `dbErrorsId`)
            # The raised slot is read only when the verdict missed; the
            # cascade is witness, then verdict, then raised.
            let cachedRaised =
              if cachedVerdict.isNone:
                loadSymexRaisedImpl(`db`, `progId`, `loopTarget`,
                                    `symexSettings`, `dbErrorsId`)
              else: @[]
            if cachedVerdict.isSome:
              f.status = cachedVerdict.get.status
              f.soundness = cachedVerdict.get.soundness   ## RFC-0005 S11
              f.gaps = cachedVerdict.get.gaps             ## RFC-0005 S8av
              f.fromCache = true
            elif cachedRaised.len > 0:
              # Phase 15 E2a. A reachable raise was persisted for this target;
              # serve it from cache without Z3. RFC-0005 W1: as the cold arm
              # below builds it -- the `raised(<type>)` descriptor, the
              # defect type and the witness the sentinel stores.
              let hit = cachedRaised[0]
              f.status = sfRaised
              f.targetDesc = "raised(" & hit.raw.raisedTypeId & ")"
              if hit.raw.isDefect:
                f.defectTypeId = hit.raw.raisedTypeId
              f.witnessChoices = hit.choices
              f.soundness = hit.raw.soundness   ## RFC-0005 S11
              f.gaps = hit.gaps                 ## RFC-0005 S8az
              f.fromCache = true
            else:
              # RFC-0005 S10: run + rule-3 replay settle; persisted below
              # only AFTER the settle (replay precedes persist, §7).
              let raw = `runReplayed`
              f.status = toFindingStatus(raw.status)
              # RFC-0005 S11: the settled soundness (persisted below with the
              # verdict) and the per-cause view of this run.
              f.soundness = raw.soundness
              f.bounds = raw.bounds   ## review R1-17
              f.gaps = `gapsSym`(raw.errors)
              # RFC-0005 W1: what `gaps` leaves out (the replay outcomes
              # among it) and the raises that did not decide the verdict,
              # the latter rendered as `symexFind` types them.
              f.hints = `hintsSym`(raw.errors)
              for diagEntry in raw.diagnostics:
                let `diagWitId` {.used.} = diagEntry.raisedWitness
                `typedDiagWitDeclNode`
                f.diagnostics.add FindingDiagnostic(
                  raisedTypeId:   diagEntry.raisedTypeId,
                  isDefect:       diagEntry.isDefect,
                  raisedMsg:      diagEntry.raisedMsg.get(""),
                  witnessChoices: renderAsChoices(`typedDiagWitId`),
                  witnessUnsafe:    diagEntry.witnessUnsafe)
              # RFC-0016 K10a-target: the undefined behaviours reached, with
              # the witness that reaches each, rendered the same way.
              for undefEntry in raw.undefined:
                let `undefWitId` {.used.} = undefEntry.witness
                `typedUndefWitDeclNode`
                f.undefined.add FindingUndefined(
                  kind: $undefEntry.kind, site: undefEntry.site,
                  witnessChoices: renderAsChoices(`typedUndefWitId`))
              var verdictSaved = false
              case raw.status
              of sxSat:
                let `witId` {.used.} = raw.witness
                `typedWitDeclNode`
                f.witnessChoices = renderAsChoices(`typedWitId`)
                verdictSaved = saveSymexWitnessImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                      f, `dbErrorsId`)
              of sxUnsat, sxUnknown:
                verdictSaved = saveSymexVerdictImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                      f.status, f.soundness, `dbErrorsId`,
                                      f.gaps)   ## RFC-0005 S8av
              of sxRaised:
                # Phase 16 D1a. The defect fork is now unconditional;
                # `routeRaise` populates `raisedWitness`. Carry it as
                # `witnessChoices` so callers can replay the input.
                # Use a DISTINCT `targetDesc` ("raised(<TypeId>)") so
                # sfSat filter loops in tests don't double-match on the
                # same base descriptor.
                let `witId` {.used.} = raw.raisedWitness
                `typedRaisedWitDeclNode`
                f.witnessChoices = renderAsChoices(`typedRaisedWitId`)
                f.targetDesc = "raised(" & raw.raisedTypeId & ")"
                # Phase 15 E6. Carry the defect type id onto the finding for
                # display when the raised type is a `Defect` subtype.
                if raw.isDefect:
                  f.defectTypeId = raw.raisedTypeId
                verdictSaved = saveSymexRaisedImpl(`db`, `progId`, `loopTarget`, `symexSettings`,
                                    @[raw], `dbErrorsId`, @[f.gaps],  ## RFC-0005 S8az
                                    @[f.witnessChoices])               ## RFC-0005 W1
              # RFC-0005 W1: beside whichever slot the arm above wrote.
              # Review R4 (W2), R5 (D4a): only when that arm saved the verdict
              # (its own return, not a copy of its skip rules).
              if verdictSaved:
                saveSymexNotesImpl(`db`, `progId`, `loopTarget`,
                                   `symexSettings`, f.hints, f.diagnostics,
                                   f.undefined, `dbErrorsId`)
          if f.fromCache:
            # RFC-0005 W1: every hit above serves the cold run's hints and
            # diagnostics too, from the `:notes` record the cold arm wrote.
            let notes = loadSymexNotesImpl(`db`, `progId`, `loopTarget`,
                                           `symexSettings`, `dbErrorsId`)
            f.hints = notes.hints
            f.diagnostics = notes.diagnostics
            f.undefined = notes.undefined   # RFC-0016 K10a-target
          `stampSym`(f.soundness)   ## RFC-0016 K5a: a cache hit's too
          `findingsId`.add f

  result = quote do:
    block:
      let `progId` {.used.} = `progExpr`
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

