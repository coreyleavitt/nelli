## nelli/smt/find_emit -- the bodies of the `symexFind`, `concolicCollect` and
## `concolicFlip` entry macros.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The macros (their
## documented signatures) stay in `symex.nim` and delegate here, each passing
## its own symbol so the methods-registration re-expansion still names it.

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

proc symexFindImpl*(self: NimNode; fn: NimNode; target: SymexTarget; settings: SymexSettings): NimNode =
  ## RFC-0016 D6: the body of the `symexFind` macro (`symex.nim`); `self` is the macro's symbol.
  # RFC-parser-normalization N1: routes through `parseEntryImpl` like
  # `symexFindAllWitnesses` — `parsed` is consumed at macro time here
  # (`.params` below) via the same helper, not a different shape.
  # RFC-0010 review round 2: goes through `parseEntryImplWarned`
  # (below `warnIncoherentSettings`), which warns on an incoherent
  # `settings` and THEN calls `parseEntryImpl` — a single call site both
  # entries share.
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s.
  let e = entryParse(fn, "symexFind", settings, newCall(self,
    fn, targetLit(target), newLit(settings)))
  if e.again != nil: return e.again
  var parsed = e.parsed  # a copy: a `let` of an object field aliases in the VM (S8x)
  let progExpr = e.prog

  # Build the tuple type and witness-construction tuple. We genSym a
  # local name for the RawWitness so the witness-constructor calls
  # share an identity-equal NimNode with the `let` that binds it.
  let witId = genSym(nskLet, "rawWit")
  let (tupleTy, witnessTup) = emitWitnessTuple(parsed.params, witId)

  # ADR-0012 D2: a SEPARATE gensym for the per-diagnostic RawWitness
  # binding inside the diagnostics loop. Using a distinct name avoids any
  # shadowing concern with the outer `witId` binding.
  let diagWitId = genSym(nskLet, "diagRawWit")
  let (_, diagWitnessTup) = emitWitnessTuple(parsed.params, diagWitId)
  # RFC-0016 K10a-target: the same reader for each `UndefinedFinding`.
  let undefWitId = genSym(nskLet, "undefRawWit")
  let (_, undefWitnessTup) = emitWitnessTuple(parsed.params, undefWitId)

  # `(int,)` is a syntactic 1-tuple; nnkTupleConstr with one child
  # renders correctly for both the type and the value.


  # RFC-0005 S10: the walker run AND the rule-3 replay settle of its
  # candidates, in one emitted expression (`emitRunSymexReplayed`) -- the
  # `case raw.status` below only ever sees a settled result.
  let progId = genSym(nskLet, "prog")
  let runReplayed = emitRunSymexReplayed(fn, parsed.params, progId,
                                         newLit(target), newLit(settings),
                                         settings.replay,
                                         irCollectProcValueSites(parsed.body,
                                                                 parsed.procs))

  result = quote do:
    block:
      let `progId` = `progExpr`
      let raw = `runReplayed`
      ## ADR-0012 D2: type each RawDiagnostic into DefectFinding[T] by
      ## rebinding diagWitId per entry and running the same witnessTup reader.
      let diagResult = block:
        var diagSeq: seq[DefectFinding[`tupleTy`]]
        for diagEntry in raw.diagnostics:
          let `diagWitId` = diagEntry.raisedWitness
          diagSeq.add DefectFinding[`tupleTy`](
            raisedTypeId: diagEntry.raisedTypeId,
            defectKind:   typeIdToDefectKind(diagEntry.raisedTypeId),
            isDefect:     diagEntry.isDefect,
            raisedMsg:    diagEntry.raisedMsg,
            witness:      `diagWitnessTup`,
            heapSnapshot: readHeapSnapshot(`diagWitId`),
            witnessUnsafe:    diagEntry.witnessUnsafe)
        diagSeq
      let undefResult = block:
        var undefSeq: seq[UndefinedFinding[`tupleTy`]]
        for undefEntry in raw.undefined:
          let `undefWitId` = undefEntry.witness
          undefSeq.add UndefinedFinding[`tupleTy`](
            kind: undefEntry.kind, site: undefEntry.site,
            witness: `undefWitnessTup`)
        undefSeq
      case raw.status
      of sxSat:
        let `witId` = raw.witness
        SymexResult[`tupleTy`](status: sxSat, witness: `witnessTup`,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               heapSnapshot: readHeapSnapshot(`witId`),
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)
      of sxUnsat:
        SymexResult[`tupleTy`](status: sxUnsat,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)
      of sxUnknown:
        SymexResult[`tupleTy`](status: sxUnknown,
                               abstractions: raw.abstractions,
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)
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
                               obligations: raw.obligations,
                               callStats: raw.callStats,
                               heapSnapshot: readHeapSnapshot(`witId`),
                               errors: raw.errors,
                               annotationViolations: raw.annotationViolations,
                               soundness: raw.soundness,   ## RFC-0005 S11
                               bounds: raw.bounds,         ## RFC-0005 S11
                               diagnostics: diagResult,
                               undefined: undefResult)

proc concolicCollectImpl*(self: NimNode; fn: NimNode; trace: NimNode; bindings: NimNode; settings: SymexSettings; maxDraws: int): NimNode =
  ## RFC-0016 D6: the body of the `concolicCollect` macro (`symex.nim`); `self` is the macro's symbol.
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s.
  let e = entryParse(fn, "concolicCollect", settings,
    newCall(self, fn, trace, bindings, newLit(settings),
            newLit(maxDraws)))
  if e.again != nil: return e.again
  let progExpr = e.prog
  result = quote do:
    block:
      let prog = `progExpr`
      runConcolicCollectImpl(prog, `trace`, `bindings`, `settings`, `maxDraws`)

proc concolicFlipImpl*(self: NimNode; fn: NimNode; trace: NimNode; bindings: NimNode; targetBranchIndex: NimNode; settings: SymexSettings; maxDraws: int; maxRelaxationAttempts: int; z3TimeoutMs: uint): NimNode =
  ## RFC-0016 D6: the body of the `concolicFlip` macro (`symex.nim`); `self` is the macro's symbol.
  # RFC-0005 S8bn (item 6): register the methods `fn` calls, then again.
  # Review R1-11: the prelude and the parse are `entryParse`'s.
  let e = entryParse(fn, "concolicFlip", settings,
    newCall(self, fn, trace, bindings, targetBranchIndex,
            newLit(settings), newLit(maxDraws), newLit(maxRelaxationAttempts),
            newLit(z3TimeoutMs)))
  if e.again != nil: return e.again
  let progExpr = e.prog
  result = quote do:
    block:
      let prog = `progExpr`
      runConcolicFlipImpl(prog, `trace`, `bindings`, `targetBranchIndex`,
                         `settings`, `maxDraws`, `maxRelaxationAttempts`,
                         `z3TimeoutMs`)

