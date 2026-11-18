## nelli/smt/cover_emit -- the `assertCoveredBy` family: `SymexCoverageDefect`,
## the per-target outcome (`coverageOutcome`, `coverageOutcomes`), the host
## refusal text and the body of the single-target `assertCoveredBy` macro.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. `SymexCoverageDefect` is
## re-exported by `symex.nim`; the macro itself (its documented signature)
## stays there and delegates to `assertCoveredByImpl`.

import std/[macros, strutils]
import ./dsl
import ../engine/types as engineTypes
from ../engine/frame import recordSymexFinding, FindingOrigin
import ./witness_render
import ./symex_cache
import ./entry_parse
import ./witness_fidelity
import ./replay_footprint

type
  SymexCoverageDefect* = object of AssertionDefect
    ## Review R1-10. What `assertCoveredBy` raises when coverage is not
    ## proven, carrying the finding(s) the call made: a finding belongs to
    ## the call that produced it, on failure as on success (it was a
    ## thread-local sink that leaked into later callers).
    findings*: seq[SymexFinding]

proc coverageOutcome*(origin: FindingOrigin; f: SymexFinding;
                     failure: string): SymexFinding {.discardable.} =
  ## Review R1-10. The end of a single-target `assertCoveredBy`: its finding,
  ## or a `SymexCoverageDefect` carrying it when `failure` says why coverage
  ## is not proven. Review R2 (DD3): inside a property, the finding also
  ## goes on the run's report (`recordSymexFinding`), on success or failure;
  ## review R3 (E2): as the latest of its call site `site` for its target.
  ## Outside any property, the return and the defect are its only channel.
  recordSymexFinding(origin, f)
  if failure.len > 0:
    var e = newException(SymexCoverageDefect, failure)
    e.findings = @[f]
    raise e
  f

proc coverageOutcomes*(fs: seq[SymexFinding]; failures: seq[string];
                      total: int): seq[SymexFinding] {.discardable.} =
  ## Review R1-10. The end of a multi-target `assertCoveredBy`: every
  ## target's finding, or one `SymexCoverageDefect` carrying them all.
  if failures.len > 0:
    var msg = "assertCoveredBy (multi): " & $failures.len &
              " of " & $total & " targets uncovered:"
    for f in failures:
      msg.add "\n  - " & f
    var e = newException(SymexCoverageDefect, msg)
    e.findings = fs
    raise e
  fs

# ---- assertCoveredBy --------------------------------------------------------

proc hostRefusalReason*(s: Soundness): string =
  ## Why `hostRunnable(s)` is false, as the reason `assertCoveredBy` gives for
  ## not running a witness: the actual cause, not one guessed for all of them.
  if s.replay == rsUnsettled:
    "its record was never settled"
  elif s.witnessUndefined != {}:
    var names: seq[string] = @[]
    for k in undefinedKinds(s): names.add $k
    "its path ran past undefined behaviour (" & names.join(", ") & ")"
  elif s.witnessUnsafe:
    "its witness ends or hangs the process that runs it (a crash claim, " &
      "or a replay that ended or hung its child)"
  else:
    "it is not host-runnable"
proc assertCoveredByImpl*(self: NimNode; fn: NimNode; target: SymexTarget; testFn: NimNode; settings: SymexSettings): NimNode =
  ## RFC-0016 D6: the body of the `assertCoveredBy` macro (`symex.nim`); `self` is the macro's symbol.
  # RFC-parser-normalization N1: routes through `parseEntryImpl`, same as
  # `symexFind` above — `parsed` is consumed at macro time via the same
  # helper `symexFindAllWitnesses` uses.
  # RFC-0010 review round 2: via `parseEntryImplWarned`, so an
  # incoherent `settings` warns here too.
  # RFC-0016 PRC-45: through `entryParse`, as every walking entry parses, so
  # the methods are registered and a type's hook probes (`dupHookProbes`) are
  # staged here exactly as in the `symexFind` this expands to: no verdict, and
  # no parse, depends on which entry of a build met a type first.
  let e = entryParse(fn, "assertCoveredBy", settings,
    newCall(self, fn, targetLit(target), testFn, newLit(settings)))
  if e.again != nil: return e.again
  var parsed = e.parsed  # a copy: a `let` of an object field aliases in the VM (S8x)

  let actualTestFn =
    if testFn.kind == nnkNilLit: fn else: testFn

  # Splat the witness tuple into testFn's positional params.
  # Phase 14 A7b: wrap each param in a fresh `var` local before the
  # call so `var T` parameters receive an addressable lvalue.
  # Pre-A7b this emitted `testFn(wit[0], wit[1], ...)` which fails
  # to compile for SUTs that take any `var T`. The wrapping is
  # zero-cost for non-var params and idiomatic for var params.
  # (RFC-0005 S2: the splat is `emitWitnessSplat`, shared with replay.)
  let witId = genSym(nskLet, "wit")
  let splatBlock = emitWitnessSplat(actualTestFn, parsed.params.len, witId)

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
    of stkNilAccess:
      quote do: `anyRaisedId`   ## Phase 15 R5: covered iff the SUT nil-derefed
    of stkUndefined:
      quote do: false           ## RFC-0016 K10a-target: never run in the host
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
    of stkNilAccess:
      newLit("assertCoveredBy: testFn did not raise NilAccessDefect " &
             "on the symex witness (target was tNilAccess)")
    of stkUndefined:
      newLit("assertCoveredBy: a tUndefined witness reaches undefined " &
             "behaviour and is never run in the host")
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
    of stkNilAccess:       newCall(bindSym"tNilAccess")
    of stkUndefined:       newCall(bindSym"tUndefined", newLit(target.ubKinds))

  let gapsSym = bindSym"findingGaps"   ## RFC-0005 S11 (private helper)
  let hintsSym = bindSym"findingHints"         ## RFC-0005 W1 (private helper)
  let diagsSym = bindSym"findingDiagnostics"   ## RFC-0005 W1 (private helper)
  let undefSym = bindSym"findingUndefined"     ## RFC-0016 K10a-target
  # RFC-0005 0.9.1 (WA-2). A witness whose confirming replay ended its child
  # after the target (`witnessUnsafe`) is never splatted here: it would end or
  # hang this process. With no `testFn`, the replay already ran `fn` on it and
  # saw the target reached, which is the coverage this checks (an `sxSat`
  # claim is replayed against the search target). Otherwise nothing runs it,
  # and the check fails, saying why.
  #
  # Review R1-15. The arm reads `trusted()`, not `status` alone. A trusted
  # claim's witness reaches the target in `fn`, so a `testFn` that does not
  # reach it on that witness is to blame. An untrusted one (`rsUnconfirmed`: a
  # lossy witness no replay confirmed) proves no witness exists: it is run
  # (unless its replay ended its child, `hostRunnable`), and a hit
  # proves coverage, but a miss proves nothing about `testFn`. It is reported
  # as unconfirmed, as an UNKNOWN is, and `acceptUnknownAsCovered` downgrades
  # it the same way.
  #
  # Review R1-10. The finding is the call's own: returned (discardable), or
  # carried by the `SymexCoverageDefect` the call raises.
  let sameFn = newLit(testFn.kind == nnkNilLit)
  let unsafeMsg = newLit("assertCoveredBy: the symex witness is known to " &
    "end or hang the process that runs it after reaching the target (its " &
    "replay's child did not finish); it is not run in this process, so " &
    "testFn's coverage of it is not checked")
  let unconfirmedMsg = newLit("assertCoveredBy: symex claims " &
    describeTarget(target) & " is reachable, but the claim is not trusted " &
    "(its witness renders lossily and no replay of the real fn confirmed " &
    "it), so no witness is known to reach the target. ")
  let unconfirmedTail = newLit("Coverage is unconfirmed, and testFn is not " &
    "blamed (set acceptUnknownAsCovered = true to downgrade)")
  let runnableSym = bindSym"hostRunnable"
  let refusalSym = bindSym"hostRefusalReason"
  let outcomeSym = bindSym"coverageOutcome"
  # Review R3 (E2): the call site the run's report keys this finding by. The
  # multi-target form hands its own `fn` node on, so its targets share it.
  let siteLit = newLit(fn.lineInfo)
  # Review R4 (U1): and the `fn` itself, since a template or helper shares one
  # call site among several `fn`s, and a generic one among its instantiations.
  # Review R5 (3d): a routine is told apart as `routineKey` tells routines
  # apart (name and body hash; `signatureHash` is the same for every routine
  # of one parameter list). `parseEntryImplWarned` above has already resolved
  # `fn` through `getImpl`, which rejects anything that is not a routine
  # symbol (a lambda, a call, a template, a macro, a proc-typed variable), so
  # only a symbol `resolveRoutineImpl` accepts gets here. Asked of that
  # resolver, not of a symbol-kind set, so the two cannot drift (the N2 kind
  # gate audit forbids a bare kind gate outside it).
  if fn.kind != nnkSym or resolveRoutineImpl(fn).isNil:
    error("assertCoveredBy: a non-routine symbol reached the finding key", fn)
  let fnIdText = routineKey(fn)
  let fnIdLit = newLit(fnIdText & "@" & fn.getTypeInst.repr)
  let originLit = nnkObjConstr.newTree(bindSym"FindingOrigin",
    nnkExprColonExpr.newTree(ident"site", siteLit),
    nnkExprColonExpr.newTree(ident"fnId", fnIdLit))
  let trustedSym = bindSym"trusted"
  # Shared by the arm bodies below and the block they are spliced into.
  let rId = genSym(nskLet, "r")
  let findingId = genSym(nskVar, "finding")
  let failureId = genSym(nskVar, "failureMsg")
  # One body for the two arms that carry a witness: `sxSat` (`r.witness`) and
  # `sxRaised` (`r.raisedWitness`). `sameFnOk` says whether, with no `testFn`,
  # an unsafe witness's replay already established the coverage: true for
  # `sxSat` (replayed against this target), false for `sxRaised` (replayed
  # against the raise).
  let acceptUnknown = newLit(settings.acceptUnknownAsCovered)
  proc claimArm(witField: NimNode; status: NimNode;
                sameFnOk: bool): NimNode =
    let unsafeCovers = newLit(sameFnOk)
    quote do:
      let `witId` = `witField`
      let trustedClaim = `trustedSym`(`rId`)
      let runIt = `runnableSym`(`rId`.soundness)
      symexCaptureBegin()
      var `assertionRaisedId` = false
      var `indexRaisedId` = false
      var `fieldRaisedId` = false
      var `anyRaisedId` = false   ## Phase 15 E2a: any exception raised
      try:
        if runIt:
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
      except NilAccessDefect:                       ## Phase 15 R5
        `anyRaisedId` = true
      except CatchableError:
        `anyRaisedId` = true
      except Defect:
        # RFC-0016 W1-c3 (W-26): any other Defect (overflow, range, div by
        # zero, ...) is a raise like the arms above, not the host's end.
        # Under --panics:on a Defect is not catchable (W1-c2 owns that).
        `anyRaisedId` = true
      let `hitsId` = symexCaptureEnd()
      let reached = runIt and `coveredExpr`
      var covered = false
      var failure = ""
      if `rId`.soundness.witnessUnsafe and trustedClaim:
        if `sameFn` and `unsafeCovers`: covered = true
        else: failure = `unsafeMsg`
      elif reached:
        covered = true
      elif trustedClaim:
        failure = `failMsg`
      else:
        if not `acceptUnknown`:
          failure = `unconfirmedMsg` &
            (if runIt: "Running it did not reach the target. "
             else: "It was not run here: " & `refusalSym`(`rId`.soundness) &
                   ". ") & `unconfirmedTail`
      `findingId` = SymexFinding(
        targetDesc:     `targetDescLit`,
        status:         `status`,
        covered:        covered,
        witnessChoices: renderAsChoices(`witId`),
        z3Version:      z3FullVersion(),
        soundness:      `rId`.soundness,              ## RFC-0005 S11
        bounds:         `rId`.bounds,                 ## review R1-17
        gaps:           `gapsSym`(`rId`.errors),
        annotationViolations: `rId`.annotationViolations,
        hints: `hintsSym`(`rId`.errors),                 ## RFC-0005 W1
        diagnostics: `diagsSym`(`rId`.diagnostics),
        undefined: `undefSym`(`rId`.undefined))
      `failureId` = failure
  let satArm = claimArm(newDotExpr(rId, ident"witness"), bindSym"sfSat", true)
  # Phase 16 D1a: defect targets (tAssertionViolation, tIndexError,
  # tFieldDefect, tNilAccess) return sxRaised with a populated
  # `raisedWitness` (the path-constrained witness that triggers the raise),
  # replayed through testFn exactly as an `sxSat` witness is.
  let raisedArm = claimArm(newDotExpr(rId, ident"raisedWitness"),
                           bindSym"sfRaised", false)
  result = quote do:
    block:
      let `rId` = symexFind(`fn`, `targetExpr`, `settings`)
      var `findingId`: SymexFinding
      var `failureId` = ""
      case `rId`.status
      of sxSat:
        `satArm`
      of sxUnsat:
        `findingId` = SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnsat, covered: true,
          z3Version:  z3FullVersion(),
          soundness:  `rId`.soundness,                  ## RFC-0005 S11
          bounds:     `rId`.bounds,                     ## review R1-17
          gaps:       `gapsSym`(`rId`.errors),
          annotationViolations: `rId`.annotationViolations,
          hints: `hintsSym`(`rId`.errors),                 ## RFC-0005 W1
          diagnostics: `diagsSym`(`rId`.diagnostics),
        undefined: `undefSym`(`rId`.undefined))
        # A vacuous pass.
      of sxUnknown:
        `findingId` = SymexFinding(
          targetDesc: `targetDescLit`, status: sfUnknown, covered: false,
          z3Version:  z3FullVersion(),
          soundness:  `rId`.soundness,                  ## RFC-0005 S11
          bounds:     `rId`.bounds,                     ## review R1-17
          gaps:       `gapsSym`(`rId`.errors),
          annotationViolations: `rId`.annotationViolations,
          hints: `hintsSym`(`rId`.errors),                 ## RFC-0005 W1
          diagnostics: `diagsSym`(`rId`.diagnostics),
        undefined: `undefSym`(`rId`.undefined))
        let s: SymexSettings = `settings`
        if not s.acceptUnknownAsCovered:
          `failureId` = "assertCoveredBy: symex returned UNKNOWN; cannot " &
            "prove coverage (set acceptUnknownAsCovered = true to downgrade)"
      of sxRaised:
        `raisedArm`
      `outcomeSym`(`originLit`, `findingId`, `failureId`)

