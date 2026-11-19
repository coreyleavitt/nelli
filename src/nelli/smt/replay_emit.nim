## nelli/smt/replay_emit -- the code a replay emits: the wire form of a
## `SymexTarget`, `emitReplayWitness` (the in-process or re-executed child run
## of a witness against the SUT) and `methodPrelude`.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The `{.compileTime.}`
## `replaySiteCounter` lives here and nowhere else. `wireTarget`,
## `readTarget`, `targetLabelOf` and `emitReplayWitness` are re-exported by
## `symex.nim`; the `replayWitness` macro that calls it stays there.

import std/[macros, sets, tables]
from std/os import extractFilename   # needed: method-call `.extractFilename` in a macro body Nim only checks on expansion
import ./dsl
import ./replayproc
import ./replaywire
import ./replayresult
import ./routine_table   # needed: `emitRoutineTable`, named in the replay child emitter, which Nim checks only on expansion
from ./scoped_names import isModuleGlobal, isRoutineGlobal, globalIRName
import ./replay_footprint
import ./witness_fidelity
import ./witness_emit   ## RFC-0016 INT-81: `witnessCellTypes`

proc wireTarget*(w: var WireWriter; t: SymexTarget) =
  ## RFC-0005 S8ct. A case object, so outside the generic encoding.
  wirePut(w, t.kind)
  case t.kind
  of stkLabel: wirePut(w, t.label)
  of stkRaisedExn: wirePut(w, t.typeFilter)
  of stkUndefined: wirePut(w, t.ubKinds)   ## RFC-0016 K10a-target
  else: discard

proc readTarget*(r: var WireReader): SymexTarget =
  ## RFC-0005 S8ct. See `wireTarget`.
  var k: SymexTargetKind
  wireGet(r, k)
  case k
  of stkLabel:
    var s: string
    wireGet(r, s)
    SymexTarget(kind: stkLabel, label: s)
  of stkRaisedExn:
    var s: string
    wireGet(r, s)
    SymexTarget(kind: stkRaisedExn, typeFilter: s)
  of stkAssertionViolation: SymexTarget(kind: stkAssertionViolation)
  of stkIndexError: SymexTarget(kind: stkIndexError)
  of stkFieldDefect: SymexTarget(kind: stkFieldDefect)
  of stkNilAccess: SymexTarget(kind: stkNilAccess)
  of stkUndefined:
    var ks: set[UbKind]
    wireGet(r, ks)
    SymexTarget(kind: stkUndefined, ubKinds: ks)

func targetLabelOf*(t: SymexTarget): string =
  ## RFC-0005 S8ct. The label a child reports as it is hit, or none.
  if t.kind == stkLabel: t.label else: ""

type ChildWitness* = object
  ## RFC-0005 S8ct. How a re-executed child comes by its witness, where it is not
  ## the rendered tuple itself: the entry macros marshal the solver's model
  ## (`blob`, of type `blobTy`), and the child renders it as the host does:
  ## `decl` binds `witId` from `blobId`.
  blob*, blobTy*, blobId*, decl*, witId*: NimNode

var replaySiteCounter {.compileTime.}: int

proc paramsFidelity*(params: seq[IRParam]): WitnessFidelity =
  ## How faithfully a witness of `params` renders: the worst parameter's
  ## `witnessFidelity`.
  var noms: Table[string, IRType]
  var seenNoms: HashSet[string]
  for p in params: collectNominals(p.ty, noms, seenNoms)
  result = wfFaithful
  for p in params: result = max(result, witnessFidelity(p.ty, noms))
  # RFC-0016 INT-81: a dynamic type a cell may have that no symbol names is
  # built as its deepest nameable ancestor (`cellDynBuild`): not the model.
  for t in witnessCellTypes(params):
    if hierChain(t).len >= 2 and not cellTypeNameable(t):
      result = max(result, wfLossy)

proc emitStartReplay*(fn: NimNode; params: seq[IRParam];
                        witness, target, pathTaint: NimNode;
                        extraLossy: NimNode = newLit(false);
                        nilDeref: NimNode = newLit(false);
                        timeoutMs: NimNode = newLit(
                          SymexSettings().replayTimeoutMs);
                        child: ChildWitness = ChildWitness();
                        hoist: NimNode = nil): NimNode =
  ## RFC-0005 S2: the macro-time half of `replayWitness`, spliced by S10 into
  ## the entry macros' shared replay emitter (`emitRunSymexReplayed`). Emits
  ## an expression of type `PendingReplay`: the replay started, not waited
  ## for (RFC-0016 INT-32 item 8; `emitReplayWitness` waits). `witness` is the typed witness
  ## tuple (the output of `emitTyAndReader`), `target` a `SymexTarget`
  ## expression, `pathTaint` a `Taint` expression (the candidate's).
  ## `extraLossy` (RFC-0005 S10) is a runtime `bool`: true when the model
  ## behind this witness is known NOT to be the rendered value even though
  ## its shape renders faithfully -- a candidate whose extraction recorded
  ## `feExtractionFailed` (a float leaf substituted by `0.0`). It demotes a
  ## miss from `roRefuted` to `roInconclusive`; a hit still confirms.
  ## `nilDeref` (RFC-0005 S8k) is a runtime `bool`: true when the witness's
  ## path went through the walker's nil-dereference edge
  ## (`SatCandidate.nilDerefOnPath`). Order of refusal, each one WITHOUT
  ## executing `fn`: ineligible taint, unexecutable witness shape, out-of-scope
  ## target kind, a nil-dereference path.
  ## `timeoutMs` (RFC-0005 S8be) is an `int` expression bounding the run;
  ## past it the child is killed and the outcome is `roTimedOut`.
  ## RFC-0005 S8ct: the run itself happens in a child process
  ## (`replayproc.nim`), never in this one.
  ## `hoist` (RFC-0016 W4 perf), when given, is a statement list in the
  ## caller's scope that receives the re-executed child's entry and routine
  ## table, where the expression itself is spliced into a routine (the
  ## `CandidateReplay` of `emitRunSymexReplayed`). The table names a nested
  ## routine only from module-level code (`nestedRoutineAddrs`), so it must
  ## not be built inside that routine; both ends read it from the entry's
  ## `{.global.}` registry. A hoisted `child.blobTy` must not name the
  ## expression's own symbols.
  let fidelity = paramsFidelity(params)
  if fidelity == wfUnexecutable:
    # Decided at macro time: the splat is not even emitted, so a placeholder
    # (a nil proc, a nil ptr) can never be called.
    return newCall(bindSym"decidedReplay", newCall(bindSym"replayNotRun"))
  let paramTys = formalParamTypes(fn)
  if paramTys.len != params.len:
    # not a plain proc type: never run it
    return newCall(bindSym"decidedReplay", newCall(bindSym"replayNotRun"))
  let witId = genSym(nskLet, "replayWit")
  let tgtId = genSym(nskLet, "replayTarget")
  let escId = genSym(nskVar, "replayEscaped")
  let boundId = genSym(nskVar, "replayArgsBound")
  let hitsId = genSym(nskLet, "replayHits")       # RFC-0005 S8be
  let childRes = genSym(nskLet, "replayChild")    # RFC-0005 S8ct
  # RFC-0005 S8bn (item 2): the module-level `var`s `fn` can reach, which a
  # `ptr` parameter's witness may be aimed at.
  var globals: seq[NimNode]
  for g in calleeOuterSyms(fn):
    if isModuleGlobal(g) and g.symKind == nskVar: globals.add g
  # The run: a statement list whose value is the `ReplayReport`, spliced into
  # the child's half on whichever side declares it. §4.2 "Capture reentrancy":
  # a nested frame, so an enclosing user capture (`assertCoveredBy`) keeps its
  # hits and does not see ours.
  proc runBody(childWitId, childTgtId: NimNode): NimNode =
    let splat = emitWitnessSplat(fn, params.len, childWitId, paramTys,
                                 newAssignment(boundId, newLit(true)),
                                 params, globals)
    result = quote do:
      var `escId`: ref Exception = nil
      var `boundId` = false
      symexCaptureBegin()
      armReplayHit(targetLabelOf(`childTgtId`))
      try:
        `splat`
      except Exception as e:
        `escId` = e
      let `hitsId` = symexCaptureEnd()
      ReplayReport(reached: replayReached(`childTgtId`, `hitsId`, `escId`),
                   bound: `boundId`)
  let lossy = newLit(fidelity == wfLossy)
  # RFC-0005 S10. The rendered witness type is not always the parameter
  # type (a `Rune` renders as `int`, a `distinct` as its base, a table as
  # the reader's own instantiation). `convertible` is a COMPILE-TIME check
  # that every argument converts; a witness that does not is never run
  # (`roInconclusive`, permanently -- the same as a placeholder shape).
  # `converted` marks a run whose arguments went through a conversion: its
  # hit still confirms (it is a real execution of `fn` on a concrete input),
  # but a miss only demotes to `roInconclusive`, because a conversion may
  # round (`float32`) and so the input run need not be the model.
  var convertible = newLit(true)
  var converted = newLit(false)
  for i in 0 ..< params.len:
    let elem = nnkBracketExpr.newTree(witId, newLit(i))
    let ty = paramTys[i]
    convertible = infix(convertible, "and",
                        newCall(bindSym"compiles", newCall(ty, elem)))
    converted = infix(converted, "or", infix(elem, "isnot", ty))
  var preamble = newStmtList()
  var runChild: NimNode
  when replayForks:
    let body = runBody(witId, tgtId)
    runChild = quote do:
      startReplayForked(proc (): ReplayReport {.closure, gcsafe.} =
        {.cast(gcsafe).}:
          result = (block:
            `body`), `timeoutMs`)
  elif replayReexecs:
    # What the SUT may reach must be handed over, or it does not run.
    var refuse = ""
    let fp = replayFootprint(fn)
    if fp.open:
      refuse = fp.why
    else:
      for g in fp.globals:
        if not isWireableType(g.getTypeInst):
          refuse = "`" & g.strVal & "`, of a type the wire cannot carry"
          break
    let blobTy =
      if child.blobTy != nil: child.blobTy
      else: newCall(bindSym"typeof", witness)
    if refuse.len == 0 and child.blobTy == nil and
       not isWireableType(witness.getTypeInst):
      refuse = "the witness, of a type the wire cannot carry (a ref " &
               "to an inheritable object, an imported C struct, a proc)"
    if refuse.len > 0:
      let msg = newLit(refuse)
      runChild = quote do:
        readyChild(refusedNotMarshallable(`msg`))
    else:
      inc replaySiteCounter
      let info = lineInfoObj(fn)
      let site = newLit(info.filename.extractFilename & ":" & $info.line & ":" &
                        $info.column & "#" & $replaySiteCounter)
      let rd = genSym(nskVar, "replayReader")
      let wr = genSym(nskVar, "replayWriter")
      let payload = genSym(nskParam, "payload")
      # Named by the site's count, which no other expansion shares (a symbol
      # made here would trip the N2 audit's routine-kind scan).
      let childProc = ident("nelliReplayChildBody" & $replaySiteCounter)
      let regId = genSym(nskVar, "replayChildRegistered")
      let stackId = genSym(nskVar, "replayStack")
      let blobId = if child.blobId != nil: child.blobId
                   else: genSym(nskVar, "replayBlob")
      # The child's own symbols, never the host side's: a genSym'd symbol declared
      # twice has one owner, and a child proc nested in a routine would then be
      # capturing the routine's local.
      let wid = if child.witId != nil: child.witId
                else: genSym(nskLet, "childWitness")
      let childTgt = genSym(nskLet, "childTarget")
      let decl =
        if child.decl != nil: child.decl
        else:
          let b = blobId
          quote do:
            let `wid` {.used.} = `b`
      let body = runBody(wid, childTgt)
      # RFC-0016 PRC-02. The routines a proc value may name, in one order for
      # both ends (the child is this binary): a slot a routine cannot fill
      # (one whose address cannot be taken) holds nil, which no value matches.
      # RFC-0016 W3-z R10: held in a `{.global.}` beside the child's entry, so
      # both ends take a nested routine's address where it can be taken
      # (module-level code, `nestedRoutineAddrs`), the child before it runs.
      let table = emitRoutineTable(fp)
      let tableExpr = table.procs
      let envOkExpr = table.envOk
      let envBenignExpr = table.envBenign
      let envPutExpr = table.envPut
      let envGetExpr = table.envGet
      let envWhyExpr = table.envWhy
      let registry = genSym(nskVar, "replayRoutines")
      var getGlobals = newStmtList()
      var putGlobals = newStmtList()
      for g in fp.globals:
        getGlobals.add quote do:
          wireGet(`rd`, cast[ptr typeof(`g`)](unsafeAddr `g`)[])
        # RFC-0016 W3-z R10 follow-up: the decline names the variable whose
        # value cannot cross, as a forked run's unlifted hint does.
        let gName = newLit("`" & g.strVal & "` holds ")
        putGlobals.add quote do:
          try:
            wirePut(`wr`, `g`)
          except WireError as e:
            raise newException(WireError, `gName` & e.msg)
      let blob = if child.blob != nil: child.blob else: witId
      # RFC-0016 PRC-02b. The child is this binary, so the toolchain's table of
      # what each method dispatcher can run says what it would run: a body no
      # scan read declines. Empty (nothing to ask) without a method in the scan.
      var dispatchCheck = newLit("")
      when hasMethodTable:
        if fp.dispatched.len > 0:
          var names = nnkBracket.newTree()
          var calls = nnkBracket.newTree()
          var addrs = nnkBracket.newTree()
          for m in fp.dispatched:
            names.add newLit(m.strVal)
            calls.add quote do: cast[pointer](`m`)
          for m in fp.methods:
            addrs.add quote do: cast[pointer](`m`)
          dispatchCheck = newCall(bindSym"methodDispatchRefusal",
                                  nnkPrefix.newTree(ident"@", names),
                                  nnkPrefix.newTree(ident"@", calls),
                                  nnkPrefix.newTree(ident"@", addrs))
      # The host runs no child for a witness that does not convert (`convertible`
      # below); the child's splat must not be compiled for one either.
      var childConvertible = newLit(true)
      for i in 0 ..< params.len:
        let elem = nnkBracketExpr.newTree(wid, newLit(i))
        childConvertible = infix(childConvertible, "and",
          newCall(bindSym"compiles", newCall(paramTys[i], elem)))
      let guarded = quote do:
        when `childConvertible`:
          `body`
        else:
          ReplayReport()
      let slotsTy = bindSym"RoutineSlots"
      preamble = quote do:
        var `registry` {.global.}: `slotsTy`
        proc `childProc`(`payload`: string): ReplayReport {.nimcall.} =
          var `rd` = initWireReader(`payload`, `registry`)
          `rd`.envGet = `envGetExpr`
          var `stackId`: int64
          wireGet(`rd`, `stackId`)
          let `childTgt` = readTarget(`rd`)
          var `blobId`: `blobTy`
          wireGet(`rd`, `blobId`)
          `getGlobals`
          readHostHooks(`rd`)
          `decl`
          result = (block:
            `guarded`)
        # The table is filled by the entry's own initialiser, so whenever
        # that runs (in the child, before the SUT), it is filled first.
        var `regId` {.global, used.} = (block:
          `registry` = `tableExpr`
          replayChildEntry(`site`, `childProc`))
      runChild = quote do:
        block:
          var `wr`: WireWriter
          `wr`.procs = `registry`
          `wr`.envOk = `envOkExpr`
          `wr`.envBenign = `envBenignExpr`
          `wr`.envPut = `envPutExpr`
          `wr`.envWhy = `envWhyExpr`
          var refused = ""
          try:
            wirePut(`wr`, int64(callerStackSize()))
            wireTarget(`wr`, `tgtId`)
            wirePut(`wr`, `blob`)
            `putGlobals`
          except WireError as e:
            refused = e.msg
          if refused.len > 0: readyChild(refusedNotMarshallable(refused))
          else:
            # RFC-0005 batch 11: what the host installed at run time, which the
            # child would start without (`putHostHooks`: RFC-0016 INT-13 hands
            # it the ones it can). RFC-0005 0.9.1 (WA-7): set at this moment
            # only, so the decline is not cached.
            let hook = putHostHooks(`wr`)
            let dispatch = `dispatchCheck`
            if hook.len > 0: readyChild(refusedHostHook(hook))
            elif dispatch.len > 0: readyChild(refusedNotMarshallable(dispatch))
            else: startReplayReexec(`site`, `wr`.data, `timeoutMs`)
  else:
    runChild = quote do:
      readyChild(refusedStatically("this platform has no way to run a " &
                                   "replay outside the host process"))
  if hoist != nil:
    hoist.add preamble
    preamble = newStmtList()
  result = quote do:
    block:
      `preamble`
      let `tgtId`: SymexTarget = `target`
      if not replayEligible(`pathTaint`) or not replayInScope(`tgtId`) or
         `nilDeref`:
        decidedReplay(replayNotRun())
      else:
        let `witId` {.used.} = `witness`
        when not (`convertible`):
          decidedReplay(replayNotRun())
        else:
          # RFC-0005 S8ct: the run is in a child: the host learns how it ended.
          let `childRes` = `runChild`
          startedReplay(`childRes`, `lossy` or `extraLossy` or `converted`)

proc emitReplayWitness*(fn: NimNode; params: seq[IRParam];
                        witness, target, pathTaint: NimNode;
                        extraLossy: NimNode = newLit(false);
                        nilDeref: NimNode = newLit(false);
                        timeoutMs: NimNode = newLit(
                          SymexSettings().replayTimeoutMs);
                        child: ChildWitness = ChildWitness();
                        hoist: NimNode = nil): NimNode =
  ## `emitStartReplay`, waited out: an expression of type `ReplayResult`.
  newCall(bindSym"awaitReplay",
          emitStartReplay(fn, params, witness, target, pathTaint, extraLossy,
                          nilDeref, timeoutMs, child, hoist))

proc methodPrelude*(fn: NimNode): NimNode =
  ## RFC-0005 S8bn (item 6). nil when every method `fn` calls (transitively)
  ## is registered (`dsl_parser.methodRegistry`); otherwise the statements
  ## that register them, emitted into the CALLER's scope, where each name
  ## resolves to every overload visible there. The entry macro then expands
  ## again after them, and its parse dispatches each method call over the
  ## overrides (`methodDispatchStmt`). A name not visible at the caller is
  ## recorded as such, and its calls stay declined.
  let names = unregisteredMethodNames(fn)
  if names.len == 0: return nil
  result = newStmtList()
  for nm in names:
    let id = ident(nm)
    let reg = newCall(bindSym"symexRegisterMethods", newLit(nm), id)
    let none = newCall(bindSym"symexRegisterNoMethods", newLit(nm))
    result.add quote do:
      when declared(`id`): `reg`
      else: `none`
