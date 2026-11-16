## nelli/smt/proc_lift -- the proc-value lift of a replay: how a module-level
## proc variable's value crosses the process boundary as a routine-table slot
## (`emitProcValueLift`, `procValueCode`), and the memoised undefined-kinds
## of a routine.
##
## RFC-0016 D6: moved out of `symex.nim` unchanged. The `{.compileTime.}`
## `routineUndefinedMemo` lives here and nowhere else.

import std/[macros, sets, tables, options, strutils]
import ./dsl
import ./replay_footprint
import ./replay_settle
import ./heldset
import ./routine_table
import ./replaywire
import ./replayproc

proc procValueCode[T: proc](x: T): pointer =
  ## RFC-0016 W3-z R7. The routine a proc value names, as the address the
  ## replay's routine table holds; nil for a nil value. RFC-0016 W3-z R10: a
  ## closure with a captured environment names its routine too (a nested
  ## one, `ReplayFootprint.nested`); what the environment holds was checked
  ## by the scratch wire (`envRefusal`, `WireWriter.envOk`).
  if x.isNil: return nil
  when sizeof(T) > sizeof(pointer):
    rawProc(x)
  else:
    cast[pointer](x)

var routineUndefinedMemo {.compileTime.}: Table[string, set[UbKind]]

proc routineUndefinedMemoised(r: NimNode): set[UbKind] =
  ## RFC-0016 W3-z R7. `routineUndefinedKinds`, once per routine.
  let key = routineKey(r)
  if key notin routineUndefinedMemo:
    routineUndefinedMemo[key] = routineUndefinedKinds(r)
  routineUndefinedMemo[key]

proc formalsShape(t: NimNode): string =
  ## RFC-0016 W3-z R7. A proc type's formals and result, without its calling
  ## convention: a nimcall routine converts to a closure type of the same
  ## shape, so the two hold the same routines.
  if t.kind == nnkProcTy and t.len > 0 and t[0].kind == nnkFormalParams:
    var parts: seq[string]
    for i in 0 ..< t[0].len:
      let d = t[0][i]
      if d.kind == nnkIdentDefs:
        for _ in 0 ..< d.len - 2: parts.add d[^2].repr
      else: parts.add d.repr
    parts.join("|")
  else: "?" & t.repr

proc emitProcValueLift*(fn: NimNode; keys: seq[string]; sites: NimNode): NimNode =
  ## RFC-0016 W3-z R7. An expression of type `ProcValueLift`: which routine
  ## each proc-valued variable the walk reported (`sites`, the run's
  ## `RawResult.procValueSites`) held when the replay ran, read in the host
  ## before the child starts (a forked child copies the host; a re-executed
  ## one is handed these values), and what the routine's body may reach.
  ##
  ## A variable's value at the run's start is the routine a call through it
  ## runs when no code the run may execute writes it otherwise: the code is
  ## the replay's footprint (`replayFootprint`; open, nothing is named), every
  ## use of the variable in it is a call, a comparison, or an assignment of a
  ## routine's symbol (`procValueUses`), whose routine joins the variable's,
  ## and the run cannot reach code the footprint did not read, which holds
  ## when every proc value the run's state holds names a routine of the
  ## footprint: the state is written to a scratch wire whose routine table is
  ## the footprint's (`replaywire.nim`, the check a re-executed child's hand-
  ## over makes), and a value it cannot carry (a closure with an
  ## environment, a routine the code does not name) names nothing. `keys`
  ## are the variables the SUT's IR names (`irCollectProcValueSites`); a
  ## reported variable with no reading here names nothing either.
  let liftT = bindSym"ProcValueLift"
  proc unnamed(why: string): NimNode =
    nnkObjConstr.newTree(bindSym"ProcValueLift",
                         nnkExprColonExpr.newTree(ident"why", newLit(why)))
  if keys.len == 0:
    return unnamed("the program names no proc-valued variable the run calls through")
  let fp = replayFootprint(fn)
  if fp.open:
    return unnamed("the replayed code is open: " & fp.why)
  for g in fp.globals:
    if not isWireableType(g.getTypeInst):
      return unnamed("`" & g.strVal & "`, of a type the wire cannot carry")
  let okId = genSym(nskVar, "procValuesNamed")
  let whyId = genSym(nskVar, "procValuesWhy")
  let ksId = genSym(nskVar, "procValueKinds")
  let siteId = genSym(nskForVar, "procValueSite")
  let codeId = genSym(nskLet, "procValueCode")
  let wr = genSym(nskVar, "procValueWire")
  let tabId = genSym(nskLet, "procValueTable")
  # RFC-0016 W3-z R10: the table names nested routines too (a closure's code),
  # where module-level code can take their addresses (`nestedRoutineAddrs`).
  let table = emitRoutineTable(fp)
  let tableExpr = table.procs
  let envOkExpr = table.envOk
  let envBenignExpr = table.envBenign
  let slots = fp.routines & fp.nested
  var putGlobals = newStmtList()
  for g in fp.globals:
    let gLit = newLit("`" & g.strVal & "` holds ")
    putGlobals.add quote do:
      if `okId`:
        try: wirePut(`wr`, `g`)
        except WireError as e:
          `okId` = false
          `whyId` = `gLit` & e.msg
  let codeOf = bindSym"procValueCode"
  let setOf = bindSym"ubSetOf"
  var caseStmt = nnkCaseStmt.newTree(siteId)
  for key in keys:
    if key notin procValueSites: continue
    let g = procValueSites[key]
    var assigned: seq[NimNode]
    var understood = true
    for r in fp.userRoutines:
      let impl =
        try: r.getImpl
        except CatchableError: newEmptyNode()
      if impl.kind in RoutineNodes and impl.len > 6 and
         not procValueUses(impl[6], g, assigned):
        understood = false
        break
    if not understood: continue
    # RFC-0016 W3-z R8: what the variable may hold AT its calls, in the
    # order the run executes, not every routine stored in it anywhere.
    let held = heldAtCalls(fn, g, fp.userRoutines, assigned)
    var staticKinds: set[UbKind]
    for a in held.routines: staticKinds = staticKinds + routineUndefinedMemoised(a)
    let staticMask = newLit(ubMaskOf(staticKinds))
    if not held.start:
      # No call runs the value the variable held as the run began: what it
      # held then is not read, and need not name a routine.
      caseStmt.add nnkOfBranch.newTree(newLit(key), quote do:
        `ksId` = `ksId` + `setOf`(`staticMask`))
      continue
    let gName = newLit("`" & g.strVal & "`")
    var chain = nnkIfStmt.newTree(nnkElifBranch.newTree(
      infix(codeId, "==", newNilLit()),
      quote do:
        `okId` = false
        `whyId` = `gName` & " is nil when the run starts"))
    # A value of `g`'s type names a routine of its shape (a cast to another
    # is undefined already); only those are asked about, and read.
    let shape = formalsShape(g.getTypeImpl)
    for i, r in slots:
      if formalsShape(r.getTypeImpl) != shape: continue
      let mask = newLit(ubMaskOf(routineUndefinedMemoised(r)))
      let at = newLit(i)
      chain.add nnkElifBranch.newTree(
        quote do: `codeId` == `tabId`[`at`],
        quote do:
          `ksId` = `ksId` + `setOf`(`mask`))
    let notFound = newLit(" holds a routine the replayed code does not " &
      "name, or names only nested in a routine where the settle cannot " &
      "take its address (it runs inside a routine, not at module level)")
    chain.add nnkElse.newTree(quote do:
      `okId` = false
      `whyId` = `gName` & `notFound`)
    caseStmt.add nnkOfBranch.newTree(newLit(key), quote do:
      `ksId` = `ksId` + `setOf`(`staticMask`)
      let `codeId` = `codeOf`(`g`)
      `chain`)
  if caseStmt.len == 1:
    return unnamed("no proc-valued variable the run calls through is read " &
                   "only by calls, comparisons and stores of a routine")
  let unread = newLit(" is called through by the run, but a use of it is " &
    "not a call, a comparison or a store of a routine")
  caseStmt.add nnkElse.newTree(quote do:
    `okId` = false
    `whyId` = "`" & `siteId` & "`" & `unread`)
  result = quote do:
    block:
      var `okId` = `sites`.len > 0
      var `whyId` = ""
      var `ksId`: set[UbKind]
      let `tabId` = `tableExpr`
      if `okId`:
        var `wr`: WireWriter
        `wr`.procs = `tabId`
        `wr`.envOk = `envOkExpr`
        # RFC-0016 W3-z R11: a scratch wire, whose environments are not
        # written: an environment whose destructor runs no user code is named.
        `wr`.envBenign = `envBenignExpr`
        `wr`.scratch = true
        `putGlobals`
        if `okId`:
          let hook = putHostHooks(`wr`)
          if hook.len > 0:
            `okId` = false
            `whyId` = "the host set a runtime hook the replayed code does " &
                      "not name: " & hook
      if `okId`:
        for `siteId` in `sites`:
          `caseStmt`
          if not `okId`: break
      `liftT`(named: `okId`, kinds: `ksId`, why: `whyId`)
