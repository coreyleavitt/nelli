## RFC-0005 S8cu. Which runtime checks a walked routine was compiled with.
##
## The walker models Nim's default checks, and a routine compiled without one
## of them runs without it: reporting its raise is a false verdict. A routine's
## check options live on its compiler symbol (`PSym.options`), which no macro
## API reads. Probed on the pinned toolchain: the typed AST of a routine is the
## same under `{.push checks: off.}` (a `nnkCheckedFieldExpr` and all, equal
## `symBodyHash`, an empty pragma slot), and `compileOption` reports the options
## where it is expanded, which is usually after the `{.pop.}`. So this reads the
## routine's source: the state of the check pragmas at its position, in the
## module it belongs to, on top of the command line's options.
##
## What the native runs settled (`tests/tsymex_rfc0005_s8cu_*.nim` pins each):
##
## - A routine and a generic take the options at their DEFINITION. A generic
##   defined under a push and instantiated elsewhere runs unchecked; one defined
##   clean and instantiated under a push runs checked.
## - A template's body and an inline iterator's take them from the routine they
##   expand into, so neither is a routine here: the routine they land in answers.
##   A closure iterator is a routine.
## - A pragma cannot sit on a routine. `proc f() {.checks: off.}` and
##   `{.pragma: x, checks: off.}` with `proc f() {.x.}` or `{.push x.}` do not
##   compile. `{.x.}` as a statement does, and `{.pragma: x, push, checks: off.}`
##   with `{.x.}` pushes.
## - `{.checks: off.}` as a statement holds until a `{.pop.}` restores what was
##   pushed, or the module ends. `{.push checks: off.}` before an `import` reaches
##   a module first compiled there, and what that module imports.
## - `checks: on` and `floatChecks: on` turn the float checks ON, which are off by
##   default, and the walker does not model them.
## - `nilChecks` is no option: `{.nilChecks: off.}` does not compile and
##   `{.push nilChecks: off.}` changes nothing. It is not read.
##
## Fails closed: an unread file, an undecided `when`, a value that is not a
## literal, and a position that cannot be placed all read as the check being off.
##
## Not visible to any of this (`docs/migration/0.9.0.md`): a check pragma built by
## a macro from strings, a pushing template or macro from another module, an
## importer that nothing in the walk reads.
import std/[macros, os, strutils, tables]

{.warning[Deprecated]: off.}   # `NimNode.owner`: no replacement in 2.2.10

type
  CheckOption* = enum
    coField = "fieldChecks"
    coOverflow = "overflowChecks"
    coRange = "rangeChecks"
    coBound = "boundChecks"
    coObj = "objChecks"
    coNan = "nanChecks"
    coInf = "infChecks"

  CheckState* = object
    ## Per option, whether it may be off and whether it may be on at a position.
    ## Both, where the scan cannot tell.
    maybeOff*, maybeOn*: set[CheckOption]

  ScanEvent = object
    line, col: int
    st: CheckState

  ScanVisit = object
    ## One reading of one file. A file included twice has two.
    file: string              ## `normalPath`ed
    events: seq[ScanEvent]
    regions: seq[tuple[first, last: int]]   ## template and macro definitions

  ModuleScan* = object
    visits: seq[ScanVisit]
    unknown: string           ## why a part of the module could not be read
    everything: CheckState    ## the union over every position
    importLeak: seq[tuple[name: string, opts: set[CheckOption]]]
      ## what an `import` under a push hands the module it names

  Scanner = object
    res: ModuleScan
    cur, hidden: CheckState
    stack: seq[CheckState]
    ambiguous: int            ## stack entries up to here may not have been pushed
    pending: bool             ## `cur` moved without an event yet
    assume: Table[string, bool]   ## one world's undecided conditions
    forkConds: seq[string]    ## undecided conditions a stack or check pragma is under
    users: Table[string, seq[NimNode]]
    visit: int
    including: seq[string]

const
  defaultOn* = {coField, coOverflow, coRange, coBound, coObj}
  defaultOff* = {coNan, coInf}
  allChecks = defaultOn + defaultOff

const commandLineChecks*: CheckState = block:
  ## Read at this module's compilation, when no user `push` is open unless the
  ## user imported nelli under one (then every routine reads as that push).
  var on: set[CheckOption]
  when compileOption("fieldChecks"): on.incl coField
  when compileOption("overflowChecks"): on.incl coOverflow
  when compileOption("rangeChecks"): on.incl coRange
  when compileOption("boundChecks"): on.incl coBound
  when compileOption("objChecks"): on.incl coObj
  when compileOption("nanChecks"): on.incl coNan
  when compileOption("infChecks"): on.incl coInf
  CheckState(maybeOn: on, maybeOff: allChecks - on)

proc deviation*(st: CheckState): set[CheckOption] =
  ## The options on which the code differs from what the walker models.
  (st.maybeOff * defaultOn) + (st.maybeOn * defaultOff)

proc normalPath*(p: string): string =
  ## For comparing: Windows reports `\\`. A file is READ by the path as the
  ## compiler reported it, never one rebuilt from this.
  p.replace('\\', '/')

proc merge(a, b: CheckState): CheckState =
  CheckState(maybeOff: a.maybeOff + b.maybeOff, maybeOn: a.maybeOn + b.maybeOn)

proc checksNamed(name: string): set[CheckOption] =
  case name.toLowerAscii.replace("_", "")
  of "checks": allChecks
  of "floatchecks": {coNan, coInf}
  of "nanchecks": {coNan}
  of "infchecks": {coInf}
  of "fieldchecks": {coField}
  of "overflowchecks": {coOverflow}
  of "rangechecks": {coRange}
  of "boundchecks": {coBound}
  of "objchecks": {coObj}
  else: {}

proc nameOf(n: NimNode): string =
  if n.kind in {nnkIdent, nnkSym}: n.strVal
  elif n.kind == nnkAccQuoted and n.len == 1: nameOf(n[0])
  else: ""

proc turnsOn(v: NimNode): int =
  ## 1 on, 0 off, -1 for a value that is no literal (a `const` is legal).
  case nameOf(v).toLowerAscii
  of "on", "true": 1
  of "off", "false": 0
  else: -1

proc applyTo(st: var CheckState; opts: set[CheckOption]; v: NimNode) =
  let t = turnsOn(v)
  if t != 1: st.maybeOff = st.maybeOff + opts
  if t != 0: st.maybeOn = st.maybeOn + opts
  if t == 1: st.maybeOff = st.maybeOff - opts
  if t == 0: st.maybeOn = st.maybeOn - opts

proc addEvent(sc: var Scanner; n: NimNode) =
  let st = merge(sc.cur, sc.hidden)
  sc.res.everything = merge(sc.res.everything, st)
  let li = n.lineInfoObj
  sc.res.visits[sc.visit].events.add ScanEvent(line: li.line, col: li.column, st: st)
  sc.pending = false

proc applyPragma(sc: var Scanner; n: NimNode; depth = 0) =
  ## In order, as `{.push a, b.}` and an expanded `{.x.}` are read.
  for i in 0 ..< n.len:
    let it = n[i]
    if it.kind == nnkExprColonExpr and nameOf(it[0]).toLowerAscii == "pragma":
      var items: seq[NimNode]
      for j in i + 1 ..< n.len: items.add n[j]
      sc.users[nameOf(it[1])] = items
      return
    if it.kind == nnkExprColonExpr:
      let opts = checksNamed(nameOf(it[0]))
      if opts != {}: applyTo(sc.cur, opts, it[1])
    else:
      let name = nameOf(it)
      if name.toLowerAscii == "push":
        sc.stack.add sc.cur
      elif name.toLowerAscii == "pop":
        if sc.stack.len > 0:
          let wasAmbiguous = sc.stack.len <= sc.ambiguous
          let top = sc.stack.pop()
          sc.cur = if wasAmbiguous: merge(sc.cur, top) else: top
          sc.ambiguous = min(sc.ambiguous, sc.stack.len)
      elif name in sc.users and depth < 16:
        applyPragma(sc, newTree(nnkPragma, sc.users[name]), depth + 1)

proc decide(c: NimNode): int =
  ## 1 true, 0 false, -1 undecided. A macro cannot evaluate `defined(x)` for a
  ## name it only holds as text, so that is undecided.
  case c.kind
  of nnkIdent, nnkSym:
    case nameOf(c).toLowerAscii
    of "true": 1
    of "false": 0
    else: -1
  of nnkPar:
    if c.len == 1: decide(c[0]) else: -1
  of nnkPrefix:
    if c.len == 2 and nameOf(c[0]) == "not":
      let d = decide(c[1])
      if d < 0: -1 else: 1 - d
    else: -1
  of nnkInfix:
    if c.len != 3: return -1
    let a = decide(c[1])
    let b = decide(c[2])
    case nameOf(c[0])
    of "and":
      if a == 0 or b == 0: 0 elif a == 1 and b == 1: 1 else: -1
    of "or":
      if a == 1 or b == 1: 1 elif a == 0 and b == 0: 0 else: -1
    of "==", "!=":
      # `hostOS` and `hostCPU` are the target's at macro time too (the one
      # `include "$projectpath/..."` in `system.nim` is under `hostOS`).
      if c[2].kind != nnkStrLit: return -1
      let here =
        case nameOf(c[1])
        of "hostOS": hostOS
        of "hostCPU": hostCPU
        else: return -1
      if (here == c[2].strVal) == (nameOf(c[0]) == "=="): 1 else: 0
    else: -1
  else: -1

proc lastLine(n: NimNode): int =
  result = n.lineInfoObj.line
  for c in n: result = max(result, lastLine(c))

proc collectHidden(sc: var Scanner; n: NimNode) =
  ## A check pragma in a template's or a macro's body applies wherever it is
  ## expanded, which the text does not say: from here on, it may apply.
  if n.kind == nnkPragma:
    var probe = Scanner(users: sc.users)
    probe.res.visits.add ScanVisit()
    applyPragma(probe, n)
    let changed = CheckState(
      maybeOff: probe.cur.maybeOff, maybeOn: probe.cur.maybeOn)
    sc.hidden = merge(sc.hidden, changed)
  else:
    for c in n: collectHidden(sc, c)

proc walk(sc: var Scanner; n: NimNode)

var parsedFiles {.compileTime.}: Table[string, tuple[text: string, ast: NimNode]]

proc movesState(n: NimNode): bool =
  ## Does this `when` branch hold a pragma that moves the stack or a check?
  case n.kind
  of nnkPragma:
    for it in n:
      let name = (if it.kind == nnkExprColonExpr: nameOf(it[0]) else: nameOf(it)).toLowerAscii
      if name in ["push", "pop", "pragma"] or checksNamed(name) != {}: return true
    # A user pragma's name: not known here without the scanner, and not worth one.
    n.len == 1 and n[0].kind == nnkIdent
  of nnkStmtList, nnkWhenStmt, nnkElifBranch, nnkElifExpr, nnkElse, nnkElseExpr,
     nnkBlockStmt, nnkIfStmt:
    for c in n:
      if movesState(c): return true
    false
  else: false

proc readSource(path: string; text: var string): string =
  ## "" and `text`, or why not. `staticRead` of a missing file ends the compile,
  ## and a file with a source filter is not the text the compiler parsed.
  if not fileExists(path): return "cannot read `" & path & "`"
  text = staticRead(path)
  if text.startsWith("#?"): return "`" & path & "` has a source filter"
  ""

proc scanFile(sc: var Scanner; path, text: string) =
  sc.res.visits.add ScanVisit(file: normalPath(path))
  let saved = sc.visit
  sc.visit = sc.res.visits.high
  sc.including.add path
  let st = merge(sc.cur, sc.hidden)
  sc.res.everything = merge(sc.res.everything, st)
  sc.res.visits[sc.visit].events.add ScanEvent(line: 0, col: 0, st: st)
  try:
    # Keyed by path, checked by text: hashing a `system.nim`-sized key on every
    # lookup spends the VM's iteration budget.
    if path notin parsedFiles or parsedFiles[path].text != text:
      parsedFiles[path] = (text: text, ast: parseStmt(text, path))
    walk(sc, parsedFiles[path].ast)
  except ValueError as e:
    if sc.res.unknown.len == 0:
      sc.res.unknown = "cannot parse `" & path & "`: " & e.msg
  discard sc.including.pop()
  sc.visit = saved
  sc.pending = true

proc includePathOf(n: NimNode): string =
  case n.kind
  of nnkStrLit, nnkRStrLit, nnkTripleStrLit: n.strVal
  of nnkIdent, nnkSym: n.strVal
  of nnkInfix:
    if n.len == 3 and nameOf(n[0]) == "/":
      let a = includePathOf(n[1])
      let b = includePathOf(n[2])
      if a.len > 0 and b.len > 0: a & "/" & b else: ""
    else: ""
  of nnkPrefix:
    if n.len == 2 and nameOf(n[0]) == "./": includePathOf(n[1]) else: ""
  else: ""

proc resolveInclude(fromFile, rel: string): string =
  ## Beside the including file, then under each directory above it (`include
  ## system/x` from `lib/system.nim`, `std/private/x` from anywhere under `lib`).
  let name = if rel.endsWith(".nim"): rel else: rel & ".nim"
  var dir = fromFile.parentDir
  while dir.len > 0:
    let cand = dir / name
    if fileExists(cand): return cand
    let up = dir.parentDir
    if up == dir: break
    dir = up
  ""

proc scanInclude(sc: var Scanner; n: NimNode) =
  let fromFile = sc.including[^1]
  let rel = includePathOf(n)
  let path = if rel.len > 0: resolveInclude(fromFile, rel) else: ""
  if path.len == 0:
    if sc.res.unknown.len == 0:
      sc.res.unknown = "cannot place `include " & n.repr & "` from `" & fromFile & "`"
    return
  for f in sc.including:
    if normalPath(f) == normalPath(path):
      if sc.res.unknown.len == 0:
        sc.res.unknown = "`" & path & "` includes itself"
      return
  var text: string
  let why = readSource(path, text)
  if why.len > 0:
    if sc.res.unknown.len == 0: sc.res.unknown = why
    return
  scanFile(sc, path, text)

proc importedNames(n: NimNode; into: var seq[string]) =
  case n.kind
  of nnkIdent, nnkSym, nnkStrLit, nnkRStrLit, nnkTripleStrLit:
    into.add n.strVal.extractFilename.changeFileExt("")
  of nnkInfix:
    if n.len == 3:
      if nameOf(n[0]) == "as": importedNames(n[1], into)
      else: importedNames(n[2], into)
  of nnkPrefix:
    if n.len == 2: importedNames(n[1], into)
  of nnkBracket:
    for c in n: importedNames(c, into)
  else: discard

proc noteImport(sc: var Scanner; n: NimNode) =
  ## What is pushed here reaches a module first compiled by this import, and what
  ## that module imports in turn.
  let opts = deviation(merge(sc.cur, sc.hidden)) - deviation(commandLineChecks)
  if opts == {}: return
  var names: seq[string]
  if n.kind == nnkImportStmt:
    for c in n: importedNames(c, names)
  elif n.len > 0:
    importedNames(n[0], names)
  for nm in names: sc.res.importLeak.add (name: nm, opts: opts)

proc walkWhen(sc: var Scanner; n: NimNode) =
  var alts: seq[NimNode]
  var exhaustive = false
  for br in n:
    if br.kind in {nnkElifBranch, nnkElifExpr}:
      let text = br[0].repr
      var d = decide(br[0])
      if d < 0 and text in sc.assume:
        d = if sc.assume[text]: 1 else: 0
      elif d < 0 and movesState(br[1]) and text notin sc.forkConds:
        sc.forkConds.add text
      if d == 0: continue
      alts.add br[1]
      if d == 1:
        exhaustive = true
        break
    elif br.kind in {nnkElse, nnkElseExpr}:
      alts.add br[0]
      exhaustive = true
  if exhaustive and alts.len == 1:
    walk(sc, alts[0])
    return
  # An undecided condition: every branch from the same state, then their union.
  # Branches that leave different stacks make the pops below them ambiguous.
  let (savedCur, savedStack) = (sc.cur, sc.stack)
  var joined = if exhaustive: CheckState() else: savedCur
  var stackJoin = savedStack
  var ambiguous = sc.ambiguous
  for alt in alts:
    sc.cur = savedCur
    sc.stack = savedStack
    addEvent(sc, if alt.len > 0: alt[0] else: alt)
    walk(sc, alt)
    joined = merge(joined, sc.cur)
    if sc.stack.len != savedStack.len:
      ambiguous = max(ambiguous, max(sc.stack.len, savedStack.len))
    if sc.stack.len > stackJoin.len:
      let grown = sc.stack
      for i in 0 ..< stackJoin.len: stackJoin[i] = merge(stackJoin[i], grown[i])
      for i in stackJoin.len ..< grown.len: stackJoin.add grown[i]
    else:
      for i in 0 ..< sc.stack.len: stackJoin[i] = merge(stackJoin[i], sc.stack[i])
  sc.cur = joined
  sc.stack = stackJoin
  sc.ambiguous = ambiguous
  sc.pending = true

proc walk(sc: var Scanner; n: NimNode) =
  case n.kind
  of nnkStmtList, nnkStmtListExpr:
    for c in n:
      if sc.pending: addEvent(sc, c)
      walk(sc, c)
  of nnkWhenStmt:
    walkWhen(sc, n)
  of nnkPragma:
    applyPragma(sc, n)
    addEvent(sc, n)
  of nnkIncludeStmt:
    for c in n: scanInclude(sc, c)
  of nnkImportStmt, nnkImportExceptStmt, nnkFromStmt:
    noteImport(sc, n)
  of nnkTemplateDef, nnkMacroDef:
    sc.res.visits[sc.visit].regions.add (first: n.lineInfoObj.line, last: lastLine(n))
    let before = sc.hidden
    collectHidden(sc, n)
    if sc.hidden != before: sc.pending = true
  of nnkBlockStmt, nnkIfStmt, nnkElifBranch, nnkElse, nnkTryStmt, nnkExceptBranch,
     nnkFinally, nnkForStmt, nnkWhileStmt, nnkCaseStmt, nnkOfBranch, nnkStaticStmt:
    for c in n: walk(sc, c)
  else:
    discard

const maxForkConds = 4
  ## `when c: {.push ....}` then `when c: {.pop.}` balance in each world, not in
  ## their union. Up to this many distinct condition texts, each combination is
  ## read on its own and a position gets the union over them; past it, the rest
  ## join in one reading, where a pop below them leaves both states.

proc scanWorld(path, text: string; assume: Table[string, bool]): Scanner =
  result = Scanner(cur: commandLineChecks, assume: assume)
  result.res.everything = commandLineChecks
  scanFile(result, path, text)

proc scanModuleText*(path, text: string): ModuleScan =
  ## The scan of a module whose text is at hand. An `include` is read from disk.
  let first = scanWorld(path, text, initTable[string, bool]())
  if first.forkConds.len == 0: return first.res
  let k = min(first.forkConds.len, maxForkConds)
  result.everything = commandLineChecks
  for mask in 0 ..< (1 shl k):
    var assume = initTable[string, bool]()
    for i in 0 ..< k: assume[first.forkConds[i]] = (mask and (1 shl i)) != 0
    let w = scanWorld(path, text, assume)
    result.visits.add w.res.visits
    result.everything = merge(result.everything, w.res.everything)
    result.importLeak.add w.res.importLeak
    if result.unknown.len == 0: result.unknown = w.res.unknown

proc scanModule*(path: string): ModuleScan =
  var text: string
  let why = readSource(path, text)
  if why.len > 0:
    result.unknown = why
    return
  scanModuleText(path, text)

proc stateAt*(m: ModuleScan; file: string; line, col: int): CheckState =
  ## The options at a position. A position inside a template or a macro is where
  ## the routine was written, not where it was expanded (the module's union); so
  ## is a file the module's text never reaches.
  let file = normalPath(file)
  var found = false
  for v in m.visits:
    if v.file != file: continue
    for r in v.regions:
      if line >= r.first and line <= r.last: return m.everything
    var here = commandLineChecks
    for e in v.events:
      if e.line < line or (e.line == line and e.col <= col): here = e.st
      else: break
    if found: result = merge(result, here)
    else: result = here
    found = true
  if not found: result = m.everything

proc unknownReason*(m: ModuleScan): string = m.unknown
proc importLeak*(m: ModuleScan): set[CheckOption] =
  for l in m.importLeak: result = result + l.opts

# ---- a routine ---------------------------------------------------------------

proc moduleFileOf(routine: NimNode; fallback: string): string =
  ## The file of the module `routine` belongs to, which an `include`d routine's
  ## own line info does not name. As the compiler reports it.
  if routine.kind != nnkSym: return fallback
  var o = routine
  for _ in 0 .. 64:
    if o.kind != nnkSym: return fallback
    if o.symKind == nskModule: return o.lineInfoObj.filename
    o = o.owner
  fallback

proc isOwnRuntime(path: string): bool =
  ## Nelli's own engine, which pushes for its own reasons and is not the program.
  "/nelli/smt/" in path or path.endsWith("/nelli/engine/markers.nim")

proc isSystemFile(path: string): bool =
  ## Compiled before any user code, so no user's import reaches it.
  path.endsWith("/lib/system.nim") or "/lib/system/" in path

proc isStdlibFile(path: string): bool =
  isSystemFile(path) or "/lib/pure/" in path or "/lib/std/" in path or
    "/lib/core/" in path or "/lib/impure/" in path

proc typeHasFloat(t: NimNode; generic: bool; depth = 0): bool =
  ## `generic`: an uninstantiated `T` may be a float. A callee's own `T` says nothing
  ## of this routine's arithmetic.
  if t.typeKind in {ntyFloat, ntyFloat32, ntyFloat64, ntyFloat128}: return true
  if generic and t.typeKind == ntyGenericParam: return true
  if depth < 4 and t.kind == nnkBracketExpr:
    for c in t:
      if typeHasFloat(c, generic, depth + 1): return true

proc touchesFloat(n: NimNode): bool =
  ## The float checks guard float arithmetic alone.
  case n.kind
  of nnkFloatLit .. nnkFloat64Lit: true
  of nnkSym:
    case n.symKind
    of nskVar, nskLet, nskParam, nskConst, nskResult, nskForVar, nskField:
      typeHasFloat(n.getType, true)
    of nskProc, nskFunc, nskConverter, nskMethod:
      typeHasFloat(n.getType, false)
    else: false
  else:
    for c in n:
      if touchesFloat(c): return true
    false

var moduleScans {.compileTime.}: Table[string, ModuleScan]
var runLeaks {.compileTime.}: seq[tuple[root, name: string; opts: set[CheckOption]]]

proc beginCheckOptionRun*() =
  ## Each entry macro's parse: what one program's importers leak is its own.
  runLeaks.setLen 0

type RoutineChecks* = object
  checks*: set[CheckOption]
  why*: string                ## set where the position could not be read at all

proc routinePlace*(impl: NimNode): string =
  ## For a message: the routine, its file and line.
  let li = impl.lineInfoObj
  "`" & impl[0].repr & "` (" & li.filename.extractFilename & ":" & $li.line & ")"

proc routineChecks*(impl: NimNode): RoutineChecks =
  ## How `impl` (a typed routine definition) differs from the model.
  let li = impl.lineInfoObj
  let file = normalPath(li.filename)
  if isOwnRuntime(file): return
  let rootRaw = moduleFileOf(impl[0], li.filename)
  let root = normalPath(rootRaw)
  if isOwnRuntime(root): return
  if root notin moduleScans: moduleScans[root] = scanModule(rootRaw)
  if moduleScans[root].unknown.len > 0:
    return RoutineChecks(checks: allChecks, why: moduleScans[root].unknown)
  result.checks = deviation(stateAt(moduleScans[root], file, li.line, li.column))
  # A user's importer hands on what it pushed to any module this walk reaches: the
  # chain from what it names is not read. `system.nim` and `math.nim` import under
  # their own pushes, so a stdlib importer hands it on to what it names alone.
  for l in moduleScans[root].importLeak:
    runLeaks.add (root: root, name: l.name, opts: l.opts)
  let moduleName = root.extractFilename.changeFileExt("")
  for l in runLeaks:
    if l.root == root: continue
    if l.name == moduleName or (not isStdlibFile(l.root) and not isSystemFile(root)):
      result.checks = result.checks + l.opts
  if result.checks * defaultOff != {} and not touchesFloat(impl[6]):
    result.checks = result.checks - defaultOff
