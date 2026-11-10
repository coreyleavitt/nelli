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
##   default. Where they are on at every reading the walker models them
##   (`RoutineChecks.nanOn`/`infOn`, RFC-0016 PRC-07); where a reading leaves
##   them either way the routine declines.
## - `nilChecks` is no option: `{.nilChecks: off.}` does not compile and
##   `{.push nilChecks: off.}` changes nothing. It is not read.
##
## Fails closed: an unread file, an undecided `when`, a value that is not a
## literal, and a position that cannot be placed all read as the check being off.
##
## A push the text does not show (a macro building the pragma, a pushing template
## or macro from another module) is caught by its `{.pop.}`: a pop with no push
## the scan read. Every call statement before it then reads as possibly pushing
## every check off, up to that pop; such a pop with no call before it makes the
## module unknown. An importer is read wherever the import graph from the
## routine's module or the project file reaches it.
##
## Not visible to any of this (`docs/migration/0.9.0.md`): a hidden push whose pop
## is hidden too (or that never pops), and an importer outside that graph.
import std/[macros, os, strutils, tables, compilesettings]
import ./buildprofile
import ./errorkind
import ./admission     ## RFC-0016 ADM-IR: `Admit`
import ./stdlib_rows   ## RFC-0016 ADM-IR: `StdlibBody`
import ./scan_kinds    ## RFC-0016 K2F-3: the shared scan kind lists
export buildprofile.CheckOption   ## moved to buildprofile (RFC-0016 W1-c1a)

{.warning[Deprecated]: off.}   # `NimNode.owner`: no replacement in 2.2.10

type
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
    imports: seq[string]      ## user modules it imports, as found on disk
    hiddenPops: seq[tuple[file: string, line: int]]
      ## a `{.pop.}` with no push the scan read: something unseen pushed

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
    knownPops: seq[tuple[file: string, line: int]]
      ## the first reading's `hiddenPops`, read again with them in view
    candOpen: bool            ## a call before a hidden pop may have pushed
    candSaved: CheckState

const
  defaultOn* = {coField, coOverflow, coRange, coBound, coObj}
  defaultOff* = {coNan, coInf}
  allChecks = defaultOn + defaultOff
  everyOption = allChecks + {coAssert}

const commandLineChecks*: CheckState = block:
  ## Read at this module's compilation, when no user `push` is open unless the
  ## user imported nelli under one (then every routine reads as that push).
  let on = buildSemantics.checks
  CheckState(maybeOn: on, maybeOff: everyOption - on)

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
  of "checks": everyOption   # natively, `{.push checks: off.}` drops `assert` too
  of "assertions": {coAssert}
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
        if sc.stack.len == 0:
          let here = (file: sc.res.visits[sc.visit].file, line: it.lineInfoObj.line)
          sc.res.hiddenPops.add here
          if sc.candOpen:
            sc.cur = sc.candSaved
            sc.candOpen = false
          elif here in sc.knownPops and sc.res.unknown.len == 0:
            sc.res.unknown = "a `{.pop.}` at " & here.file.extractFilename & ":" &
              $here.line & " pops a push the scan cannot see"
        elif sc.stack.len > 0:
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
  else: -1  # k2: fail-closed: -1 is undecided; walkWhen walks every branch and joins

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
  else: false  # k2: fail-closed: false only skips forkConds; walkWhen still joins the branch

proc anchored(p: string): string =
  ## `p`, absolute. A search path given on the command line (`--path:src`, as
  ## the Windows legs pass it) stays relative to the compiler's working
  ## directory, which `fileExists` resolves against but `staticRead` does not
  ## (it reads beside this file), and which the VM cannot query. A relative
  ## path is taken under the nearest directory at or above the project that
  ## holds it; "" when none does.
  if p.len == 0 or p.isAbsolute: return p
  var dir = querySetting(projectPath)
  while dir.len > 0:
    if fileExists(dir / p): return dir / p
    let up = dir.parentDir
    if up == dir: break
    dir = up
  ""

proc readSource(path: string; text: var string): string =
  ## "" and `text`, or why not. `staticRead` of a missing file ends the compile,
  ## and a file with a source filter is not the text the compiler parsed.
  let at = anchored(path)
  if at.len == 0 or not fileExists(at): return "cannot read `" & path & "`"
  text = staticRead(at)
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
  else: ""  # k2: fail-closed: "": scanInclude sets res.unknown

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

const unlistedImport = "\0unknown-import"
  ## RFC-0016 K2F-3. An import whose path the scan cannot read: the module's
  ## options are unknown (`noteImport`, `recordImports`).

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
  of nnkPragmaExpr:
    # RFC-0016 K2F-3: `import ./m {.all.}`. Dropped before, so a push the
    # import was under did not leak into `m`.
    if n.len > 0: importedNames(n[0], into)
  else:
    # RFC-0016 K2F-3 (RFC section 8.1): an import shape not listed. Its name
    # cannot be read, so the leak lands on the empty name, which no module
    # has: `unlistedImport` makes the module's options unknown instead.
    into.add unlistedImport

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
  for nm in names:
    if nm == unlistedImport:
      if sc.res.unknown.len == 0:
        sc.res.unknown = "an import under a push whose module cannot be named: `" &
                         n.repr & "`"
      continue
    sc.res.importLeak.add (name: nm, opts: opts)

proc isOwnSource(path: string): bool =
  ## Nelli itself: `src/nelli.nim` and everything under `src/nelli/`.
  const src = normalPath(currentSourcePath().parentDir.parentDir.parentDir)
  let p = normalPath(path)
  p == src & "/nelli.nim" or p.startsWith(src & "/nelli/")

proc isLibraryFile(path: string): bool =
  ## The stdlib and installed packages: not the program's own modules.
  let p = "/" & normalPath(path)     # a relative `_deps/...` as well
  "/lib/pure/" in p or "/lib/std/" in p or "/lib/core/" in p or
    "/lib/impure/" in p or "/lib/system" in p or "/lib/packages/" in p or
    "/lib/deprecated/" in p or "/lib/posix/" in p or "/lib/windows/" in p or
    "/lib/js/" in p or "/lib/wrappers/" in p or "/.nimble/" in p or
    "/_deps/" in p or "/pkgs2/" in p or "/pkgs/" in p or isOwnSource(p)

proc importPathOf(n: NimNode): string =
  ## `a`, `./a`, `../a`, `a/b`, `"a.nim"`; "" for a bracket or an `as`.
  ## RFC-0016 K2F-3: `a {.all.}` is `a`; any other shape is `unlistedImport`.
  case n.kind
  of nnkInfix:
    if n.len == 3 and nameOf(n[0]) == "as": importPathOf(n[1])
    else: includePathOf(n)
  of nnkPrefix:
    if n.len == 2 and nameOf(n[0]) == "../":
      let b = includePathOf(n[1])
      if b.len > 0: "../" & b else: ""
    else: includePathOf(n)
  of nnkPragmaExpr:
    if n.len > 0: importPathOf(n[0]) else: unlistedImport
  of nnkIdent, nnkSym, nnkStrLit, nnkRStrLit, nnkTripleStrLit:
    includePathOf(n)
  of nnkBracket:
    ""    # `recordImports` reads `a/[b, c]` itself
  else:
    unlistedImport

proc recordImports(sc: var Scanner; n: NimNode) =
  ## The user modules this file imports, for the import graph.
  var rels: seq[string]
  if n.kind == nnkImportStmt:
    for c in n:
      if c.kind == nnkInfix and c.len == 3 and c[2].kind == nnkBracket:
        let head = importPathOf(c[1])
        if head == unlistedImport:
          rels.add unlistedImport
          continue
        for b in c[2]:
          let tail = includePathOf(b)
          if head.len > 0 and tail.len > 0: rels.add head & "/" & tail
      else:
        rels.add importPathOf(c)
  elif n.len > 0:
    rels.add importPathOf(n[0])
  let dir = sc.including[^1].parentDir
  for rel in rels:
    if rel == unlistedImport:
      # RFC-0016 K2F-3: an import edge the graph cannot draw; an importer it
      # would reach is not read, so the module's options are unknown.
      if sc.res.unknown.len == 0:
        sc.res.unknown = "an import whose module cannot be named: `" & n.repr & "`"
      continue
    if rel.len == 0 or rel.startsWith("std/") or rel.startsWith("system/"): continue
    let name = if rel.endsWith(".nim"): rel else: rel & ".nim"
    var found = ""
    if fileExists(dir / name): found = dir / name
    else:
      for sp in querySettingSeq(searchPaths):
        if fileExists(sp / name):
          found = sp / name
          break
    # Kept as found if it cannot be anchored: reading it then fails closed.
    if found.len > 0 and anchored(found).len > 0: found = anchored(found)
    if found.len > 0 and not isLibraryFile(found) and found notin sc.res.imports:
      sc.res.imports.add found

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

proc unlistedStatement(sc: var Scanner; n: NimNode) =
  ## RFC-0016 K2F-3. A module-level statement `walk` does not list: the
  ## module's options are unknown (each check reads as possibly off).
  if sc.res.unknown.len == 0:
    sc.res.unknown = "a module-level `" & $n.kind & "` the check scan does " &
                     "not read at line " & $n.lineInfoObj.line

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
    recordImports(sc, n)
  of nnkCall, nnkCommand, nnkCallStrLit, nnkIdent, nnkSym, nnkAccQuoted,
     nnkDotExpr, nnkInfix, nnkPrefix, nnkPostfix, nnkBracketExpr:
    # A call statement before a pop the scan cannot match may be what pushed.
    # RFC-0016 K2F-3: so may a call spelled without parentheses (`pushOff`,
    # `x.pushOff`, an operator), which the scan skipped.
    if not sc.candOpen:
      let li = n.lineInfoObj
      let file = sc.res.visits[sc.visit].file
      for p in sc.knownPops:
        if p.file == file and p.line > li.line:
          sc.candSaved = sc.cur
          sc.candOpen = true
          sc.cur = merge(sc.cur, CheckState(maybeOff: everyOption))
          sc.pending = true
          break
  of nnkTemplateDef, nnkMacroDef:
    sc.res.visits[sc.visit].regions.add (first: n.lineInfoObj.line, last: lastLine(n))
    let before = sc.hidden
    collectHidden(sc, n)
    if sc.hidden != before: sc.pending = true
  of nnkBlockStmt, nnkIfStmt, nnkElifBranch, nnkElse, nnkTryStmt, nnkExceptBranch,
     nnkFinally, nnkForStmt, nnkWhileStmt, nnkCaseStmt, nnkOfBranch, nnkStaticStmt:
    for c in n: walk(sc, c)
  of nnkProcDef, nnkFuncDef, nnkIteratorDef, nnkConverterDef, nnkMethodDef,
     nnkTypeSection, nnkVarSection, nnkLetSection, nnkConstSection,
     nnkCommentStmt, nnkEmpty, nnkDiscardStmt, nnkAsgn, nnkExportStmt,
     nnkMixinStmt, nnkBindStmt, nnkUsingStmt, nnkReturnStmt, nnkBreakStmt,
     nnkContinueStmt, nnkRaiseStmt, nnkDefer, nnkAsmStmt, nnkYieldStmt,
     nnkStrLit .. nnkTripleStrLit, nnkCharLit .. nnkFloat128Lit, nnkNilLit,
     nnkPar, nnkTupleConstr, nnkBracket, nnkCurly, nnkTableConstr, nnkObjConstr,
     nnkExprColonExpr, nnkExprEqExpr, nnkCast, nnkLambda, nnkDo, nnkVarTuple,
     nnkRange, nnkIfExpr, nnkElifExpr, nnkElseExpr, nnkTypeOfExpr,
     nnkPragmaExpr:
    # RFC-0016 K2F-3: no check pragma at this module's level. A routine's
    # body is its own: a push in it declines by its statement (the parser).
    # An expression (a condition, a loop's range, a pattern) pushes nothing.
    discard
  of nnkBlockExpr:
    for c in n: walk(sc, c)
  of nnkPragmaBlock:
    # RFC-0016 K2F-3: `{.cast(gcsafe).}: ...` runs its body here; a check
    # option on the block itself holds for the block only, which this scan
    # does not model.
    var checks = false
    if n.len > 0 and n[0].kind == nnkPragma:
      for it in n[0]:
        let nm = if it.kind == nnkExprColonExpr: nameOf(it[0]) else: nameOf(it)
        if checksNamed(nm) != {}: checks = true
    if checks:
      if sc.res.unknown.len == 0:
        sc.res.unknown = "a check option on a pragma block at " &
                         $n.lineInfoObj.line
    elif n.len > 1:
      walk(sc, n[1])
  else:
    # RFC-0016 K2F-3 (RFC section 8.1): a module-level statement this scan
    # does not list may hold a check pragma it does not see.
    unlistedStatement(sc, n)

const maxForkConds = 4
  ## `when c: {.push ....}` then `when c: {.pop.}` balance in each world, not in
  ## their union. Up to this many distinct condition texts, each combination is
  ## read on its own and a position gets the union over them; past it, the rest
  ## join in one reading, where a pop below them leaves both states.

proc scanWorld(path, text: string; assume: Table[string, bool]): Scanner =
  ## Read twice where a pop matched no push: the second reading knows where.
  result = Scanner(cur: commandLineChecks, assume: assume)
  result.res.everything = commandLineChecks
  scanFile(result, path, text)
  if result.res.hiddenPops.len > 0:
    let pops = result.res.hiddenPops
    result = Scanner(cur: commandLineChecks, assume: assume, knownPops: pops)
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
    for i in w.res.imports:
      if i notin result.imports: result.imports.add i
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

proc moduleStemOf*(sym: NimNode): string =
  ## RFC-0016 K4c. The name of the module a symbol belongs to (`tables` for
  ## `OrderedTable`): the `<module>` of a `stdlibAxis` key.
  normalPath(moduleFileOf(sym, sym.lineInfoObj.filename))
    .extractFilename.changeFileExt("")

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
  of mayScanLeafKinds - {nnkFloatLit .. nnkFloat64Lit}:
    false
  of mayScanNoCodeKinds + mayScanStructuralKinds + RoutineNodes:
    for c in n:
      if touchesFloat(c): return true
    false
  else:
    # RFC-0016 K2F-3 (RFC section 8.1): a kind not listed may compute with
    # floats (`asm` included), so the float checks may matter to it.
    true

var moduleScans {.compileTime.}: Table[string, ModuleScan]
var runLeaks {.compileTime.}: seq[tuple[root, name: string; opts: set[CheckOption]]]
var runReach {.compileTime.}: Table[string, seq[string]]
  ## Per user importer and name: the modules the named one reaches by import,
  ## itself included. Absent where it was not found on disk.
var runSeen {.compileTime.}: seq[string]
var runUnknown {.compileTime.}: string

proc beginCheckOptionRun*() =
  ## Each entry macro's parse: what one program's importers leak is its own.
  runLeaks.setLen 0
  runSeen.setLen 0
  runUnknown = ""
  runReach.clear()

proc reachOf(start: string): seq[string] =
  ## `start` and the user modules its imports reach.
  var queue = @[start]
  while queue.len > 0:
    let raw = anchored(queue.pop())
    let key = normalPath(raw)
    if key in result: continue
    result.add key
    if key notin moduleScans: moduleScans[key] = scanModule(raw)
    for i in moduleScans[key].imports: queue.add i

proc enterGraph(startRaw: string) =
  ## Every user module the import graph from `startRaw` reaches hands on what it
  ## imports under a push, whether or not the walk enters it. One that cannot be
  ## read may import under one: every routine then declines (`runUnknown`).
  var queue = @[startRaw]
  while queue.len > 0:
    let raw = anchored(queue.pop())
    let key = normalPath(raw)
    if key in runSeen or isOwnRuntime(key) or isOwnSource(key): continue
    runSeen.add key
    if key notin moduleScans: moduleScans[key] = scanModule(raw)
    let m = moduleScans[key]
    if m.unknown.len > 0:
      if runUnknown.len == 0:
        runUnknown = "`" & raw.extractFilename & "`, which the program imports: " & m.unknown
      continue
    for l in m.importLeak:
      runLeaks.add (root: key, name: l.name, opts: l.opts)
      for i in m.imports:
        if i.extractFilename.changeFileExt("") == l.name:
          runReach[key & "|" & l.name] = reachOf(i)
          break
    for i in m.imports: queue.add i

type RoutineChecks* = object
  checks*: set[CheckOption]
  assertsMaybeOff*: bool
    ## The routine's module may compile an `assert` out: at the routine's
    ## position, or anywhere else in it, where an iterator's instance it shares
    ## may have been compiled first (`mitems[T]` takes the options of its first
    ## instantiation). Read where the walker models a stdlib iterator's assert.
  why*: string                ## set where the position could not be read at all
  overflowModelled*: bool
    ## RFC-0016 K4c. A `stdlibAxis` row covers the routine's overflow delta:
    ## its body exercises `overflowChecks` and the push turns them off, and
    ## the walker models that (`asUnchecked`). Set by the parser, never here.
  overflowRow*: Admit[StdlibBody]
    ## RFC-0016 ADM-IR. The admitted row behind `overflowModelled`: the proof
    ## `mkArithBlock` takes for the `asUnchecked` stamp. Set with it.
  unadmitted*: string
    ## RFC-0016 K4c. The stdlib-body axis does not admit this routine's body
    ## (`admitStdlibBody`: no row, or a declined one), and the reason names the
    ## cell. Set by the parser, never here; the routine is walked behind a
    ## `unadmittedKind` marker.
  unadmittedKind*: SymexErrorKind
    ## The kind of that decline (`feUnadmitted` for an absent row).
  rangeOn*: bool
    ## RFC-0016 PRC-07. The routine's position was read and `rangeChecks` is
    ## on there on every reading: in a build whose own range checks are off, a
    ## `push rangeChecks: on`, which the walker does not model (it follows the
    ## build's bit). `checks` never carries `coRange` in such a build: the
    ## option being off is the build, not a deviation.
  boundOn*: bool
    ## RFC-0016 PRC-07. `rangeOn`'s twin for `boundChecks`: in a build whose
    ## own bound checks are off, the routine pushed them back on (not
    ## modelled: its `s[i]` raises `IndexDefect`, the walker follows the
    ## build). `checks` never carries `coBound` in such a build.
  objOn*: bool
    ## RFC-0016 PRC-07. `boundOn`'s twin for `objChecks`: in a build whose own
    ## object checks are off, the routine pushed them back on (not modelled:
    ## its down-conversion raises `ObjectConversionDefect`). `checks` never
    ## carries `coObj` in such a build.
  fieldOn*: bool
    ## RFC-0016 PRC-07. `boundOn`'s twin for `fieldChecks`: the routine pushed
    ## them back on in a build whose own field checks are off (not modelled:
    ## its variant access raises `FieldDefect`). `checks` never carries
    ## `coField` in such a build.
  nanOn*, infOn*: bool
    ## RFC-0016 PRC-07 (float half). The routine's position was read and
    ## `nanChecks` (`infChecks`) is on there on every reading, from the build
    ## or a push, with no importer's push reaching it: the walker models the
    ## check (a `FloatInvalidOpDefect` / `FloatOverflowDefect` fork after a
    ## float `+ - * /`), so `checks` no longer carries it. Where it may be on
    ## and may be off, `checks` keeps it and the routine declines.
  overflowOn*: bool
    ## RFC-0016 W1-d2c. The routine's position was read and `overflowChecks`
    ## is on there on every reading (no `coOverflow` deviation): in a build
    ## whose own checks are off, a `push overflowChecks: on`. False wherever
    ## the position was not read (own runtime, `why`) or may be off.

const fourChecks = {coRange, coBound, coField, coObj}

var bodyAsts {.compileTime.}: Table[string, NimNode]

proc routineNameOf(n: NimNode): string =
  var h = n
  while h.kind in {nnkPostfix, nnkPragmaExpr} and h.len > 0:
    h = h[if h.kind == nnkPostfix: 1 else: 0]
  nameOf(h)

proc findRoutineDef(n: NimNode; name: string; line: int): NimNode =
  ## The parsed definition of the routine `name` written at `line`, or nil.
  if n.kind in {nnkProcDef, nnkFuncDef, nnkMethodDef, nnkIteratorDef,
                nnkConverterDef} and n.len > 0 and
     (n.lineInfoObj.line == line or n[0].lineInfoObj.line == line):
    if routineNameOf(n[0]) == name: return n
  for c in n:
    let r = findRoutineDef(c, name, line)
    if r != nil: return r

proc inRoutineChecks(n: NimNode; off: set[CheckOption]): string =
  ## "" or the first check pragma under `n` that names a check of `off` with a
  ## value other than a literal `off`: `{.push rangeChecks: on.}` in a body, or
  ## the routine's own `{.rangeChecks: on.}`. Neither is seen by the scan of
  ## the module's statements, which does not enter a routine.
  if n.kind == nnkExprColonExpr and n.len == 2:
    let opts = checksNamed(nameOf(n[0])) * off
    if opts != {} and turnsOn(n[1]) != 0:
      return "`" & nameOf(n[0]) & ": " & n[1].repr & "` at line " &
             $n.lineInfoObj.line
  for c in n:
    let r = inRoutineChecks(c, off)
    if r.len > 0: return r

proc positionUnreadable(impl: NimNode; file: string; line: int;
                        st: CheckState): string =
  ## RFC-0016 PRC-07. Why the routine's check state at the options its build has
  ## off cannot be taken as one answer: "" when it can. The walker models a
  ## routine compiled with such an option off as unchecked (the build's bit) or
  ## walks it checked where it was pushed on; a routine that is checked at some
  ## positions only, or whose position is ambiguous, is neither, and is never
  ## assumed to be the build's setting.
  let off = fourChecks - buildSemantics.checks
  if off == {}: return
  let both = off * st.maybeOn * st.maybeOff
  if both != {}:
    return "its position is both pushed on and off for " & $both
  if not isStdlibFile(file):
    var ast: NimNode
    if file in bodyAsts: ast = bodyAsts[file]
    else:
      var text: string
      if readSource(file, text).len == 0:
        try: ast = parseStmt(text, file)
        except ValueError: discard
      bodyAsts[file] = ast
    if ast != nil:
      let def = findRoutineDef(ast, routineNameOf(impl[0]), line)
      if def != nil:
        let hit = inRoutineChecks(def, off)
        if hit.len > 0:
          return "it carries " & hit & " inside its own definition, so it is " &
                 "checked at some positions and not others"

proc routinePlace*(impl: NimNode): string =
  ## For a message: the routine, its file and line.
  let li = impl.lineInfoObj
  "`" & impl[0].repr & "` (" & li.filename.extractFilename & ":" & $li.line & ")"

proc stdlibRoutineKey*(impl: NimNode): string =
  ## RFC-0016 K4c. The `stdlibAxis` key of a typed routine definition,
  ## `<module>.<name>`, or "" for a routine outside the toolchain's `lib/`.
  ## The module is the one the routine belongs to (`system` for a routine of
  ## `system/arithmetics.nim`, which `system.nim` includes).
  ## RFC-0016 W3-z P3: an iterator is `<module>.<name>/iterator`, a key of its
  ## own, so a proc row never admits an iterator of the same name.
  if impl.kind notin {nnkProcDef, nnkFuncDef, nnkIteratorDef} or
     impl.len == 0: return
  let li = impl.lineInfoObj
  let rootAt = anchored(moduleFileOf(impl[0], li.filename))
  let root = normalPath(if rootAt.len > 0: rootAt
                        else: moduleFileOf(impl[0], li.filename))
  if not isStdlibFile(root): return
  result = root.extractFilename.changeFileExt("") & "." & impl[0].strVal
  if impl.kind == nnkIteratorDef: result.add "/iterator"

proc routineChecks*(impl: NimNode): RoutineChecks =
  ## How `impl` (a typed routine definition) differs from the model.
  let li = impl.lineInfoObj
  let fileRaw = anchored(li.filename)
  let file = normalPath(if fileRaw.len > 0: fileRaw else: li.filename)
  if isOwnRuntime(file): return
  let rootAt = anchored(moduleFileOf(impl[0], li.filename))
  let rootRaw = if rootAt.len > 0: rootAt else: moduleFileOf(impl[0], li.filename)
  let root = normalPath(rootRaw)
  if isOwnRuntime(root): return
  if root notin moduleScans: moduleScans[root] = scanModule(rootRaw)
  if moduleScans[root].unknown.len > 0:
    return RoutineChecks(checks: allChecks, assertsMaybeOff: true,
                         why: moduleScans[root].unknown)
  let st = stateAt(moduleScans[root], file, li.line, li.column)
  result.checks = deviation(st)
  result.assertsMaybeOff = coAssert in st.maybeOff or
    coAssert in moduleScans[root].everything.maybeOff
  # A user's importer hands on what it pushed to any module this walk reaches: the
  # chain from what it names is not read. `system.nim` and `math.nim` import under
  # their own pushes, so a stdlib importer hands it on to what it names alone.
  # Importers are found by the import graph from this module and the project file.
  for l in moduleScans[root].importLeak:
    runLeaks.add (root: root, name: l.name, opts: l.opts)
  if not isStdlibFile(root):
    enterGraph(rootRaw)
    enterGraph(querySetting(projectFull))
    if runUnknown.len > 0:
      return RoutineChecks(checks: allChecks, assertsMaybeOff: true, why: runUnknown)
  let moduleName = root.extractFilename.changeFileExt("")
  var leaked: set[CheckOption]
  for l in runLeaks:
    if l.root == root: continue
    let rk = l.root & "|" & l.name
    let reaches =
      if l.name == moduleName: true
      elif isStdlibFile(l.root) or isSystemFile(root): false
      elif rk in runReach: root in runReach[rk] or isStdlibFile(root)
      else: true          # the named module was not found: any may be under it
    if reaches:
      result.checks = result.checks + l.opts
      leaked = leaked + l.opts
  if result.checks * defaultOff != {} and not touchesFloat(impl[6]):
    result.checks = result.checks - defaultOff
  # RFC-0016 PRC-07 (float half): a float check on at every reading is walked.
  if coNan in result.checks and coNan notin st.maybeOff and coNan notin leaked:
    result.nanOn = true
    result.checks.excl coNan
  if coInf in result.checks and coInf notin st.maybeOff and coInf notin leaked:
    result.infOn = true
    result.checks.excl coInf
  result.overflowOn = coOverflow notin result.checks
  let unreadable = positionUnreadable(impl, file, li.line, st)
  if unreadable.len > 0:
    result.why = "the routine's range, bound, field or object checks differ " &
      "within it, not modelled as one setting: " & unreadable
  if coRange notin buildSemantics.checks:
    result.rangeOn = coRange notin result.checks
    result.checks = result.checks - {coRange}
  if coBound notin buildSemantics.checks:
    result.boundOn = coBound notin result.checks
    result.checks = result.checks - {coBound}
  if coField notin buildSemantics.checks:
    result.fieldOn = coField notin result.checks
    result.checks = result.checks - {coField}
  if coObj notin buildSemantics.checks:
    result.objOn = coObj notin result.checks
    result.checks = result.checks - {coObj}
