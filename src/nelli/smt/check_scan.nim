## RFC-0005 S8cu -- the pure half of the check-option scan: a module's text in,
## the state of the check pragmas at every position out.
##
## RFC-0016 0.10.0 review D5. Nothing here reaches the compiler or the disk: a
## file the scan has to open (an `include`d one, an importer to look for) is
## found and read through a `SourceEnv` the caller passes, so the scan runs on
## literal inputs. `check_options` is the adapter that supplies the compile-time
## one (the project path, the search paths, the compiler's file reader) and
## adds the routine-level reads that need a typed symbol. The census in
## `tests/tsymex_0016_d5_axisdeps.nim` keeps this module free of those calls.
import std/[macros, strutils, tables]
import ./buildprofile
export buildprofile.CheckOption   ## moved to buildprofile (RFC-0016 W1-c1a)

type
  SourceEnv* = object
    ## What the scan asks of the world, as plain procs (the compile-time VM has
    ## no closures to give). `anchor` places a path as the reader wants it ("" when
    ## it cannot be placed); `searchPaths` are the directories an import is
    ## looked for under after the importer's own.
    exists*: proc (path: string): bool {.nimcall.}
    read*: proc (path: string): string {.nimcall.}
    anchor*: proc (path: string): string {.nimcall.}
    searchPaths*: seq[string]
    libDir*: string
      ## RFC-0016 PRC-43. The compiler's `lib/` (`querySetting(libPath)`),
      ## which a `--lib:` override may put under any name; "" leaves only the
      ## spelled `/lib/...` patterns.
    defines*: Table[string, bool]
      ## RFC-0016 int6-a2. `defined(x)` as the compiler evaluated it at an
      ## entry macro's call site (`check_options.symexResolveDefine`), by the
      ## name as written. A name absent is undecided. A conditional symbol is
      ## the same at every site of one compile, so the value read there is
      ## the value the scanned module was compiled with.

# Path text, with no file system behind it. Both separators, as the compiler
# reports either on Windows.
func isSep(c: char): bool = c == '/' or c == '\\'

func parentOf*(p: string): string =
  ## The directory part, as `os.parentDir`: "" for a bare name.
  var e = p.len
  while e > 1 and isSep(p[e - 1]): dec e
  var i = e - 1
  while i >= 0 and not isSep(p[i]): dec i
  if i < 0: return ""
  while i > 0 and isSep(p[i - 1]): dec i
  if i == 0: (if e > 1: p[0 ..< 1] else: "")
  else: p[0 ..< i]

func joined*(dir, name: string): string =
  ## `dir / name`.
  if dir.len == 0: name
  elif isSep(dir[^1]): dir & name
  else: dir & "/" & name

func baseName*(p: string): string =
  var i = p.len - 1
  while i >= 0 and not isSep(p[i]): dec i
  p[i + 1 .. ^1]

func stemOf*(file: string): string =
  ## A file name without its extension.
  let dot = file.rfind('.')
  if dot > 0: file[0 ..< dot] else: file

type
  CheckState* = object
    ## Per option, whether it may be off and whether it may be on at a position.
    ## Both, where the scan cannot tell.
    maybeOff*, maybeOn*: set[CheckOption]

  ScanEvent = object
    line, col: int
    st: CheckState

  RoutineDefs = Table[string, seq[int]]
    ## RFC-0016 int6-w. Per routine name (`defKey`), the lines its definitions
    ## start on in one text, at any depth; `expandedAt` for one a template or
    ## macro body spells.

  ScanVisit = object
    ## One reading of one file. A file included twice has two.
    file: string              ## `normalPath`ed
    events: seq[ScanEvent]
    regions: seq[tuple[first, last: int]]   ## template and macro definitions
    parse: int                ## RFC-0016 int6-w: the text as parsed, an index
                              ## into `parsedAsts` (`scannedAst`) and
                              ## `parsedShapes` (`textDisagrees`); -1 for none

  ModuleScan* = object
    visits: seq[ScanVisit]
    unknown*: string          ## why a part of the module could not be read
    everything*: CheckState   ## the union over every position
    importLeak*: seq[tuple[name: string, opts: set[CheckOption]]]
      ## what an `import` under a push hands the module it names
    imports*: seq[string]     ## user modules it imports, as found on disk
    hiddenPops: seq[tuple[file: string, line: int]]
      ## a `{.pop.}` with no push the scan read: something unseen pushed
    undecidedDefines*: seq[string]
      ## RFC-0016 int6-a2. The names `x` of the `defined(x)` the scan could not
      ## decide (absent from `SourceEnv.defines`) in a `when` that moves the
      ## check state: deciding them may make a position exact.

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
    env: SourceEnv            ## where an included or imported file is found and read

const
  defaultOn* = {coField, coOverflow, coRange, coBound, coObj}
  defaultOff* = {coNan, coInf}
  allChecks* = defaultOn + defaultOff
  everyOption* = allChecks + {coAssert}

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

proc libRelPath*(path, libDir: string): string =
  ## RFC-0016 PRC-43. `path` relative to the stdlib directory `libDir`, with
  ## `/` separators, or "" when it is not under it. Compared without case and
  ## across both separators, as `dsl_typebridge.isStdlibDecl` compares: a
  ## `--lib:` override names the directory anything, so stdlib identity is
  ## the configured path and not the spelling `/lib/`.
  if libDir.len == 0: return ""
  var d = normalPath(libDir)
  if not d.endsWith("/"): d.add '/'
  if path.len <= d.len: return ""
  for i in 0 ..< d.len:
    let c = if path[i] == '\\': '/' else: path[i]
    if c.toLowerAscii != d[i].toLowerAscii: return ""
  normalPath(path[d.len .. ^1])

proc merge(a, b: CheckState): CheckState =
  CheckState(maybeOff: a.maybeOff + b.maybeOff, maybeOn: a.maybeOn + b.maybeOn)

proc checksNamed*(name: string): set[CheckOption] =
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

proc nameOf*(n: NimNode): string =
  if n.kind in {nnkIdent, nnkSym}: n.strVal
  elif n.kind == nnkAccQuoted and n.len == 1: nameOf(n[0])
  else: ""

proc turnsOn*(v: NimNode): int =
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
            sc.res.unknown = "a `{.pop.}` at " & here.file.baseName & ":" &
              $here.line & " pops a push the scan cannot see"
        elif sc.stack.len > 0:
          let wasAmbiguous = sc.stack.len <= sc.ambiguous
          let top = sc.stack.pop()
          sc.cur = if wasAmbiguous: merge(sc.cur, top) else: top
          sc.ambiguous = min(sc.ambiguous, sc.stack.len)
      elif name in sc.users and depth < 16:
        applyPragma(sc, newTree(nnkPragma, sc.users[name]), depth + 1)

proc decide(c: NimNode; defines: Table[string, bool];
            atoms: var seq[string]): int =
  ## 1 true, 0 false, -1 undecided. A macro cannot evaluate `defined(x)` for a
  ## name it only holds as text: it is decided where the call site evaluated
  ## it (`defines`, RFC-0016 int6-a2), and otherwise undecided, its name added
  ## to `atoms`. Only `defined` of a bare name, `not`, `and`, `or`, `true`,
  ## `false` and the host comparisons below are decided: any other name (a
  ## `const`, `declared(...)`) may resolve differently at another site.
  case c.kind
  of nnkCall, nnkCommand:
    if c.len == 2 and nameOf(c[0]) == "defined" and c[1].kind == nnkIdent:
      let name = c[1].strVal
      if name in defines: return (if defines[name]: 1 else: 0)
      if name notin atoms: atoms.add name
    -1
  of nnkIdent, nnkSym:
    case nameOf(c).toLowerAscii
    of "true": 1
    of "false": 0
    else: -1
  of nnkPar:
    if c.len == 1: decide(c[0], defines, atoms) else: -1
  of nnkPrefix:
    if c.len == 2 and nameOf(c[0]) == "not":
      let d = decide(c[1], defines, atoms)
      if d < 0: -1 else: 1 - d
    else: -1
  of nnkInfix:
    if c.len != 3: return -1
    let a = decide(c[1], defines, atoms)
    let b = decide(c[2], defines, atoms)
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

var parsedFiles {.compileTime.}:
  Table[string, tuple[text: string, ast: NimNode, parse: int]]
var parsedAsts {.compileTime.}: seq[NimNode]
  ## RFC-0016 int6-w. Every text a scan parsed, in parse order: a `ScanVisit`
  ## names its own by index, so a later read of the same file under another
  ## text does not replace the one it was scanned from. An index and not the
  ## node, so a `ModuleScan` stays a value a `const` can hold.
var parsedShapes {.compileTime.}:
  seq[tuple[text: string, done: bool, lines: int, defs: RoutineDefs]]
  ## RFC-0016 int6-s. Per entry of `parsedAsts`, its text, and once
  ## `textDisagrees` first asks of it, the text's line count and the routines
  ## it defines. Read lazily: only a user module a routine is placed in is
  ## asked, and a count over every visit of every included stdlib file, in
  ## every world `scanModuleText` reads, spent the VM's iteration budget on
  ## the `system.nim` scan alone (`tests/tsymex_0016_int6s_scancost.nim`).

func defKey*(name: string): string =
  ## RFC-0016 int6-w. A routine name as Nim compares identifiers: the first
  ## character as written, the rest without case or underscores.
  nimIdentNormalize(name)

proc defName(n: NimNode): string =
  ## The name a routine definition's first child spells: `p`, `p*`, `` `+` ``.
  case n.kind
  of nnkIdent, nnkSym: n.strVal
  of nnkPostfix: (if n.len == 2: defName(n[1]) else: "")
  of nnkAccQuoted:
    var s = ""
    for c in n: s.add defName(c)
    s
  of nnkPragmaExpr: (if n.len > 0: defName(n[0]) else: "")
  else: ""  # k2: n/a: a name this cannot spell records no definition; textDisagrees says nothing of it and the position is read as before

const expandedAt = 0
  ## RFC-0016 int6 l1. The line `collectDefs` records for a routine a template
  ## or macro body spells: the compiler places such a routine where the body
  ## is expanded (its call site, `{.dirty.}` or not: a template's routines are
  ## injected), not on the line its name is written, so no line of the text
  ## tells it apart. Not a line any routine starts on (lines count from 1).

proc collectDefs(n: NimNode; acc: var RoutineDefs; inBody = false) =
  ## RFC-0016 int6-w. Every routine definition in a parsed text, nested ones
  ## and those inside templates included, by name and starting line; one
  ## inside a template or macro body (`inBody`) at `expandedAt`.
  if n.kind in RoutineNodes and n.kind != nnkLambda and n.len > 0:
    let nm = defName(n[0])
    if nm.len > 0:
      # The definition's line and its name's: a position is either.
      let k = defKey(nm)
      var lines = acc.getOrDefault(k)
      if inBody:
        if expandedAt notin lines: lines.add expandedAt
      else:
        lines.add n.lineInfoObj.line
        if n[0].lineInfoObj.line != n.lineInfoObj.line:
          lines.add n[0].lineInfoObj.line
      acc[k] = lines
  let body = inBody or n.kind in {nnkTemplateDef, nnkMacroDef}
  for c in n: collectDefs(c, acc, body)

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

proc readSource*(env: SourceEnv; path: string; text: var string): string =
  ## "" and `text`, or why not. A missing file is reported, not read, and a
  ## file with a source filter is not the text the compiler parsed.
  let at = env.anchor(path)
  if at.len == 0 or not env.exists(at): return "cannot read `" & path & "`"
  text = env.read(at)
  if text.startsWith("#?"): return "`" & path & "` has a source filter"
  ""

proc scanFile(sc: var Scanner; path, text: string) =
  sc.res.visits.add ScanVisit(file: normalPath(path), parse: -1)
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
      let ast = parseStmt(text, path)
      parsedAsts.add ast
      parsedShapes.add (text: text, done: false, lines: 0,
                        defs: initTable[string, seq[int]]())
      parsedFiles[path] = (text: text, ast: ast, parse: parsedAsts.high)
    sc.res.visits[sc.visit].parse = parsedFiles[path].parse
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

proc resolveInclude(env: SourceEnv; fromFile, rel: string): string =
  ## Beside the including file, then under each directory above it (`include
  ## system/x` from `lib/system.nim`, `std/private/x` from anywhere under `lib`).
  let name = if rel.endsWith(".nim"): rel else: rel & ".nim"
  var dir = fromFile.parentOf
  while dir.len > 0:
    let cand = dir.joined(name)
    if env.exists(cand): return cand
    let up = dir.parentOf
    if up == dir: break
    dir = up
  ""

proc scanInclude(sc: var Scanner; n: NimNode) =
  let fromFile = sc.including[^1]
  let rel = includePathOf(n)
  let path = if rel.len > 0: resolveInclude(sc.env, fromFile, rel) else: ""
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
  let why = readSource(sc.env, path, text)
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
    into.add n.strVal.baseName.stemOf
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

proc isOwnSource*(path: string): bool =
  ## Nelli itself: `src/nelli.nim` and everything under `src/nelli/`.
  const src = normalPath(currentSourcePath().parentOf.parentOf.parentOf)
  let p = normalPath(path)
  p == src & "/nelli.nim" or p.startsWith(src & "/nelli/")

proc isLibraryFile*(path: string; libDir = ""): bool =
  ## The stdlib and installed packages: not the program's own modules.
  ## RFC-0016 PRC-43: the stdlib is also whatever is under `libDir`.
  if libRelPath(path, libDir).len > 0: return true
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
  let dir = sc.including[^1].parentOf
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
    if sc.env.exists(dir.joined(name)): found = dir.joined(name)
    else:
      for sp in sc.env.searchPaths:
        if sc.env.exists(sp.joined(name)):
          found = sp.joined(name)
          break
    # Kept as found if it cannot be anchored: reading it then fails closed.
    if found.len > 0 and sc.env.anchor(found).len > 0:
      found = sc.env.anchor(found)
    if found.len > 0 and not isLibraryFile(found, sc.env.libDir) and found notin sc.res.imports:
      sc.res.imports.add found

proc walkWhen(sc: var Scanner; n: NimNode) =
  var alts: seq[NimNode]
  var exhaustive = false
  var atoms: seq[string]
  for br in n:
    if br.kind in {nnkElifBranch, nnkElifExpr}:
      let text = br[0].repr
      var d = decide(br[0], sc.env.defines, atoms)
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
  # RFC-0016 int6-a2: a name undecided where the `when` moves the check
  # state, for the call site to decide (`undecidedDefines`).
  if atoms.len > 0 and movesState(n):
    for a in atoms:
      if a notin sc.res.undecidedDefines: sc.res.undecidedDefines.add a
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

proc scanWorld(env: SourceEnv; path, text: string;
               assume: Table[string, bool]): Scanner =
  ## Read twice where a pop matched no push: the second reading knows where.
  result = Scanner(cur: commandLineChecks, assume: assume, env: env)
  result.res.everything = commandLineChecks
  scanFile(result, path, text)
  if result.res.hiddenPops.len > 0:
    let pops = result.res.hiddenPops
    result = Scanner(cur: commandLineChecks, assume: assume, knownPops: pops,
                     env: env)
    result.res.everything = commandLineChecks
    scanFile(result, path, text)

proc scanModuleText*(path, text: string; env: SourceEnv): ModuleScan =
  ## The scan of a module whose text is at hand. An `include` is read through
  ## `env`.
  let first = scanWorld(env, path, text, initTable[string, bool]())
  if first.forkConds.len == 0: return first.res
  let k = min(first.forkConds.len, maxForkConds)
  result.everything = commandLineChecks
  for mask in 0 ..< (1 shl k):
    var assume = initTable[string, bool]()
    for i in 0 ..< k: assume[first.forkConds[i]] = (mask and (1 shl i)) != 0
    let w = scanWorld(env, path, text, assume)
    result.visits.add w.res.visits
    result.everything = merge(result.everything, w.res.everything)
    result.importLeak.add w.res.importLeak
    for a in w.res.undecidedDefines:
      if a notin result.undecidedDefines: result.undecidedDefines.add a
    for i in w.res.imports:
      if i notin result.imports: result.imports.add i
    if result.unknown.len == 0: result.unknown = w.res.unknown

proc scanModule*(path: string; env: SourceEnv): ModuleScan =
  var text: string
  let why = readSource(env, path, text)
  if why.len > 0:
    result.unknown = why
    return
  scanModuleText(path, text, env)

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

proc scannedAst*(m: ModuleScan; file: string): NimNode =
  ## RFC-0016 int6-w. The text of `file` the scan read, parsed; nil where the
  ## scan did not read it. A second read of the file from disk is another
  ## snapshot, which an edit during the compile can make disagree with this.
  let file = normalPath(file)
  for v in m.visits:
    if v.file == file and v.parse in 0 .. parsedAsts.high:
      return parsedAsts[v.parse]
  nil

proc shapeOf(i: int) =
  ## RFC-0016 int6-s. Fills `parsedShapes[i]`, once per parsed text: linear in
  ## the text and its tree.
  if parsedShapes[i].done: return
  let text = parsedShapes[i].text
  var defs: RoutineDefs
  collectDefs(parsedAsts[i], defs)
  parsedShapes[i].lines = text.count('\n') +
    (if text.len > 0 and text[^1] != '\n': 1 else: 0)
  parsedShapes[i].defs = defs
  parsedShapes[i].done = true

proc textDisagrees*(m: ModuleScan; file, name: string; line: int): string =
  ## RFC-0016 int6-w. "" when the text the scan read can be the text the
  ## compiler parsed at a routine `name` it places at `line` of `file`, else
  ## why not. The scan reads the module from disk when a macro first asks,
  ## which may be after the compiler parsed it: a file edited during the
  ## compile is read as the new text and its positions as the old, so a push
  ## two lines above a routine read two lines late is not over it (a pushed-
  ## off routine read checked, a trusted `OverflowDefect` its binary never
  ## raises). The text disagrees when it ends before `line`, or defines a
  ## routine `name` but not starting there. A routine a macro made, with a
  ## position its name is not written at, defines no `name` and is not told
  ## apart; nor is one a template or macro body spells (`expandedAt`), placed
  ## where the body is expanded. A file the scan did not read says nothing.
  let file = normalPath(file)
  let key = defKey(name)
  for v in m.visits:
    if v.file != file: continue
    if v.parse notin 0 .. parsedAsts.high:
      # Not parsed: a text of no lines and no routines.
      if line > 0:
        return "`" & baseName(file) & "` on disk has 0 lines, and the " &
          "compiler placed `" & name & "` at line " & $line
      continue
    shapeOf(v.parse)
    let lines = parsedShapes[v.parse].lines
    if line > lines:
      return "`" & baseName(file) & "` on disk has " & $lines &
        " lines, and the compiler placed `" & name & "` at line " & $line
    if key in parsedShapes[v.parse].defs and
       expandedAt notin parsedShapes[v.parse].defs[key] and
       line notin parsedShapes[v.parse].defs[key]:
      return "`" & baseName(file) & "` on disk defines `" & name &
        "` at line " & parsedShapes[v.parse].defs[key].join(", ") &
        ", not at line " & $line & ", where the compiler placed it"
  ""

proc unknownReason*(m: ModuleScan): string = m.unknown
proc importLeak*(m: ModuleScan): set[CheckOption] =
  for l in m.importLeak: result = result + l.opts
