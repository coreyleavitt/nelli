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
## - RFC-0016 int6-a6. Nim compiles `system` first, then the import graph
##   depth first: each module at the first import that reaches it, under the
##   options open at that import, and the importer's options come back after
##   it. A later import of a compiled module changes nothing; a module's own
##   trailing `{.rangeChecks: off.}` does not reach its importer
##   (`tests/tsymex_0016_int6a_leak.nim`). `replayCompileOrder` replays that
##   order over the user modules, so a leak is a position state.
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
import ./check_scan    ## RFC-0016 D5: the pure scan; this module is its adapter
import ./magic_rows    ## RFC-0016 int6-u: `magicIs`, for `loopIncRegion`
export check_scan, buildprofile.CheckOption

{.warning[Deprecated]: off.}   # `NimNode.owner`: no replacement in 2.2.10

# ---- the compile-time I/O the pure scan is given -----------------------------

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

proc diskExists(p: string): bool = fileExists(p)

proc diskRead(p: string): string = staticRead(p)

const configuredLibDir* = querySetting(libPath)
  ## RFC-0016 PRC-43. The compiler's `lib/`, under whatever name `--lib:` gave it.

var resolvedDefines {.compileTime.}: Table[string, bool]
  ## RFC-0016 int6-a2. `defined(x)` by name, as an entry macro's call site
  ## evaluated it (`symexResolveDefine`): the scan's `SourceEnv.defines`.
var askedDefines {.compileTime.}: seq[string]
  ## Names a position the walk read was undecided on (`noteUndecided`), for
  ## the entry macro to have its call site decide (`undecidedDefines`).
var emittedDefines {.compileTime.}: seq[string]
  ## Names an entry macro has already asked its call site for: never twice, so
  ## a name the re-expansion did not resolve cannot re-enter forever.

proc compileTimeEnv(): SourceEnv =
  ## The compiler's own view: the project's directories and search paths, and
  ## the compiler's file reader.
  SourceEnv(exists: diskExists, read: diskRead, anchor: anchored,
            searchPaths: querySettingSeq(searchPaths),
            libDir: configuredLibDir, defines: resolvedDefines)

macro symexResolveDefine*(name: static string; value: static bool): untyped =
  ## RFC-0016 int6-a2. Records `defined(name)` as the call site evaluated it
  ## (`value`), before an entry macro expands again (`entry_parse`). The
  ## scan reads a `when defined(name)` around a check pragma by it.
  resolvedDefines[name] = value
  newEmptyNode()

proc undecidedDefines*(): seq[string] =
  ## RFC-0016 int6-a2. The names an entry macro asks its call site to decide
  ## before it expands again: undecided at a position the walk read, and not
  ## asked before. Each is marked asked.
  for a in askedDefines:
    if a notin resolvedDefines and a notin emittedDefines:
      result.add a
      emittedDefines.add a

proc noteUndecided(m: ModuleScan) =
  for a in m.undecidedDefines:
    if a notin resolvedDefines and a notin askedDefines: askedDefines.add a

proc stale(m: ModuleScan): bool =
  ## A scan read before a name it was undecided on was resolved.
  for a in m.undecidedDefines:
    if a in resolvedDefines: return true

proc scanModuleText*(path, text: string): ModuleScan =
  ## The scan of a module whose text is at hand; an `include` is read from disk.
  scanModuleText(path, text, compileTimeEnv())

proc scanModule*(path: string; start = commandLineChecks): ModuleScan =
  ## The scan of a module on disk, compiled from `start` (RFC-0016 int6-a6).
  scanModule(path, compileTimeEnv(), start)

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
  let rel = libRelPath(path, configuredLibDir)
  rel == "system.nim" or rel.startsWith("system/") or
    path.endsWith("/lib/system.nim") or "/lib/system/" in path

proc isStdlibFile(path: string): bool =
  let rel = libRelPath(path, configuredLibDir)
  isSystemFile(path) or "/lib/pure/" in path or "/lib/std/" in path or
    "/lib/core/" in path or "/lib/impure/" in path or
    rel.startsWith("pure/") or rel.startsWith("std/") or
    rel.startsWith("core/") or rel.startsWith("impure/")

proc typeHasFloat(t: NimNode; generic: bool; depth = 0): bool =
  ## `generic`: an uninstantiated `T` may be a float. A callee's own `T` says nothing
  ## of this routine's arithmetic.
  if t.typeKind in {ntyFloat, ntyFloat32, ntyFloat64, ntyFloat128}: return true
  if generic and t.typeKind == ntyGenericParam: return true
  if depth < 4 and t.kind == nnkBracketExpr:
    for c in t:
      if typeHasFloat(c, generic, depth + 1): return true

proc touchesFloat(n: NimNode; seen: var seq[string]): bool =
  ## The float checks guard float arithmetic alone. An inline iterator a loop
  ## runs is compiled into the loop with the options of the routine holding it
  ## (read from the generated C: an iterator defined outside a `push nanChecks`
  ## still raises under one), so its body counts as the routine's own,
  ## transitively. Typed bodies already carry expanded templates.
  case n.kind
  of nnkFloatLit .. nnkFloat64Lit: true
  of nnkSym:
    case n.symKind
    of nskVar, nskLet, nskParam, nskConst, nskResult, nskForVar, nskField:
      typeHasFloat(n.getType, true)
    of nskProc, nskFunc, nskConverter, nskMethod:
      typeHasFloat(n.getType, false)
    of nskIterator:
      # Inline and closure alike: a closure iterator's body is a separate
      # routine, but a body that cannot be told apart is read as touching.
      # RFC-0016 W3-z P11: the key is the iterator's own, not its signature's:
      # two iterators of one signature (`fouter` over `fdiv`, both
      # `(int): bool`) were one, and the inner one's body was never read.
      let body = n.getImpl
      let key = n.signatureHash & "@" & n.strVal &
                (if body.kind != nnkEmpty: body.lineInfo else: "")
      if key in seen: false
      else:
        seen.add key
        if typeHasFloat(n.getType, false): true
        else:
          body.kind != nnkEmpty and body.len > 6 and touchesFloat(body[6], seen)
    else: false
  of mayScanLeafKinds - {nnkFloatLit .. nnkFloat64Lit}:
    false
  of mayScanNoCodeKinds + mayScanStructuralKinds + RoutineNodes:
    for c in n:
      if touchesFloat(c, seen): return true
    false
  else:  # k2: fail-closed: true: read as touching floats, so the routine keeps its float checks
    # RFC-0016 K2F-3 (RFC section 8.1): a kind not listed may compute with
    # floats (`asm` included), so the float checks may matter to it.
    true

proc touchesFloat(n: NimNode): bool =
  var seen: seq[string]
  touchesFloat(n, seen)

var moduleScans {.compileTime.}: Table[string, ModuleScan]

proc scanOf(key, raw: string; start = commandLineChecks): ModuleScan =
  ## The scan of the module at `key`, read once, and again once a `defined`
  ## it was undecided on is resolved (RFC-0016 int6-a2). RFC-0016 int6-a6:
  ## per state it is compiled from; the command line's is keyed by the path
  ## alone.
  let k = if start == commandLineChecks: key
          else: key & "|" & $start.maybeOff & "|" & $start.maybeOn
  if k notin moduleScans or stale(moduleScans[k]):
    moduleScans[k] = scanModule(raw, start)
  moduleScans[k]
var runLeaks {.compileTime.}: seq[tuple[root, name: string; opts: set[CheckOption]]]
var runReach {.compileTime.}: Table[string, seq[string]]
  ## Per user importer and name: the modules the named one reaches by import,
  ## itself included. Absent where it was not found on disk.
var runSeen {.compileTime.}: seq[string]
var runUnknown {.compileTime.}: string

type CompileReplay = object
  ## RFC-0016 int6-a6. Nim's compile order replayed over the user modules
  ## (`replayCompileOrder`).
  done, exact: bool
  why: string                       ## why not `exact`: the coarse reading stands
  entry: Table[string, CheckState]  ## per user module, the state it is first compiled from
  compiled: seq[string]             ## user keys and `lib:` targets, in compile order
  libTaint: set[CheckOption]
    ## what an import under a push may hand a library module it first
    ## compiles: every library routine but `system`'s reads as under it
  callAt: string                    ## the first module-level call, in compile order

var runReplay {.compileTime.}: CompileReplay

proc beginCheckOptionRun*() =
  ## Each entry macro's parse: what one program's importers leak is its own.
  runLeaks.setLen 0
  runSeen.setLen 0
  runUnknown = ""
  runReach.clear()
  runReplay = CompileReplay()

proc reachOf(start: string): seq[string] =
  ## `start` and the user modules its imports reach.
  var queue = @[start]
  while queue.len > 0:
    let raw = anchored(queue.pop())
    let key = normalPath(raw)
    if key in result: continue
    result.add key
    for i in scanOf(key, raw).imports: queue.add i

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
    let m = scanOf(key, raw)
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

proc namesImportSwitch*(text: string): bool =
  ## RFC-0016 int6-a6. Does a configuration text (a `nim.cfg`, a `.nims`, the
  ## command line) set `import` or `include`: `--import:x`, `import = x`,
  ## `switch("import", x)`? Comments after `#` are skipped; `cincludes:`,
  ## `importc:` and a NimScript `import`/`include` statement are not it.
  for raw in text.splitLines:
    var line = raw
    let h = line.find('#')
    if h >= 0: line = line[0 ..< h]
    let l = line.toLowerAscii
    for word in ["import", "include"]:
      var i = l.find(word)
      while i >= 0:
        let before = if i == 0: ' ' else: l[i - 1]
        var j = i + word.len
        while j < l.len and l[j] in {' ', '\t'}: inc j
        let after = if j < l.len: l[j] else: ' '
        if before notin {'a' .. 'z', '0' .. '9', '_'} and
           (after in {':', '='} or (before == '"' and after == '"')):
          return true
        i = l.find(word, i + 1)

var configImportRead {.compileTime.}: bool
var configImportWhy {.compileTime.}: string

proc configuredImport(): string =
  ## RFC-0016 int6-a6. "" or where `--import:`/`--include:` is set: the command
  ## line, or a configuration file the compiler reads (its own `config/`, the
  ## user's, every directory from the project's up, `<project>.nim.cfg` and
  ## `<project>.nims`). A module so imported is compiled ahead of the
  ## program's own imports, and the scan does not read it. Read once.
  if configImportRead: return configImportWhy
  configImportRead = true
  if namesImportSwitch(querySetting(commandLine)):
    configImportWhy = "the command line sets `--import` or `--include`"
    return configImportWhy
  var files: seq[string]
  let globalDir = configuredLibDir.parentDir / "config"
  files.add globalDir / "nim.cfg"
  files.add globalDir / "config.nims"
  for v in ["XDG_CONFIG_HOME", "APPDATA"]:
    if getEnv(v).len > 0: files.add getEnv(v) / "nim" / "nim.cfg"
  if getEnv("HOME").len > 0:
    files.add getEnv("HOME") / ".config" / "nim" / "nim.cfg"
    files.add getEnv("HOME") / ".config" / "nim" / "config.nims"
  let proj = querySetting(projectPath)
  let name = querySetting(projectName)
  files.add proj / name & ".nim.cfg"
  files.add proj / name & ".nims"
  var dir = proj
  while dir.len > 0:
    files.add dir / "nim.cfg"
    files.add dir / "config.nims"
    let up = dir.parentDir
    if up == dir: break
    dir = up
  for f in files:
    if fileExists(f) and namesImportSwitch(staticRead(f)):
      configImportWhy = "`" & f & "` sets `--import` or `--include`"
      return configImportWhy
  ""

proc replayFail(why: string) =
  if runReplay.exact:
    runReplay.exact = false
    runReplay.why = why

proc isUserTarget(t: string): bool =
  not t.startsWith("lib:") and not t.startsWith("lib?:") and
    not t.startsWith("?")

var moduleDefsCache {.compileTime.}: Table[string, ModuleDefs]

proc defsOf(path: string): ModuleDefs =
  ## RFC-0016 int6-m6. `moduleDefs` of `path`, read once per compile.
  let k = normalPath(path)
  if k notin moduleDefsCache:
    moduleDefsCache[k] = moduleDefs(compileTimeEnv(), path)
  moduleDefsCache[k]

proc callImportsNothing(m: ModuleScan; at: int; raw: string): string =
  ## RFC-0016 int6-m6. "" where the module-level call `m.events[at]` imports
  ## nothing: its callee name is defined, in every module visible at the
  ## call, only by `proc`/`func`/`method`/`converter`/`iterator`
  ## definitions, which compile no module. Visible: the calling module's own
  ## text, `system`, every module its imports before the call name (under an
  ## undecided `when` too), and what each of those re-exports, read as
  ## definition text alone (`moduleDefs`). Otherwise why not: a callee that
  ## is no name, is a template or macro anywhere so visible (an overload set
  ## mixing the two), is defined nowhere so read, or may come from a module
  ## the scan cannot place or read.
  let ev = m.events[at]
  if ev.callee.len == 0: return "its callee is not a name the scan reads"
  var queue = @[raw, configuredLibDir / "system.nim"]
  for j in 0 ..< at:
    if not m.events[j].call: queue.add m.events[j].targets
  var seen: seq[string]
  var kinds: set[DefKind]
  while queue.len > 0:
    let t = queue.pop()
    if t.startsWith("?") or t.startsWith("lib?:"):
      return "an import before it names a module the scan cannot place (`" &
             t & "`)"
    let path = if t.startsWith("lib:"): t[4 .. ^1] else: t
    let key = normalPath(path)
    if key in seen: continue
    seen.add key
    let d = defsOf(path)
    if d.unknown.len > 0:
      return "`" & path.extractFilename & "` is not read whole: " & d.unknown
    if ev.callee in d.exportedNames:
      return "`" & path.extractFilename & "` re-exports `" & ev.callee &
             "` from a module the scan does not place"
    kinds = kinds + d.defs.getOrDefault(ev.callee)
    queue.add d.reexports
  if dkExpands in kinds:
    return "`" & ev.callee & "` names a template or macro"
  if kinds == {}:
    return "`" & ev.callee & "` is defined in no module the scan reads"
  ""

proc replayModule(raw: string; start: CheckState) =
  ## Compiles the user module `raw` from `start`, as the first import that
  ## reaches it does, and in turn each module its statements first compile.
  let key = normalPath(raw)
  runReplay.compiled.add key
  runReplay.entry[key] = start
  let m = scanOf(key, raw, start)
  if m.unknown.len > 0:
    replayFail("`" & raw.extractFilename & "`: " & m.unknown)
    return
  for ei, ev0 in m.events:
    if not runReplay.exact: return
    # Nelli's own modules are library ones, as `enterGraph` reads them,
    # however the search path spelled them.
    var ev = ev0
    for t in ev.targets.mitems:
      if isUserTarget(t):
        let r = anchored(t)
        let k = normalPath(if r.len > 0: r else: t)
        if isOwnRuntime(k) or isOwnSource(k): t = "lib:" & k
    let dev = deviation(ev.st) - deviation(commandLineChecks)
    let at = "`" & ev.file.extractFilename & ":" & $ev.line & "`"
    if ev.call:
      # RFC-0016 int6-m6: a call of routines alone imports nothing.
      let why = callImportsNothing(m, ei, raw)
      if why.len == 0: continue
      if dev != {}:
        replayFail("a module-level call at " & at & " runs with " & $dev &
                   " pushed and may be a macro or template that imports (" &
                   why & ")")
        return
      if runReplay.callAt.len == 0:
        runReplay.callAt = at & " (" & why & ")"
      continue
    if ev.uncertain:
      if dev != {}:
        replayFail("the import at " & at & " under a push is under a `when` " &
                   "the scan does not decide")
        return
      for t in ev.targets:
        if isUserTarget(t):
          replayFail("the import at " & at & " of a user module is under a " &
                     "`when` the scan does not decide")
          return
      continue      # a library module so imported is not proven compiled
    if dev != {} and runReplay.callAt.len > 0:
      replayFail("the module-level call at " & runReplay.callAt & " comes " &
                 "before the import at " & at & " under a push, and may be a " &
                 "macro or template that imports")
      return
    for t in ev.targets:
      if t.startsWith("?"):
        if dev != {}:
          replayFail("the import at " & at & " under a push names a module " &
                     "the scan cannot find")
          return
      elif not isUserTarget(t):
        if t in runReplay.compiled or
           (t.startsWith("lib:") and isSystemFile(t[4 .. ^1])):
          continue
        # A library module's own imports are not read: under a push, any
        # library module may be first compiled here.
        if dev != {}: runReplay.libTaint = runReplay.libTaint + dev
        if t.startsWith("lib:"): runReplay.compiled.add t
      else:
        let raw2 = anchored(t)
        let k2 = normalPath(if raw2.len > 0: raw2 else: t)
        if k2 notin runReplay.compiled:
          replayModule(if raw2.len > 0: raw2 else: t, ev.st)

proc replayCompileOrder() =
  ## RFC-0016 int6-a6. Nim's compile order over the program, once per run:
  ## `system` first, then from the project file depth first, each user module
  ## scanned from the state at the import that first compiles it, which a
  ## push open there reaches. Not exact (`why`), and the coarse reading
  ## stands, where an import under a push is under an undecided `when`, a
  ## module-level call (a possible importing macro) comes before an import
  ## under a push or runs under one, or `--import:` is configured. A library
  ## module is never scanned: one an import under a push names, and no
  ## earlier import compiled, taints every library routine (`libTaint`).
  ## Cost: each user module is scanned once from the state it is first
  ## compiled from, beside its command-line scan (`scanOf` keys by state).
  if runReplay.done: return
  runReplay = CompileReplay(done: true, exact: true)
  let cfg = configuredImport()
  if cfg.len > 0:
    replayFail(cfg)
    return
  let proj = querySetting(projectFull)
  let raw = anchored(proj)
  replayModule(if raw.len > 0: raw else: proj, commandLineChecks)

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
    ## `push rangeChecks: on`. RFC-0016 int6: modelled, the routine's body is
    ## scoped checked (`checkedIn` in the parser), so its conversions raise
    ## `RangeDefect`. `checks` never carries `coRange` in such a build: the
    ## option being off is the build, not a deviation.
  boundOn*: bool
    ## RFC-0016 PRC-07. `rangeOn`'s twin for `boundChecks`: in a build whose
    ## own bound checks are off, the routine pushed them back on, and its
    ## `s[i]` raises `IndexDefect` (modelled, int6). `checks` never carries
    ## `coBound` in such a build.
  objOn*: bool
    ## RFC-0016 PRC-07. `boundOn`'s twin for `objChecks`: the routine pushed
    ## them back on in a build whose own object checks are off, and its
    ## down-conversion raises `ObjectConversionDefect` (modelled, int6).
    ## `checks` never carries `coObj` in such a build.
  fieldOn*: bool
    ## RFC-0016 PRC-07. `boundOn`'s twin for `fieldChecks`: the routine pushed
    ## them back on in a build whose own field checks are off, and its variant
    ## access raises `FieldDefect` (modelled, int6). `checks` never carries
    ## `coField` in such a build.
  offModelled*: set[CheckOption]
    ## RFC-0016 int6. Of the four checks (range, bound, field, object) and,
    ## int6-o, `overflowChecks`, those
    ## on in the build and off at the routine's position on every reading, in
    ## a user module, with no importer's push reaching it (RFC-0016 int6-a6:
    ## where the compile order is replayed, a push the import that first
    ## compiled the module was under is its position's state): the routine is
    ## walked with them off (its body's check scope leaves them out; for
    ## `coOverflow` its body is stamped `asPushedOff`), as the
    ## build route walks a build that has them off. They are not in `checks`.
    ## A position that may be either way keeps the option in `checks` and
    ## declines. RFC-0016 int6-a: a stdlib module's push of the four checks
    ## is modelled the same way (its body is walked under its own scope, as a
    ## user routine's is), where its definition holds no check pragma of its
    ## own; its `overflowChecks` stay the K4c delta's until
    ## `applyStdlibDelta` finds no row models them (`overflowOffExact`).
  overflowOffExact*: bool
    ## RFC-0016 int6-a. A stdlib routine whose position turns the build's
    ## `overflowChecks` off on every reading, with no importer's push reaching
    ## it and no check pragma inside its definition. `coOverflow` stays in
    ## `checks` here: the parser moves it to `offModelled` (`asPushedOff`)
    ## only where no stdlib row models it (`overflowModelled`, `asUnchecked`).
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
  bodyRegions*: bool
    ## RFC-0016 int6-a5. The routine is a user module's: a `{.push ...}` /
    ## `{.pop.}` pair of check options among its body's statements is walked
    ## as a region of its own (the parser's `nnkPragma` arm, grouped by
    ## `withCheckDeclines`). A stdlib or own-runtime routine's in-body push
    ## stays the unsupported statement it was.

const fourChecks = {coRange, coBound, coField, coObj}
const scopedChecks = fourChecks + {coOverflow}
  ## RFC-0016 int6-o. The checks a routine's position is read for as one
  ## setting (`positionUnreadable`) and modelled off at (`offModelled`).

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

proc inRoutineChecks(n: NimNode; off, on: set[CheckOption]): string =
  ## "" or the first check pragma under `n` that names a check of `off` with a
  ## value other than a literal `off`, or a check of `on` with a value other
  ## than a literal `on`: `{.push rangeChecks: on.}` in a body, or the
  ## routine's own `{.rangeChecks: off.}`. Neither is seen by the scan of the
  ## module's statements, which does not enter a routine.
  if n.kind == nnkExprColonExpr and n.len == 2:
    let named = checksNamed(nameOf(n[0]))
    let t = turnsOn(n[1])
    if (named * off != {} and t != 0) or (named * on != {} and t != 1):
      return "`" & nameOf(n[0]) & ": " & n[1].repr & "` at line " &
             $n.lineInfoObj.line
  for c in n:
    let r = inRoutineChecks(c, off, on)
    if r.len > 0: return r

proc lastLine(n: NimNode): int =
  result = n.lineInfoObj.line
  for c in n: result = max(result, lastLine(c))

const hostKinds = {nnkProcDef, nnkFuncDef, nnkMethodDef, nnkIteratorDef,
                   nnkConverterDef, nnkLambda, nnkDo}
  ## RFC-0016 int6-a5. What a routine can be declared inside.

proc pushesInBody(n: NimNode; root = true): bool =
  ## A check pragma among `n`'s statements, a routine declared in it aside
  ## (its pushes are its own).
  if not root and n.kind in hostKinds: return false
  if n.kind == nnkPragma and inRoutineChecks(n, allChecks, allChecks).len > 0:
    return true
  for c in n:
    if pushesInBody(c, false): return true

type PushHost = tuple[first, last: int; node: NimNode; name: string]

var pushHosts {.compileTime.}: Table[string, seq[PushHost]]
  ## RFC-0016 int6-a5. Per file read, the routines whose body pushes a check
  ## option, with their line spans: computed once per file.

proc collectHosts(n: NimNode; acc: var seq[PushHost]) =
  if n.kind in hostKinds and n.len > 6 and pushesInBody(n[6]):
    let name = if n.kind in {nnkLambda, nnkDo}: "an anonymous routine"
               else: "`" & routineNameOf(n[0]) & "`"
    acc.add (first: n.lineInfoObj.line, last: lastLine(n), node: n, name: name)
  for c in n: collectHosts(c, acc)

proc pushingHost(file: string; ast, def: NimNode; line: int): string =
  ## RFC-0016 int6-a5. "" or the routine whose body pushes a check option and
  ## holds the routine written at `line` (`def`, nil for a lambda). A routine
  ## declared inside such a body takes the push's options where it stands,
  ## which the scan of the module's statements never sees.
  if file notin pushHosts:
    var acc: seq[PushHost]
    collectHosts(ast, acc)
    pushHosts[file] = acc
  for h in pushHosts[file]:
    if h.node == def: continue
    if h.node.kind in {nnkLambda, nnkDo} and h.first == line: continue
    if h.first <= line and line <= h.last:
      return h.name & " (line " & $h.first & ")"

proc bodyAstOf(file: string): NimNode =
  ## `file` parsed from disk, once; nil where it cannot be read or parsed.
  if file notin bodyAsts:
    var ast: NimNode
    var text: string
    if readSource(compileTimeEnv(), file, text).len == 0:
      try: ast = parseStmt(text, file)
      except ValueError: discard
    bodyAsts[file] = ast
  bodyAsts[file]

const loopIncExemptions* = [
  (file: "system/iterators.nim", name: "unCheckedInc"),
  (file: "pure/collections/sequtils.nim", name: "unCheckedInc")]
  ## RFC-0016 int6-t. The push regions the opaque defect scan reads through
  ## (`bodyCheckPragma`): a template of the toolchain's `lib/` file,
  ## whose body is exactly `{.push overflowChecks: off.}` `inc(x)` `{.pop.}`,
  ## as expanded inside a routine of that same file. Each entry is audited, use
  ## site by use site, in `tests/0016-allowlist/pushexempt.txt`, which must
  ## list exactly these (`tsymex_0016_int6t_typedpush`). RFC-0016 int6-u:
  ## `sequtils`' own copy, inside that module's routines. RFC-0016 int6-x2:
  ## and where one of its exported templates expands it into a caller's
  ## routine, stepping that template's own counter (`loopIncCounters`).

const loopIncCounters* = [
  (file: "pure/collections/sequtils.nim", tpl: "findIt", counter: "i",
   byItems: true),
  (file: "pure/collections/sequtils.nim", tpl: "keepItIf", counter: "pos",
   byItems: false),
  (file: "pure/collections/sequtils.nim", tpl: "toSeq2", counter: "i",
   byItems: false),
  (file: "pure/collections/sequtils.nim", tpl: "toSeq", counter: "i",
   byItems: false)]
  ## RFC-0016 int6-x2. The audited use sites of a `loopIncExemptions`
  ## template inside a template of the same file, which expands the step into
  ## its caller's routine: the template `tpl` declares the stepped `counter`
  ## in its own text, a local the template generates (gensym), so no code
  ## outside it can name the variable. A step is one of these when its
  ## counter's symbol is declared at that declaration's position in the
  ## toolchain's file (`loopIncCounterSites`), never by the counter's name. The
  ## positions and each counter's bound are listed in
  ## `tests/0016-allowlist/pushexempt.txt` under the template's entry.
  ## RFC-0016 int6-f2: `byItems`, the counter is stepped once per item the
  ## caller's `items(s)` yields and nothing else bounds it, so the step is
  ## admitted only where the typed loop around it calls a stdlib `items`
  ## whose yields are bounded below `high(int)` (`boundedItemsLoop`).

proc isLoopIncTemplate(t: NimNode; name: string): bool =
  ## The parsed `template <name>(x) = {.push overflowChecks: off.}; inc(x);
  ## {.pop.}`, and nothing else.
  if t.kind != nnkTemplateDef or t.len < 7 or routineNameOf(t[0]) != name:
    return false
  let ps = t[3]
  if ps.kind != nnkFormalParams or ps.len != 2 or ps[1].kind != nnkIdentDefs or
     ps[1].len != 3: return false
  let x = nameOf(ps[1][0])
  let b = t[6]
  if b.kind != nnkStmtList or b.len != 3: return false
  let push = b[0]
  if push.kind != nnkPragma or push.len != 2 or nameOf(push[0]) != "push" or
     push[1].kind != nnkExprColonExpr or push[1].len != 2 or
     checksNamed(nameOf(push[1][0])) != {coOverflow} or
     turnsOn(push[1][1]) != 0: return false
  let step = b[1]
  if step.kind notin {nnkCall, nnkCommand} or step.len != 2 or
     nameOf(step[0]) != "inc" or nameOf(step[1]) != x or x.len == 0:
    return false
  b[2].kind == nnkPragma and b[2].len == 1 and nameOf(b[2][0]) == "pop"

proc findTemplateDefs(n: NimNode; name: string; acc: var seq[NimNode]) =
  ## Every parsed `template <name>` in `n`, at any depth (`since (1, 1):`
  ## wraps some of `sequtils`' templates).
  if n.kind == nnkTemplateDef and n.len >= 7 and routineNameOf(n[0]) == name:
    acc.add n
  for c in n: findTemplateDefs(c, name, acc)

proc counterDecls(n: NimNode; counter: string; acc: var seq[NimNode]) =
  ## The `IdentDefs` declaring the plain name `counter` (no pragma, so no
  ## `{.inject.}`) in a `var` section of the parsed template body `n`.
  if n.kind == nnkVarSection:
    for d in n:
      if d.kind == nnkIdentDefs:
        for i in 0 ..< d.len - 2:
          if d[i].kind == nnkIdent and d[i].strVal == counter: acc.add d
  for c in n: counterDecls(c, counter, acc)

proc loopIncCounterSites*(file: string; path = ""):
    seq[tuple[tpl: string; line, col: int]] =
  ## RFC-0016 int6-x2. The positions, in the toolchain file `file` (its path
  ## under `lib/`; read from `path`, the compiler's own spelling of it, when
  ## given), of the `loopIncCounters` declarations: each template is
  ## defined once there, without pragmas (no `{.dirty.}`, which would inject
  ## its locals), and declares its counter exactly once. A template that does
  ## not has no site (the toolchain no longer has the audited shape).
  let ast = bodyAstOf(if path.len > 0: path else: configuredLibDir / file)
  if ast == nil: return
  for e in loopIncCounters:
    if e.file != file: continue
    var defs: seq[NimNode]
    findTemplateDefs(ast, e.tpl, defs)
    if defs.len != 1 or defs[0][4].kind != nnkEmpty: continue
    var decls: seq[NimNode]
    counterDecls(defs[0][6], e.counter, decls)
    if decls.len != 1: continue
    let li = decls[0].lineInfoObj
    result.add (e.tpl, li.line, li.column)

proc auditedCounter(counter: NimNode; rel: string): string =
  ## RFC-0016 int6-x2. The template of `rel`'s `loopIncCounterSites` at whose
  ## counter declaration the variable `counter` (a symbol of a typed body) is
  ## declared, or "". Read from the symbol's own declaration (`getImpl`, its
  ## `IdentDefs`), whose position is the template text's when a template
  ## generated it: user code declares its variables in its own file.
  if counter == nil or counter.kind != nnkSym or counter.symKind != nskVar:
    return ""
  let decl =
    try: counter.getImpl
    except CatchableError: return ""
  if decl == nil or decl.kind != nnkIdentDefs: return ""
  let li = decl.lineInfoObj
  if libRelPath(li.filename, configuredLibDir) != rel: return ""
  for s in loopIncCounterSites(rel, li.filename):
    if s.line == li.line and s.col == li.column: return s.tpl

const boundedItemsFile* = "system/iterators.nim"
  ## RFC-0016 int6-f2. The toolchain file whose `items` iterators a
  ## `byItems` counter's loop may call (`boundedItemsLoop`). `system`
  ## includes it; its iterators' owner is the module symbol `iterators`.

type ItemsBound* = enum
  ibNone     ## not one of the audited families: unbounded for the scan
  ibLength   ## openArray, array, seq, string, set, cstring
  ibOrdinal  ## an ordinal `Slice[T]` or an enum `typedesc[T]`

proc itemsBoundAt*(path: string; line: int): ItemsBound =
  ## RFC-0016 int6-f2. The family of the `items` iterator defined at `line`
  ## of the toolchain file `path` (`boundedItemsFile`), by its first
  ## parameter's type in the parsed text: a length (or a set's element range,
  ## or one object's bytes) bounds the yields of an openArray, array, seq,
  ## string, set or cstring; a `Slice` or a `typedesc` yields every value of
  ## its ordinal range, which only the element's width bounds. Anything else
  ## (the toolchain changed) is `ibNone`.
  let ast = bodyAstOf(path)
  if ast == nil: return ibNone
  let def = findRoutineDef(ast, "items", line)
  if def == nil or def.kind != nnkIteratorDef or def.len < 7: return ibNone
  let ps = def[3]
  if ps.kind != nnkFormalParams or ps.len != 2 or
     ps[1].kind != nnkIdentDefs or ps[1].len != 3: return ibNone
  let t = ps[1][1]
  if t.kind == nnkIdent and t.strVal in ["string", "cstring"]: return ibLength
  if t.kind != nnkBracketExpr or t.len < 2: return ibNone
  let head = nameOf(t[0])
  if head in ["openArray", "array", "seq", "set"]: ibLength
  elif head in ["Slice", "typedesc"]: ibOrdinal
  else: ibNone

proc boundedItemsLoop*(loop: NimNode): bool =
  ## RFC-0016 int6-f2. Is the typed `for` statement `loop` a call of a
  ## `boundedItemsFile` `items` iterator whose yields stay below `high(int)`?
  ## Read from the resolved iterator symbol: its name, its owner module
  ## (`iterators`), and its declaration's position in the toolchain's file,
  ## classified by `itemsBoundAt`. A length family is bounded by a length
  ## (at most `high(int)`); an ordinal family only when its element is at
  ## most 4 bytes (at most 2^32 values: an `int` slice yields up to 2^64).
  ## A user's `items`, a `{.closure.}` one, or `sequtils`' over a closure
  ## iterator is not: nothing bounds how often it yields.
  if loop == nil or loop.kind != nnkForStmt or loop.len < 3: return false
  let call = loop[^2]
  if call.kind notin {nnkCall, nnkCommand} or call.len != 2 or
     call[0].kind != nnkSym: return false
  let it = call[0]
  if it.symKind != nskIterator or it.strVal != "items": return false
  let o = it.owner
  if o == nil or o.kind != nnkSym or o.symKind != nskModule or
     o.strVal != boundedItemsFile.splitFile.name: return false
  let decl =
    try: it.getImpl
    except CatchableError: return false
  if decl == nil or decl.kind != nnkIteratorDef: return false
  let li = decl.lineInfoObj
  if libRelPath(li.filename, configuredLibDir) != boundedItemsFile:
    return false
  case itemsBoundAt(li.filename, li.line)
  of ibLength: true
  of ibOrdinal:
    let v = loop[0]
    if v.kind != nnkSym: return false
    let size =
      try: getSize(v)
      except CatchableError: -1
    size in 1 .. 4
  of ibNone: false

proc loopIncExempt*(owner, push: NimNode; counter: NimNode = nil;
                    loop: NimNode = nil): bool =
  ## RFC-0016 int6-t. Is the pragma statement `push`, in the typed body of the
  ## routine definition `owner`, the push of a `loopIncExemptions` template as
  ## that template's own module expands it? Identified by position, never by a
  ## name alone: `push` stands at the push of the template's body in the
  ## toolchain's own file (a template expansion carries its definition's
  ## positions), that file's text there is the template's exact shape
  ## (`isLoopIncTemplate`), and `owner` is a routine of the same file. The
  ## caller checks the expanded region's own shape. RFC-0016 int6-x2: or
  ## `owner` is any routine and the stepped `counter` is declared at an
  ## audited counter site of that file (`auditedCounter`): the template is
  ## unexported, but `import std/sequtils {.all.}` reaches it, so a routine
  ## outside the file is admitted only by the counter, never by the push.
  ## RFC-0016 int6-f2: a `byItems` counter only inside `loop`, the innermost
  ## typed `for` around the step, when that loop is one of the template's
  ## own (in `rel`) calling a bounded stdlib `items` (`boundedItemsLoop`).
  if owner == nil or owner.kind notin RoutineNodes or push == nil: return false
  let pli = push.lineInfoObj
  let rel = libRelPath(pli.filename, configuredLibDir)
  if rel.len == 0: return false
  if libRelPath(owner.lineInfoObj.filename, configuredLibDir) != rel:
    let tpl = auditedCounter(counter, rel)
    if tpl.len == 0: return false
    for e in loopIncCounters:
      if e.file == rel and e.tpl == tpl and e.byItems:
        if loop == nil or
           libRelPath(loop.lineInfoObj.filename, configuredLibDir) != rel or
           not boundedItemsLoop(loop):
          return false
  for e in loopIncExemptions:
    if e.file != rel: continue
    let ast = bodyAstOf(pli.filename)
    if ast == nil: return false
    for t in ast:
      if isLoopIncTemplate(t, e.name) and t[6][0].lineInfoObj.line == pli.line:
        return true

# ---- RFC-0016 int6-u: the typed body's check pragmas (moved from dsl_parser,
# so the placement of a routine reads them too) ---------------------------

proc pragmaWord*(n: NimNode): string =
  if n.kind in {nnkIdent, nnkSym}: n.strVal.toLowerAscii else: ""

proc isPushPragma*(n: NimNode): bool =
  n.kind == nnkPragma and n.len >= 1 and pragmaWord(n[0]) == "push"

proc isPopPragma*(n: NimNode): bool =
  n.kind == nnkPragma and n.len == 1 and pragmaWord(n[0]) == "pop"

proc namesCheck*(n: NimNode): bool =
  ## A push item naming a check option (`rangeChecks: off`, `checks: on`).
  let h = if n.kind == nnkExprColonExpr and n.len == 2: n[0] else: n
  checksNamed(nameOf(h)) != {}

proc literalOn*(v: NimNode): int =
  ## 1 on, 0 off, -1 otherwise. The typed body folds `off` and a `const` to
  ## an integer literal.
  case v.kind
  of nnkIntLit .. nnkUInt64Lit: (if v.intVal == 0: 0 elif v.intVal == 1: 1
                                 else: -1)
  of nnkIdent, nnkSym: turnsOn(v)
  else: -1  # k2: fail-closed: -1: parseCheckPragma declines feCheckOption on a value it cannot read

proc implMagic*(impl: NimNode): string =
  ## RFC-0005 S8be / S8bl. The `{.magic: "X".}` name of the routine
  ## declaration `impl`, or "". A magic's semantics are the compiler's: its
  ## body, when it has one, is documentation or a VM fallback, never what
  ## the call does. (Batch 6: S8be's `routineMagic` and S8bl's, which took
  ## the declaration, are this one reader.)
  if impl == nil or impl.kind notin RoutineNodes or impl.len < 5: return ""
  let prag = impl[4]
  if prag.kind != nnkPragma: return ""
  for p in prag:
    if p.kind == nnkExprColonExpr and p.len == 2 and
       p[0].kind in {nnkIdent, nnkSym} and macros.strVal(p[0]) == "magic" and
       p[1].kind in {nnkStrLit .. nnkTripleStrLit, nnkIdent, nnkSym}:
      return macros.strVal(p[1])
  ""

proc routineMagic*(sym: NimNode): string =
  ## RFC-0005 S8be. The `{.magic.}` name of the routine `sym` (`"AddI"` for
  ## `system.+` on `int`), or "" when it has none.
  if sym.kind != nnkSym: return ""
  let impl =
    try: sym.getImpl
    except CatchableError: return ""
  implMagic(impl)

proc loopIncRegion(s, owner: NimNode; loop: NimNode = nil): bool =
  ## RFC-0016 int6-t. Is the statement list `s`, in the typed body of the
  ## routine definition `owner`, exactly an audited loop-counter step: `{.push
  ## overflowChecks: off.}` (no other option), `inc` (`system.inc`, by its
  ## magic) of a local variable or the routine's `result` by one, `{.pop.}`,
  ## whose push is a
  ## `check_options.loopIncExemptions` template's as its own module expands it
  ## (`loopIncExempt`)? Its counter's loop bounds it (the allowlist's audit),
  ## so it neither overflows nor leaves its range: reading the routine as one
  ## scope loses nothing there. `loop`: the innermost typed `for` around `s`
  ## (RFC-0016 int6-f2).
  if s.kind != nnkStmtList or s.len != 3: return false
  let push = s[0]
  if not isPushPragma(push) or push.len != 2: return false
  let it = push[1]
  if it.kind != nnkExprColonExpr or it.len != 2 or
     checksNamed(nameOf(it[0])) != {coOverflow} or literalOn(it[1]) != 0:
    return false
  let step = s[1]
  if step.kind notin {nnkCall, nnkCommand} or step.len notin 2 .. 3 or
     not magicIs(routineMagic(step[0]), "Inc"): return false
  # RFC-0016 int6-w2: `result` is a local slot of the routine as a `var` is
  # (`sequtils.count` steps it); a parameter, a global or a path is not.
  if step[1].kind != nnkSym or step[1].symKind notin {nskVar, nskResult}:
    return false
  if step.len == 3 and
     (step[2].kind notin {nnkIntLit .. nnkInt64Lit} or step[2].intVal != 1):
    return false
  isPopPragma(s[2]) and loopIncExempt(owner, push, step[1], loop)

proc bodyCheckPragma*(n, owner: NimNode; loop: NimNode = nil): NimNode =
  ## RFC-0016 int6-t. The first pragma statement naming a check option in the
  ## typed body `n` of the routine definition `owner` (a routine declared in
  ## it aside: it is not run here), or nil. The typed body keeps every push
  ## and pop as a pragma statement, whether the definition's text wrote it, a
  ## template expanded it or a macro emitted it; int6-a5 and int6-m6 read the
  ## text, which holds the first only. An audited loop-counter step
  ## (`loopIncRegion`) is not one. `loop`: the innermost `for` statement
  ## whose body `n` is in (RFC-0016 int6-f2), passed down into a body only.
  if n == nil or n.kind in RoutineNodes: return nil
  if loopIncRegion(n, owner, loop): return nil
  if n.kind == nnkPragma:
    for it in n:
      if namesCheck(it): return n
  for i in 0 ..< n.len:
    let inner = if n.kind == nnkForStmt and i == n.len - 1: n else: loop
    result = bodyCheckPragma(n[i], owner, inner)
    if result != nil: return

const typedHostKinds = {nskProc, nskFunc, nskMethod, nskIterator, nskConverter}
  ## RFC-0016 int6-u. The owners a routine can be declared inside.

proc typedPushingHost(impl: NimNode): string =
  ## RFC-0016 int6-u. "" or why the typed routine definition `impl` is
  ## declared inside a routine, at any depth, whose typed body holds a check
  ## pragma (`bodyCheckPragma`): a routine declared there compiles under that
  ## push where it stands. `pushingHost` reads the definitions' text, which a push
  ## a template expands or a macro emits is not in; the typed body keeps every
  ## push as a pragma statement. Fail closed: a host whose typed body cannot
  ## be read, or a definition whose owner cannot be found, is named too.
  if impl.len == 0 or impl[0].kind != nnkSym:
    return "its definition's name is no symbol (`" &
           (if impl.len > 0: impl[0].repr else: "") & "`), so the routine " &
           "it is declared inside, if any, is not found"
  var o = impl[0].owner
  while o != nil and o.kind == nnkSym and o.symKind in typedHostKinds:
    let h =
      try: o.getImpl
      except CatchableError: nil
    let at = "it is declared inside `" & o.strVal & "` (line " &
             $o.lineInfoObj.line & "), whose typed body "
    if h == nil or h.kind notin RoutineNodes or h.len <= 6:
      return at & "the scan cannot read: a push there would place it"
    if bodyCheckPragma(h[6], h) != nil:
      return at & "pushes check options (a template's or a macro's push " &
             "among them): it takes that push's where it stands, which the " &
             "scan of the module's statements does not read"
    o = o.owner

type CallHost = tuple[first, last: int; node: NimNode]

var callHosts {.compileTime.}: Table[string, seq[CallHost]]
  ## RFC-0016 CR4-H1. Per file read, the module-level calls with a statement
  ## block among their arguments (a template's or a macro's `body`), with
  ## their line spans: computed once per file.

proc collectCallHosts(n: NimNode; acc: var seq[CallHost]) =
  if n.kind in hostKinds or n.kind in {nnkTemplateDef, nnkMacroDef}: return
  if n.kind in {nnkCall, nnkCommand}:
    var block0 = false
    for c in n:
      if c.kind == nnkStmtList: block0 = true
    if block0: acc.add (first: n.lineInfoObj.line, last: lastLine(n), node: n)
  for c in n: collectCallHosts(c, acc)

proc reachesDef(n, def: NimNode): bool =
  ## `def` is under `n`, through no other routine.
  if n == def: return true
  if n.kind in hostKinds: return false
  for c in n:
    if reachesDef(c, def): return true

proc expanderDefs(n: NimNode; name: string; acc: var seq[NimNode]) =
  if n.kind in {nnkTemplateDef, nnkMacroDef} and n.len >= 7 and
     nimIdentNormalize(routineNameOf(n[0])) == name:
    acc.add n
  for c in n: expanderDefs(c, name, acc)

proc visibleAsts(m: ModuleScan; own: NimNode; unplaced: var string):
    seq[NimNode] =
  ## The parsed texts a call at the module's level may name a template or
  ## macro from: this module's own and every user module it imports, what
  ## those re-export too. `unplaced` is set where one cannot be read.
  result.add own
  var queue: seq[string]
  for ev in m.events:
    if not ev.call: queue.add ev.targets
  var seen: seq[string]
  while queue.len > 0:
    let t = queue.pop()
    if t.startsWith("lib:") or t.startsWith("lib?:"): continue
    if t.startsWith("?"):
      unplaced = "an import names a module the scan cannot place (`" & t & "`)"
      continue
    let raw = anchored(t)
    let path = if raw.len > 0: raw else: t
    let key = normalPath(path)
    if key in seen: continue
    seen.add key
    let ast = bodyAstOf(path)
    if ast == nil:
      unplaced = "`" & path.extractFilename & "` cannot be read"
      continue
    result.add ast
    queue.add defsOf(path).reexports

proc expansionPushes(asts: seq[NimNode]; callee: string;
                     seen: var seq[string]): string =
  ## "" or why the template or macro `callee` may push a check option where it
  ## expands: a macro (its expansion is not read), or a template whose text,
  ## or a template or macro its text calls, holds a check pragma. A name no
  ## visible text defines is the toolchain's (none pushes, int6-w2).
  if callee in seen or seen.len > 32: return
  seen.add callee
  var defs: seq[NimNode]
  for a in asts: expanderDefs(a, callee, defs)
  for d in defs:
    if d.kind == nnkMacroDef:
      return "a macro, whose expansion the scan does not read"
    if pushesInBody(d[6]):
      return "a template whose text pushes check options"
    var calls: seq[NimNode]
    proc gather(n: NimNode; acc: var seq[NimNode]) =
      if n.kind in {nnkCall, nnkCommand, nnkCallStrLit, nnkIdent}:
        acc.add n
      for c in n: gather(c, acc)
    gather(d[6], calls)
    for c in calls:
      let nm = calleeName(c)
      if nm.len == 0 or nm == callee: continue
      let inner = expansionPushes(asts, nm, seen)
      if inner.len > 0:
        return "a template that expands `" & nm & "`, " & inner

proc moduleLevelExpansionHost(file: string; ast, def: NimNode; line: int;
                              m: ModuleScan): string =
  ## RFC-0016 CR4-H1. "" or why the routine `def`, declared at its module's
  ## level, lies inside the arguments of a template's or a macro's call whose
  ## expansion may push a check option around it. As `pushingHost` and
  ## `typedPushingHost` place a routine declared inside a routine, this
  ## places one declared in a call's block: the scan reads this module's text
  ## alone, where an imported template's matched push and pop are not. Fail
  ## closed: a callee that is no name, a macro, or a module that cannot be
  ## read declines; a callee defined in no visible text is the toolchain's.
  if def == nil: return
  if file notin callHosts:
    var acc: seq[CallHost]
    collectCallHosts(ast, acc)
    callHosts[file] = acc
  var unplaced = ""
  var asts: seq[NimNode]
  var read = false
  for h in callHosts[file]:
    if h.first > line or line > h.last or not reachesDef(h.node, def): continue
    let callee = calleeName(h.node)
    let at = "it is declared inside the call of `" & h.node[0].repr &
             "` (line " & $h.first & "), "
    if callee.len == 0:
      return at & "whose callee is not a name the scan reads"
    if not read:
      asts = visibleAsts(m, ast, unplaced)
      read = true
    var seen: seq[string]
    let why = expansionPushes(asts, callee, seen)
    if why.len > 0:
      return at & "which is " & why & ": it takes that push's where it " &
             "stands, which the scan of the module's statements does not read"
    if unplaced.len > 0:
      var defs: seq[NimNode]
      for a in asts: expanderDefs(a, callee, defs)
      if defs.len == 0:
        return at & "whose definition the scan cannot find: " & unplaced

proc positionUnreadable(impl: NimNode; file: string; line: int;
                        st: CheckState; m: ModuleScan): string =
  ## RFC-0016 PRC-07. Why the routine's check state at the four checks cannot be
  ## taken as one answer: "" when it can. The walker models a routine compiled
  ## with such an option off as unchecked and one compiled with it on as
  ## checked, at its position (RFC-0016 int6, in both build directions); a
  ## routine that is checked at some positions only, or whose position is
  ## ambiguous, is neither, and is never assumed to be the build's setting.
  ## In a build with the option on, an ambiguous position is a deviation
  ## already (`checks` keeps it, and the routine declines).
  ##
  ## RFC-0016 int6-a5: a routine declared inside a body that pushes is
  ## unreadable here: its position is that push's; RFC-0016 int6-u: that body
  ## is read typed as well as by text (`typedPushingHost`); RFC-0016 int6-w2:
  ## the typed read holds for a stdlib routine too. (A push among the
  ## routine's own statements is the parser's: it walks each pair as a
  ## region, and the opaque defect scan finds it in the typed body, int6-t.)
  let off = scopedChecks - buildSemantics.checks
  let both = off * st.maybeOn * st.maybeOff
  if both != {}:
    return "its position is both pushed on and off for " & $both
  if not isStdlibFile(file):
    # RFC-0016 int6-w: the text the scan read (`m`), where it read this file:
    # a second read from disk is another snapshot of a file that may be
    # edited during the compile.
    var ast = scannedAst(m, file)
    if ast == nil: ast = bodyAstOf(file)
    if ast != nil:
      let def = findRoutineDef(ast, routineNameOf(impl[0]), line)
      let host = pushingHost(file, ast, def, line)
      if host.len > 0:
        return "it is declared inside " & host & ", whose body pushes " &
               "check options: it takes that push's where it stands, which " &
               "the scan of the module's statements does not read"
  # RFC-0016 int6-u: the host found in the typed body, where a template's or a
  # macro's push is (the text above holds the written ones alone). RFC-0016
  # int6-w2: for a stdlib routine too. The typed body keeps every push as a
  # pragma statement, the written ones included, so this alone places a stdlib
  # routine declared inside a pushing stdlib body, sound by construction and
  # not by a census of the toolchain (none on 2.2.10, by its text). A routine
  # declared at its module's level, every stdlib one on 2.2.10, has a module
  # owner and costs one step.
  let typed = typedPushingHost(impl)
  if typed.len > 0: return typed
  # RFC-0016 CR4-H1: a routine at its module's level inside a template's or
  # macro's call: the expansion's push is nowhere in this module's text.
  if not isStdlibFile(file):
    var ast = scannedAst(m, file)
    if ast == nil: ast = bodyAstOf(file)
    if ast != nil:
      let def = findRoutineDef(ast, routineNameOf(impl[0]), line)
      let top = moduleLevelExpansionHost(file, ast, def, line, m)
      if top.len > 0: return top

proc stdlibDefClean(impl: NimNode; file: string; line: int;
                    m: ModuleScan): bool =
  ## RFC-0016 int6-a. A stdlib routine's definition, in the text the scan read,
  ## holds no pragma naming any of the scoped checks, whatever its value: its
  ## position's state then holds for its whole body. False where the text or
  ## the definition cannot be found (fail closed: the push stays a deviation).
  let ast = scannedAst(m, file)
  if ast == nil: return false
  let def = findRoutineDef(ast, routineNameOf(impl[0]), line)
  if def == nil: return false
  # Every value of a named check is a hit with `off` and `on` both the set.
  inRoutineChecks(def, scopedChecks, scopedChecks).len == 0

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
  discard scanOf(root, rootRaw)
  if moduleScans[root].unknown.len > 0:
    return RoutineChecks(checks: allChecks, assertsMaybeOff: true,
                         why: moduleScans[root].unknown)
  # RFC-0016 int6-a6: the compile order replayed. A user module it reaches is
  # read from the state it was first compiled from; a library one takes what
  # an import under a push may hand it (`libTaint`).
  replayCompileOrder()
  let rootLib = isLibraryFile(root, configuredLibDir)
  let replayed = runReplay.exact and (rootLib or root in runReplay.entry)
  let scan =
    if replayed and not rootLib: scanOf(root, rootRaw, runReplay.entry[root])
    else: moduleScans[root]
  if scan.unknown.len > 0:
    return RoutineChecks(checks: allChecks, assertsMaybeOff: true,
                         why: scan.unknown)
  # RFC-0016 int6-w: the scan's text is read from disk when a macro first asks,
  # not when the compiler parsed the module; a file edited in between places
  # the routine against pushes it was not compiled under. Not read, then.
  if not isStdlibFile(file):
    let stale = textDisagrees(scan, file,
                              nameOf(if impl[0].kind == nnkPostfix: impl[0][1]
                                     else: impl[0]), li.line)
    if stale.len > 0:
      return RoutineChecks(checks: allChecks, assertsMaybeOff: true,
        why: "the module's text on disk is not the text the compiler parsed: " &
             stale)
  let st = stateAt(scan, file, li.line, li.column)
  # RFC-0016 int6-a2: a position read both ways may be decided by a
  # `defined(x)` the scan could not evaluate; the entry macro asks its call
  # site (`undecidedDefines`) and expands again.
  if st.maybeOn * st.maybeOff != {}: noteUndecided(scan)
  result.checks = deviation(st)
  result.assertsMaybeOff = coAssert in st.maybeOff or
    coAssert in scan.everything.maybeOff
  # The coarse reading, where the compile order is not replayed (`runReplay.why`):
  # a user's importer hands on what it pushed to any module this walk reaches: the
  # chain from what it names is not read. `system.nim` and `math.nim` import under
  # their own pushes, so a stdlib importer hands it on to what it names alone.
  # Importers are found by the import graph from this module and the project file.
  # Each once: this runs for every routine the walk registers, and a list
  # re-appended per routine made the loop below quadratic in the program's
  # callees (the compile-time VM's iteration limit, on the replay suites).
  for l in moduleScans[root].importLeak:
    let e = (root: root, name: l.name, opts: l.opts)
    if e notin runLeaks: runLeaks.add e
  let rootStdlib = isStdlibFile(root)
  let rootSystem = isSystemFile(root)
  if not rootStdlib:
    enterGraph(rootRaw)
    enterGraph(querySetting(projectFull))
    if runUnknown.len > 0:
      return RoutineChecks(checks: allChecks, assertsMaybeOff: true, why: runUnknown)
  let moduleName = root.extractFilename.changeFileExt("")
  var leaked: set[CheckOption]
  if replayed:
    # RFC-0016 int6-a6: a user module's leak is in its scan's start state,
    # a plain position state; `system` is compiled before any user code.
    if rootLib and not rootSystem:
      leaked = runReplay.libTaint
      result.checks = result.checks + leaked
  else:
    # The coarse reading (`runReplay.why`): an importer's push reaches every
    # module the named one may reach.
    for l in runLeaks:
      if l.root == root: continue
      let rk = l.root & "|" & l.name
      let reaches =
        if l.name == moduleName: true
        elif rootSystem or isStdlibFile(l.root): false
        elif rk in runReach: root in runReach[rk] or rootStdlib
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
  result.bodyRegions = not isStdlibFile(file)
  let unreadable = positionUnreadable(impl, file, li.line, st, scan)
  if unreadable.len > 0:
    result.why = "the routine's range, bound, field, object or overflow checks differ " &
      "within it, not modelled as one setting: " & unreadable
  # RFC-0016 int6: a check the build has on and the routine's position has off
  # on every reading is modelled (`offModelled`): the walker scopes the body
  # without it. Ambiguous, leaked and stdlib positions stay deviations.
  # RFC-0016 int6-o: `overflowChecks` likewise; its body is walked unchecked
  # (`asPushedOff`), as the build route walks a `--overflowChecks:off` build.
  # `overflowOn` above was read before the move, so it stays false for it.
  # RFC-0016 int6-a: a stdlib routine likewise, now that a body is walked
  # under its own scope: the K4c delta was the only model of a stdlib push
  # when a routine could only be walked under the build's checks. Its file's
  # text is the scan's (`stdlibDefClean`), so a pragma inside its definition
  # is seen; one that names any of the checks leaves them deviations.
  let stdlibClean = rootStdlib and result.why.len == 0 and
                    stdlibDefClean(impl, file, li.line, scan)
  if result.why.len == 0 and (not rootStdlib or stdlibClean):
    for co in scopedChecks * buildSemantics.checks:
      if co in result.checks and co in st.maybeOff and co notin st.maybeOn and
         co notin leaked:
        if rootStdlib and co == coOverflow:
          result.overflowOffExact = true
        else:
          result.checks.excl co
          result.offModelled.incl co
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
