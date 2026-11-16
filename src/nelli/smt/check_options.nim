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
import ./check_scan    ## RFC-0016 D5: the pure scan; this module is its adapter
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

proc compileTimeEnv(): SourceEnv =
  ## The compiler's own view: the project's directories and search paths, and
  ## the compiler's file reader.
  SourceEnv(exists: diskExists, read: diskRead, anchor: anchored,
            searchPaths: querySettingSeq(searchPaths))

proc scanModuleText*(path, text: string): ModuleScan =
  ## The scan of a module whose text is at hand; an `include` is read from disk.
  scanModuleText(path, text, compileTimeEnv())

proc scanModule*(path: string): ModuleScan =
  ## The scan of a module on disk.
  scanModule(path, compileTimeEnv())

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
      if readSource(compileTimeEnv(), file, text).len == 0:
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
