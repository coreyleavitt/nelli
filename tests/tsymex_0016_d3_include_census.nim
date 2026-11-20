## RFC-0016 0.10.0 review D3 (the runtime `include` files share one namespace):
## the include census. Slice D3c-0 freezes the surface, slices D3c-1 and D3c-2 extend it
## to the `symval.nim` and `walk_state.nim` leaves.
##
## `src/nelli/smt/runtime.nim` textually includes five files. An include sees
## every name `runtime.nim` defines, so the boundary is invisible to the
## compiler. This test makes it visible, by text scan (the house pattern of
## `tsymex_0016_k2a_census.nim`):
##
##   * the include list and its order are exact;
##   * no `runtime_*.nim` has an `import` (an include compiles inside
##     `runtime.nim`; once one becomes a module this test is edited in the
##     slice that makes it so, and not before);
##   * per include, the count of runtime-private symbols it references has a
##     ceiling that only goes down. A symbol is runtime-private when
##     `runtime.nim` defines it at top level (a proc, template, type, const,
##     var or threadvar, or a field line of one of those blocks) and the
##     include does not define it itself. Identifiers are matched in comment-
##     and string-stripped text, so the count is approximate but monotone in
##     the real coupling;
##   * `runtime.nim` has no forward declaration of a `heap_model` or `z3check`
##     proc (D3c-6 deleted the block: the algebra is imported, not declared),
##     `heap_model.nim` imports only leaves, names no `runtime.nim` symbol and
##     resets every run-state threadvar it owns in one proc;
##   * the `symval.nim` and `walk_state.nim` leaves import only the allowed
##     leaves, `walk_state` resets every threadvar it owns in one proc, its
##     `sync*` procs append on the sinks pointer (no forward declaration is
##     left in `runtime.nim`), and `runtime.nim`
##     defines none of the names that moved into it.
import std/[unittest, os, strutils, sets, tables]
import audit_scan_utils
import nelli/smt/walk_state   ## `LowerHooks`'s declared fields, by `fieldPairs`

const
  root = currentSourcePath().parentDir() / ".."
  smt = root / "src" / "nelli" / "smt"

  expectedIncludes = ["runtime_heap.nim"]

  ## Includes that became real modules (D3c-3: exceptions, D3c-4: floats,
  ## D3c-5: closures, D3c-7: strings).
  movedToModules = ["runtime_exceptions.nim", "runtime_floats.nim",
                    "runtime_closures.nim", "runtime_strings.nim"]

  ## D3c-8: the exact set of `runtime.nim`-private names the heap include
  ## (the walker's statement arm) references, sorted. The scan is textual: a
  ## local that shares a name with a `runtime.nim` symbol (`exact`) is counted.
  ## What slice D3c-6 made real modules below `runtime.nim`: the heap algebra
  ## and the sort-checked Z3 term builders it rests on.
  hmAllowed = ["std/tables", "std/options", "std/sets", "std/strutils",
               "std/hashes", "std/algorithm", "z3",   # RFC-0016 INT-83, INT-84
               "./types", "./abstraction", "./symval", "./walk_state", "./z3check",
               "./variant_layout",   ## R2-4: the union byte image of the moved allocator
               "../thread_state"]  ## S8ck-r: the Z3-free per-thread release leaf
  zcAllowed = ["z3", "./types", "./symval"]

  ## The decl-kind caches of the linked Z3: the same in every run, read in a
  ## probe context (`probeContext`), so `resetHeapModel` leaves them alone.
  hmProcessStable = ["storeDeclKind", "selectDeclKind", "constArrayDeclKind",
                     "iteDeclKind", "heapChainKinds",
                     "provKinds",   # RFC-0016 INT-82
                     "madeKinds"]   # RFC-0016 INT-85

  heapPinned = [
    "AddrCellEntry", "Degrade", "ElemCell", "Path", "PtrLeafAim",
    "PtrStore", "Survivors", "WalkCtx",
    "bitsPlace", "callGuardedNames", "cellValue", "coerceIntLit",
    "crashRaise", "deadElemRefs",
    "degrade", "discConst", "drainPendingLowerEffects",
    "drainScalarRaiseForks", "effectiveHeapDepthLimit", "entryValueOf",
    "exact", "fieldsUnchecked", "forkDefect",
    "forkPath", "forkPathTainted", "freshnessCapHints", "globalEntryVals",
    "globalHiddenRoute", "globalInitValue", "guardLiteral", "halted",
    "heapEpochPrefix", "heapInputName", "heapKeyValTy", "imgReadDef",
    "inactiveFieldSide", "isConcolicFollowWalk",
    "liveFrame", "loopArmInfeasible", "lowerInExpr",
    "lowerLeafInExpr", "maybeForkDefect", "noteTableKey", "overlaps",
    "pathInfeasible", "programGlobal", "ptrFamilyHints",
    "ptrFamilyKey", "ptrIdxKey", "ptrKeyKey", "ptrLeafAims",
    "ptrLeafPathStr", "ptrObjKey", "ptrScalarPointee", "ptrSelKey",
    "ptrTargetCode", "sameBranchSymCond",
    "seqStoreArrs", "shouldStop",
    "stampHeapSteps", "storeSeqElem", "symEq", "tabValAt", "tabValTerms",
    "taintInPlace", "unwrittenImage",
    "unwrittenIn", "unwrittenKind", "unwrittenMsg", "unwrittenReadMsg",
    "unwrittenUb", "writeExactArm", 
    # enum members (R2-5: the scan now sees them): `GuardLiteral`, `CapKind`
    # and `DegradeSink` constructors the arm names directly
    "ckHeapDepth", "dsHeapDepth", "dsNewFieldZero", "glFalse"]

  ## The imports `symval.nim` may have: stdlib, `z3`, and the existing leaves.
  symvalAllowed = ["std/tables", "std/options", "std/sets", "std/hashes",
                   "std/strutils", "std/algorithm", "std/math", "z3",
                   "./types", "./abstraction",
                   "../thread_state"]  ## S8ck-r: the Z3-free per-thread release leaf

  ## What slice D3c-1 moved out of `runtime.nim`.
  movedNames = [
    "SVKind", "SymVal", "Env", "plainEnglishSymValKind", "liftBV", "ofBool",
    "bvVar", "bvRangeConds", "queueDegrade", "StrBuf", "VariantAxisSym",
    "truncBV",
    "sameSymVal"]   ## INT-34 B0: pure `SymVal` code, returned to the value core

proc leadIdent(s: string): string =
  for c in s:
    if c in IdentChars: result.add c else: break
  if result.len > 0 and result[0] notin IdentStartChars: result = ""

proc declNames(s: string, multi: bool): seq[string] =
  ## The names a declaration's left-hand side binds. `s` starts at the name
  ## (after the keyword, or an indent-2 block line). With `multi`, `a, b: T`
  ## and `a*, b = 1` bind both names; the list ends at the first `=` or `:`.
  var lhs = s
  if multi:
    for stop in ["=", ":"]:
      let q = lhs.find(stop)
      if q >= 0: lhs = lhs[0 ..< q]
    for w in lhs.split(','):
      let n = leadIdent(w.strip())
      if n.len > 0: result.add n
  else:
    let n = leadIdent(lhs.strip())
    if n.len > 0: result.add n

proc enumMembers(s: string): seq[string] =
  ## Members listed in `s` (comma separated, `= value` and pragmas dropped).
  for w in s.split(','):
    let n = leadIdent(w.split('=')[0].strip())
    if n.len > 0: result.add n

const perModuleNames = ["releaseThreadState"]
  ## RFC-0016 S8ck-r: names every module with threadvars defines privately,
  ## by convention (its `registerThreadStateRelease` argument). Two modules
  ## defining one is the convention, not code left behind by a move, so the
  ## moved-name checks below skip them.

proc definedNames(text: string): HashSet[string] =
  ## Top-level definitions: `proc|func|template|macro|iterator|converter|
  ## method|type|var|let|const NAME` at column 0, the NAME lines (indent 2)
  ## of a bare `type`/`var`/`let`/`const` block, every name of a multi-name
  ## `var|let|const a, b` declaration, and every member of a top-level enum
  ## (inline `= enum a, b` or one or more lines below the `= enum`): an enum
  ## member is a bare identifier any file that sees the type can name.
  var inBlock = false
  var blockKw = ""
  var enumIndent = -1      # indent of the `X = enum` line while in its body
  let stripped = codeOf(text).splitLines
  let rawLines = text.splitLines
  for li, raw in rawLines:
    if raw.strip().len == 0 or raw[0] == '#': continue
    let l = stripped[li]
    if l.strip().len == 0: continue
    let indent = raw.len - raw.strip(trailing = false).len
    if enumIndent >= 0:
      if indent > enumIndent:
        for m in enumMembers(l): result.incl m
        continue
      enumIndent = -1
    var decl = ""            # the text of a type/var/const line after its keyword
    if raw[0] != ' ':
      inBlock = false
      let ws = l.splitWhitespace
      if ws.len == 0: continue
      case ws[0]
      of "proc", "func", "template", "macro", "iterator", "converter",
         "method":
        if ws.len > 1:
          let n = leadIdent(ws[1])
          if n.len > 0: result.incl n
      of "type", "var", "let", "const":
        # only a bare keyword opens a block of definitions; after
        # `type Foo = object` the indent-2 lines are its FIELDS, which no
        # other module can name as a bare identifier
        inBlock = ws.len == 1
        blockKw = ws[0]
        if ws.len > 1:
          decl = l.strip()[ws[0].len .. ^1]
          for n in declNames(decl, ws[0] != "type"): result.incl n
      else: discard
    elif inBlock and raw.len > 2 and raw[1] == ' ' and raw[2] != ' ':
      decl = l.strip()
      for n in declNames(decl, blockKw != "type"): result.incl n
    if decl.len > 0 and blockKw == "type":
      let e = decl.find("= enum")
      if e >= 0 and decl.find('=') == e:
        for m in enumMembers(decl[e + 6 .. ^1]): result.incl m
        enumIndent = indent

proc referenced(text: string, names: HashSet[string]): HashSet[string] =
  for raw in codeOf(text).splitLines:
    var cur = ""
    for c in raw & " ":
      if c in IdentChars: cur.add c
      else:
        if cur in names: result.incl cur
        cur = ""

proc readSmt(f: string): string = readFile(smt / f)

proc boundHere(text: string): HashSet[string] =
  ## Names a module binds or labels itself, which a same-named `runtime.nim`
  ## top-level symbol does not make a dependency: a `let`/`var`/`const`/`for`
  ## binder, a parameter or tuple-constructor label (`name:` after `(`, `,`
  ## or at the start of a line), and a field read (`x.name`). Used for the
  ## modules only; the heap pin is measured with it.
  for l in codeOf(text).splitLines:
    let t = l.strip()
    let ws = t.splitWhitespace
    if ws.len > 1 and ws[0] in ["let", "var", "const"]:
      # `let a, b = ...` and `var a, b: T`: every name of the comma list
      var lhs = t[ws[0].len .. ^1]
      for stop in [" = ", ":"]:
        let q = lhs.find(stop)
        if q >= 0: lhs = lhs[0 ..< q]
      for w in lhs.split(','):
        result.incl leadIdent(w.strip().strip(chars = {'*'}))
    if ws.len > 1 and ws[0] == "for":
      for w in t[4 .. ^1].split(" in ")[0].split(','):
        result.incl leadIdent(w.strip())
    let isSig = ws.len > 0 and ws[0] in ["proc", "func", "template", "macro",
                                          "iterator", "converter", "method"]
    var prev = ' '   # the last non-space character before the identifier
    var i = 0
    while i < l.len:
      if l[i] in IdentStartChars:
        var j = i
        while j < l.len and l[j] in IdentChars: inc j
        let name = l[i ..< j]
        var k = j
        while k < l.len and l[k] == ' ': inc k
        let labelled = k < l.len and l[k] == ':' and
                       (k + 1 >= l.len or l[k + 1] != ':')
        if prev == '.' or
           (labelled and (prev in {'(', ',', ';'} or l[0 ..< i].strip().len == 0)):
          result.incl name
          if labelled and (isSig or l[0 ..< i].strip().allCharsInSet(
                                       IdentChars + {',', ' '})):
            # `a, b: T`: walk back over the bare names before the label
            var b = i
            while true:
              var m = b
              while m > 0 and l[m - 1] == ' ': dec m
              if m == 0 or l[m - 1] != ',': break
              dec m
              while m > 0 and l[m - 1] == ' ': dec m
              var n0 = m
              while n0 > 0 and l[n0 - 1] in IdentChars: dec n0
              if n0 == m: break
              result.incl l[n0 ..< m]
              b = n0
        prev = 'a'
        i = j
      else:
        if l[i] != ' ': prev = l[i]
        inc i

proc viaHooks(text: string): string =
  ## A call through the hook table (`lowerHooks.lower(`) names a field of the
  ## table, not the `runtime.nim` proc of the same name: drop the member name.
  ## `pathHooks.` (INT-34 B3b, `walk_path`'s own typed table),
  ## `lowerExprHooks.` (INT-34 B4, `lower_expr`'s) and `walkExprHooks.`
  ## (INT-34 B6b, `walk_expr`'s) are the same.
  var i = 0
  while i < text.len:
    var hit = 0
    for tag in ["lowerHooks.", "pathHooks.", "lowerExprHooks.",
                "walkExprHooks."]:
      if text.continuesWith(tag, i): hit = tag.len
    if hit > 0:
      i += hit
      while i < text.len and text[i] in IdentChars: inc i
    else:
      result.add text[i]
      inc i

proc familyImports(): HashSet[string] =
  ## The union of the `./` imports of EVERY runtime-family file, iterated to a
  ## fixpoint: a module the walk reaches only through a leaf (not through
  ## `runtime.nim` or `walk_state.nim`) is found, and a family member found
  ## that way is scanned in its turn. Only family files are traversed: the
  ## modules listed in `noWalkerSites` are reported as imported but their own
  ## imports are never read (they hold no walker site, so nothing past them is
  ## the walker's).
  var scanned: HashSet[string]
  var work: seq[string] = @runtimeFamilyFiles
  while work.len > 0:
    let f = work.pop()
    if f in scanned: continue
    scanned.incl f
    for m in relImports(readSmt(f)):
      let g = m & ".nim"
      result.incl g
      if g in runtimeFamilyFiles and g notin scanned: work.add g

const
  ## Smt modules `runtime.nim`/`walk_state.nim` import that hold no walker
  ## site of the kinds the runtime-family source audits count (raise, degrade,
  ## placeholder read, include surface), each with the reason.
  noWalkerSites = [
    ("walk_log.nim", "the units-log env switch; no lowering"),
    ("buildprofile.nim", "the host build-profile table (a data row)"),
    ("types.nim", "the IR type definitions"),
    ("admission.nim", "the admission verdict model, consulted not walked"),
    ("readonlyaxes.nim", "an axis decision table, no walk sites"),
    ("arith_regime.nim", "the arithmetic-regime owner, pure data"),
    ("definedness.nim", "the definedness axis, pure data"),
    ("variant_layout.nim", "a variant's C layout arithmetic"),
    ("abstraction.nim", "the abstraction pre-pass over the IR"),
    ("regex_parser.nim", "regex parsing to a Z3 regex, no walker state"),
    ("pcre_select.nim", "the PCRE priority-run model"),
    ("pcre_engine.nim", "the PCRE matching engine"),
    ("pcre_syntax.nim", "PCRE syntax tables"),
    ("exn_hierarchy.nim", "the exception type table"),
    ("ptraim.nim", "pointer-aim name parsing"),
    ("nativestack.nim", "a native stack-depth probe"),
    ("stdlib_rows.nim", "the stdlib facet rows (data)"),
    ("errorkind.nim", "the error-kind classification table"),
    ("exits.nim", "the exit channels, called by the walker not part of it"),
    ("concolictaxonomy.nim", "the concolic taxonomy (data)")]

suite "RFC-0016 D3: codeOf reads code, not comments or strings":
  test "a # inside a string does not start a comment, and the string is dropped":
    check not codeOf("x = \"# lowerHooks.lower(\"\n").contains("lowerHooks.lower(")
    check codeOf("x = \"# a\" + y # tail\n").contains("y")
    check not codeOf("x = \"a\" # tail\n").contains("tail")
  test "block comments, single-line and multi-line, nested":
    check not codeOf("a #[ lowerHooks.lower( ]# b\n").contains("lowerHooks")
    let c = codeOf("a\n#[ x\n lowerHooks.lower(\n #[ inner ]# still\n]#\nb\n")
    check not c.contains("lowerHooks")
    check not c.contains("still")
    check c.splitLines.len == 7      # line structure is kept
    check c.contains("b")
    check not codeOf("##[ doc\nlowerHooks.lower(\n]##\nz\n").contains("lowerHooks")
    check codeOf("##[ doc ]##\nz\n").contains("z")
  test "a triple-quoted string spanning lines is dropped, a comment-like line in it too":
    let c = codeOf("a = \"\"\"\nlowerHooks.lower(\n# not a comment\n\"\"\"\nb\n")
    check not c.contains("lowerHooks")
    check c.contains("b")
    check c.splitLines.len == 6
  test "the '\"' char literal does not open a string":
    let c = codeOf("var q = '\"'\nlowerHooks.lower(x)\n")
    check c.contains("lowerHooks.lower(")
    check codeOf("c = '\\''; d = 1\n").contains("d = 1")
    check codeOf("x = 1'u8 + y\n").contains("y")
  test "a raw string's backslash escapes nothing":
    let c = codeOf("p = r\"a\\\" + lowerHooks.lower(z)\n")
    check c.contains("lowerHooks.lower(")
    check not codeOf("p = r\"a \"\" lowerHooks.lower( b\" + w\n").contains("lowerHooks")
    check codeOf("p = r\"a \"\" lowerHooks.lower( b\" + w\n").contains("w")
  test "the '#' char literal does not start a comment":
    let c = codeOf("var h = '#'; d = 1\nlowerHooks.lower(x)\n")
    check c.contains("d = 1")
    check c.contains("lowerHooks.lower(")
  test "a #[ or ##[ inside a string opens no block comment":
    let c = codeOf("s = \"#[ not a comment\"\nlowerHooks.lower(x)\nt = \"##[\"\nw\n")
    check c.contains("lowerHooks.lower(")
    check c.contains("w")
  test "a four-quote close of a triple string ends it on the last three":
    let c = codeOf("x = \"\"\"a\"\"\"\"\nlowerHooks.lower(y)\n")
    check c.contains("lowerHooks.lower(")
    check not c.contains("a\"")
    check codeOf("x = \"\"\"a \"\"\" + q\n").contains("q")
  test "an unterminated char literal swallows nothing past its line":
    check codeOf("var c = 'a\nlowerHooks.lower(x)\n").contains("lowerHooks.lower(")
    check codeOf("var c = '\\nfoo\nlowerHooks.lower(x)\n").contains("lowerHooks.lower(")
    check codeOf("var c = '\n").contains("var c")
  test "]## closes at nested depth as ]# and leaves a lone #":
    let c = codeOf("##[ a #[ b ]## c ]##\nz\n")
    check c.contains("z")
    check not c.contains("c ")
    check c.splitLines.len == 3
    let d = codeOf("#[ a #[ b ]# c ]#\nz\n")
    check d.contains("z")
    check not d.contains("c ")

suite "RFC-0016 D3: relImports reads every import form":
  test "plain, aliased, comma, bracket and from forms; comments are not imports":
    let r = relImports("import ./a\nimport ./b as bb, std/os, ./c\n" &
      "import ./[d, e as ee]\nfrom ./f import x\n# import ./g\n" &
      "import std/[os, strutils], ./h\n")
    check r == @["a", "b", "c", "d", "e", "f", "h"]

  test "a multi-line bracket group":
    check relImports("import ./[\n  a,\n  b as bb,\n  c]\nimport ./z\n") ==
      @["a", "b", "c", "z"]

  test "a multi-line comma list":
    check relImports("import ./a,\n  std/os,\n  ./b\nimport ./c\n") ==
      @["a", "b", "c"]

  test "a bare import with its list below":
    check relImports("import\n  ./a,\n  ./b\nlet x = 1\n") == @["a", "b"]

  test "import ... except yields the module":
    check relImports("import ./a except x\nimport ./b except y, z\n") ==
      @["a", "b"]

  test "an import inside a block comment or a string is not read":
    check relImports("#[\nimport ./a\n]#\nx = \"\"\"\nimport ./b\n\"\"\"\nimport ./c\n") ==
      @["c"]

suite "RFC-0016 D3: definedNames sees enum members and every declared name":
  # R2-5: the scanner used to record the first name after a column-0 keyword
  # and nothing else, so `heapPinned` (an "exact set") could not see an enum
  # member or the second name of `var a, b`.
  test "an inline enum's members are defined names":
    let d = definedNames("type GuardLiteral = enum glOpen, glTrue, glFalse\n")
    check d == toHashSet(["GuardLiteral", "glOpen", "glTrue", "glFalse"])

  test "a multi-line enum's members, with doc comments, values and a block":
    let d = definedNames("""
type
  CapKind = enum
    ## doc
    ckNone                ## not a cap
    ckFrontier, ckDepth   ## two on a line
    ckValued = 5

  Other = object
    field: int
type Pol* = enum
  polPos,
  polNeg
proc after()
""")
    for n in ["CapKind", "ckNone", "ckFrontier", "ckDepth", "ckValued",
              "Other", "Pol", "polPos", "polNeg", "after"]:
      checkpoint n
      check n in d
    check "field" notin d
    check "doc" notin d

  test "multi-name var/let/const record every name, pragmas included":
    let d = definedNames("""
var a, b: int
const c*, e = 1
let f {.used.}, g = 2
var h {.threadvar.}: int
type Pair[T, U] = object
  x: int
""")
    for n in ["a", "b", "c", "e", "f", "g", "h", "Pair"]:
      checkpoint n
      check n in d
    check "U" notin d
    check "x" notin d

suite "RFC-0016 D3: the include surface":
  let rt = readSmt("runtime.nim")

  test "the include list and its order are exact":
    var got: seq[string]
    for l in rt.splitLines:
      if l.startsWith("include "):
        let a = l.find('"')
        let b = l.find('"', a + 1)
        got.add l[a + 1 ..< b]
    check got == @expectedIncludes

  test "no remaining include has an import":
    for f in expectedIncludes:
      for l in readSmt(f).splitLines:
        let t = l.strip()
        check not (t.startsWith("import ") or t.startsWith("from ") or
                   t.startsWith("export "))

  test "the shared runtime-family list names every runtime*.nim and every leaf":
    ## The source audits read `runtimeFamilyFiles` (tests/audit_scan_utils.nim)
    ## instead of their own file lists, so a file move cannot break four
    ## audits at once. This is what keeps the list whole.
    var listed: HashSet[string]
    for f in runtimeFamilyFiles: listed.incl f
    for p in walkFiles(smt / "runtime*.nim"):
      checkpoint p
      check extractFilename(p) in listed
    for f in runtimeFamilyFiles:
      check fileExists(smt / f)

  test "every smt module the walker imports is in the family or reasoned out":
    # L1 (R2-5, R3-5): the expected leaf set is DERIVED from the `./` imports
    # of every family file (to a fixpoint), not kept by hand. A newly imported
    # module is either a family member (it holds walker sites a source audit
    # must read) or is named, with a reason, in `noWalkerSites`.
    let imported = familyImports()
    var listed, reasoned: HashSet[string]
    for f in runtimeFamilyFiles: listed.incl f
    for (f, why) in noWalkerSites:
      checkpoint f & ": " & why
      check why.len > 0
      check f notin listed          # not both
      check f in imported           # no stale entry
      check fileExists(smt / f)
      reasoned.incl f
    for f in imported:
      checkpoint f
      check f in listed or f in reasoned
    # and the family's leaves are all reachable from those imports (the
    # `runtime*.nim` includes/modules are covered by the glob test above)
    for f in listed:
      checkpoint f
      check f in imported or f.startsWith("runtime")

  test "a module is imported, never included, and names no runtime symbol":
    let priv = definedNames(rt)
    for f in movedToModules:
      checkpoint f
      let m = f[0 ..< f.len - 4]
      check not rt.contains("include \"" & f & "\"")
      # INT-34 B4: `lowerFloatArm` and `lowerExnArm` are called by `lower`
      # only, so `lower_expr.nim` imports those two, not `runtime.nim`
      check rt.contains("\nimport ./" & m) or
            readSmt("lower_expr.nim").contains("\nimport ./" & m)
      let text = readSmt(f)
      check text.contains("\nimport ./symval")
      let named = referenced(viaHooks(text),
                             priv - definedNames(text) - boundHere(text))
      checkpoint $named
      check named.len == 0

  test "the heap include references exactly the pinned runtime.nim names":
    # D3c-8: the walker arm stays an include (see the header of
    # `runtime_heap.nim`). Its surface is an EXACT set, not a ceiling: a new
    # name fails (add it to `heapPinned` only after deciding it belongs), and
    # a removed one fails too (shrink the list).
    # RFC-0016 INT-34 B2: the walker's types moved to `walk_types.nim`, which
    # `runtime.nim` imports; to the include they are still names of the
    # runtime unit, so the pinned set did not change with the move. INT-34
    # B3: likewise the routines that moved to `walk_path.nim`, and B4 the
    # names that moved to `lower_expr.nim` (`callGuardedNames`,
    # `entryValueOf`, `storeSeqElem`, ...), and B5 those that moved to
    # `walk_solve.nim` (`currentVariantHeaps`, `ptrSelKey`, ...), and B6a
    # those that moved to `walk_ctx.nim` (`exact`, `heapInputName`, ...), and
    # B6b those that moved to `walk_expr.nim` (`forkDefect`, `liveFrame`,
    # ...): the include reaches them through `runtime.nim`'s import.
    let priv = definedNames(rt) + definedNames(readSmt("walk_types.nim")) +
               definedNames(readSmt("walk_path.nim")) +
               definedNames(readSmt("lower_expr.nim")) +
               definedNames(readSmt("walk_solve.nim")) +
               definedNames(readSmt("walk_ctx.nim")) +
               definedNames(readSmt("walk_expr.nim"))
    let text = readSmt("runtime_heap.nim")
    let got = referenced(text, priv - definedNames(text))
    var pinned: HashSet[string]
    for n in heapPinned: pinned.incl n
    check pinned.len == heapPinned.len   # no duplicate in the list
    let added = got - pinned
    let gone = pinned - got
    checkpoint "new names the heap include now references: " & $added
    checkpoint "pinned names it no longer references (shrink heapPinned): " &
               $gone
    check added.len == 0
    check gone.len == 0

  test "no forward declaration of a heap_model or z3check proc is left":
    check not rt.contains("proc allocRefSort*(")
    let rtDefs = definedNames(rt)
    for f in ["heap_model.nim", "z3check.nim"]:
      for n in definedNames(readSmt(f)):
        if n in perModuleNames: continue
        # a field or parameter line of a block may share a name; only a
        # top-level proc/func/template/iterator declaration is a forward decl
        for kw in ["proc ", "func ", "template ", "iterator "]:
          checkpoint f & " " & n
          check not (rt.contains("\n" & kw & n & "(") or
                     rt.contains("\n" & kw & n & "*(") or
                     rt.contains("\n" & kw & n & "["))

suite "RFC-0016 D3c-1: the symval leaf":
  test "symval.nim imports only the allowed leaves":
    let sv = readSmt("symval.nim")
    var seen: seq[string]
    for l in codeOf(sv).splitLines:
      let t = l.strip()
      if t.startsWith("import "):
        for m in t[7 .. ^1].split(','):
          var s = m.strip()
          let k = s.find(" as ")
          if k >= 0: s = s[0 ..< k]
          seen.add s
      elif t.startsWith("from "):
        seen.add t.splitWhitespace[1]
    checkpoint $seen
    for s in seen: check s in symvalAllowed
    check "./types" in seen

  test "runtime.nim defines none of the moved names":
    let defs = definedNames(readSmt("runtime.nim"))
    for n in movedNames:
      checkpoint n
      check n notin defs

  test "every threadvar of symval.nim is reset by resetLoweringSink":
    let sv = readSmt("symval.nim")
    let at = sv.find("proc resetLoweringSink*()")
    check at >= 0
    let resetBody = sv[at .. ^1]
    var tvs: seq[string]
    for l in sv.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    check tvs.len == 3   # + RFC-0016 CRH-07 rawKeep; INT-34: one lowering queue (`pending`)
    for n in tvs:
      checkpoint n
      check resetBody.contains("\n  " & n & " = ")

  test "resetSymexRunState calls resetLoweringSink":
    let rt = readSmt("runtime.nim")
    let at = rt.find("proc resetSymexRunState(")
    check at >= 0
    check rt[at .. ^1].contains("\n  resetLoweringSink()")

const
  ## What slice D3c-2 moved into `walk_state.nim`.
  wsAllowed = ["std/tables", "std/options", "z3", "./types", "./symval",
               "./definedness", "./errorkind", "./pcre_syntax",
               "../thread_state"]  ## S8ck-r: the Z3-free per-thread release leaf

  wsMoved = [
    "currentWalkCtxPtr", "currentRefSorts", "currentNilConsts",
    "currentMaxSplitParts", "currentInFlightTypeId", "currentInFlightMsg",
    "currentExnRefCounter", "lastGetCurrentExnRef", "currentClosureSyms",
    "currentClosureBodies", "currentDistinctSorts",
    "regexRecDefConds", "regexRecFactConds",
    "regexPointSites", "regexLimitSites", "stripDecompConds",
    "stripSynthCounter", "DistinctSortEntry", "ConvBound", "ArithTrap",
    "ParseIntRaise", "ClosureSymKey", "ClosureBody", "RegexPointSite",
    "RegexLimitSite", "RaiseSinkKind", "LowerSinks", "LowerHooks", "degradeSymCounter",
    "freshDegradeName", "convBoundOf"]

  syncProcs = [
    "syncRefSortEntry", "syncDistinctSortEntry", "syncClosureSymEntry",
    "syncClosureBodyEntry", "syncFreshnessCapHint",
    "syncDistinctBijectivityHint", "syncRangeDefectCond",
    "syncExtractionError", "syncClosureCallError",
    "syncConvFloatToIntBoundCond", "syncParseIntRaiseCond",
    "syncDivByZeroCond", "syncOverflowCond", "syncStrIndexOobCond",
    "syncSeqOobCond", "syncRegexRaiseMsg", "syncUninitReadCond",
    "syncArithTrapCond"]

suite "RFC-0016 D3c-2: the walk_state leaf":
  test "walk_state.nim imports only the allowed leaves":
    let ws = readSmt("walk_state.nim")
    var seen: seq[string]
    for l in codeOf(ws).splitLines:
      let t = l.strip()
      if t.startsWith("import "):
        for m in t[7 .. ^1].split(','):
          var s = m.strip()
          let k = s.find(" as ")
          if k >= 0: s = s[0 ..< k]
          seen.add s
      elif t.startsWith("from "):
        seen.add t.splitWhitespace[1]
    checkpoint $seen
    for s in seen: check s in wsAllowed
    check "./symval" in seen

  test "runtime.nim defines none of the moved names":
    let defs = definedNames(readSmt("runtime.nim"))
    for n in wsMoved:
      checkpoint n
      check n notin defs

  test "every threadvar of walk_state.nim is reset by resetWalkState":
    let ws = readSmt("walk_state.nim")
    let at = ws.find("proc resetWalkState*(")
    check at >= 0
    let resetBody = ws[at .. ^1]
    var tvs: seq[string]
    for l in ws.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    check tvs.len == 19   # RFC-0016 K9e: the raise sinks live in LowerSinks only
    for n in tvs:
      checkpoint n
      check resetBody.contains("\n  " & n & " = ")

  test "a raise sink has one store: its LowerSinks field, no threadvar (K9e)":
    # Every drain takes the walk's own `WalkCtx` and reads `w.sinks`; a
    # threadvar of the same name was a mirror no reader could reach.
    let ws = readSmt("walk_state.nim")
    let at = ws.find("type LowerSinks* = object")
    check at >= 0
    var fields: seq[string]
    for l in ws[at .. ^1].splitLines()[1 .. ^1]:
      if l.len > 0 and not l.startsWith(" "): break
      if l.startsWith("  ") and not l.startsWith("   ") and
         ("Conds*: seq[" in l or "Msgs*: seq[" in l):
        fields.add leadIdent(l.strip())
    checkpoint $fields
    check fields.len == 10
    for p in walkFiles(smt / "*.nim"):
      for l in codeOf(readFile(p)).splitLines():
        if l.startsWith("var ") and "{.threadvar.}" in l:
          checkpoint extractFilename(p) & ": " & l
          check leadIdent(l[4 .. ^1]) notin fields

  test "resetSymexRunState calls resetWalkState":
    let rt = readSmt("runtime.nim")
    let at = rt.find("proc resetSymexRunState(")
    check at >= 0
    check rt[at .. ^1].contains("\n  resetWalkState(")

  test "the sync* forward declarations are gone, the bodies live in the leaf":
    let rt = readSmt("runtime.nim")
    let ws = readSmt("walk_state.nim")
    let rtDefs = definedNames(rt)
    let wsDefs = definedNames(ws)
    for n in syncProcs:
      checkpoint n
      check n notin rtDefs
      check n in wsDefs
      # the body appends on the sinks pointer, not by casting the walk pointer
      let at = ws.find("proc " & n & "*(")
      check at >= 0
      let e = ws.find("\nproc ", at + 1)
      let body = ws[at ..< (if e < 0: ws.len else: e)]
      check "currentLowerSinks" in body
      check "WalkCtx" notin body

  test "WalkCtx embeds the sinks and sets the pointer where it sets the walk":
    let rt = readSmt("runtime.nim")
    # RFC-0016 INT-34 B2: `WalkCtx` is declared in `walk_types.nim`
    check readSmt("walk_types.nim").contains("    sinks*:     LowerSinks")
    var sets, clears, setSinks, clearSinks = 0
    for l in rt.splitLines:
      let t = l.strip()
      if t.startsWith("currentWalkCtxPtr = addr w"): inc sets
      if t.startsWith("currentWalkCtxPtr = nil"): inc clears
      if t.startsWith("currentLowerSinks = addr w.sinks"): inc setSinks
      if t.startsWith("currentLowerSinks = nil"): inc clearSinks
    check sets >= 3
    check setSinks == sets
    check clearSinks == clears

  test "the lower hooks are declared and a module is live through them":
    let ws = readSmt("walk_state.nim")
    var callers = ""   # every smt/ module but runtime.nim and the table itself
    for p in walkFiles(smt / "*.nim"):
      let f = extractFilename(p)
      if f notin ["runtime.nim", "walk_state.nim"]:
        callers.add codeOf(readFile(p))   # a comment is not a caller
    for h in ["lower", "lowerClosureCall",
              "currentFrameId", "registerCapCell", "depositStrIndexOob"]:
      checkpoint h
      check ws.contains("\n  " & h & "*: proc(")
      # a field no module outside runtime.nim calls is dead: delete it
      check callers.contains("lowerHooks." & h & "(")
    for h in ["storeSeqElem", "sameSymVal", "entryValueOf", "iteSV",
              "allocateSym", "seqElemAt"]:
      check not ws.contains("\n  " & h & "*: proc(")
    check not ws.contains("sortOfTuple*:")   # D3c-6: read directly from heap_model
    check codeOf(readSmt("runtime_floats.nim")).contains("lowerHooks.lower(")
    check codeOf(readSmt("runtime_closures.nim")).contains(
      "lowerHooks.lowerClosureCall(")
    check readSmt("runtime.nim").contains("\nlowerHooks = LowerHooks(")

  test "a commented-out hook call is not a caller (self-test)":
    let src = "proc a() =\n  # lowerHooks.lower(env, e, p)\n  discard\n" &
              "  ## lowerHooks.registerCapCell(x, v)\n  discard 1 # lowerHooks.currentFrameId()\n"
    for h in ["lower", "registerCapCell", "currentFrameId"]:
      check not codeOf(src).contains("lowerHooks." & h & "(")
    check codeOf("  lowerHooks.lower(env, e, p)\n").contains("lowerHooks.lower(")

  test "the lowerHooks init assigns every declared field and no other":
    # R3-4: a field the init leaves nil is a nil-call at the first hook use.
    var declared, assigned: HashSet[string]
    var probe: LowerHooks
    for name, _ in fieldPairs(probe): declared.incl name
    let rt = readSmt("runtime.nim")
    let i = rt.find("\nlowerHooks = LowerHooks(")
    check i >= 0
    var j = rt.find('(', i)
    let start = j + 1
    var depth = 1
    inc j
    while j < rt.len and depth > 0:
      if rt[j] == '(': inc depth
      elif rt[j] == ')': dec depth
      inc j
    var item = ""
    var d = 0
    for c in codeOf(rt[start ..< j - 1]):
      if c in {'(', '['}: inc d
      elif c in {')', ']'}: dec d
      if c == ',' and d == 0:
        let k = item.find(":")
        if k > 0: assigned.incl item[0 ..< k].strip()
        item = ""
      else: item.add c
    let k = item.find(":")
    if k > 0: assigned.incl item[0 ..< k].strip()
    checkpoint $declared & " vs " & $assigned
    check declared.len >= 5
    check declared == assigned

proc importsOf(text: string): seq[string] =
  for l in codeOf(text).splitLines:
    let t = l.strip()
    if t.startsWith("import "):
      for m in t[7 .. ^1].split(','):
        var s = m.strip()
        let k = s.find(" as ")
        if k >= 0: s = s[0 ..< k]
        result.add s
    elif t.startsWith("from "):
      result.add t.splitWhitespace[1]

suite "RFC-0016 D3c-6: the heap_model and z3check leaves":
  test "heap_model.nim imports only leaves":
    let seen = importsOf(readSmt("heap_model.nim"))
    checkpoint $seen
    for s in seen: check s in hmAllowed
    check "./symval" in seen and "./walk_state" in seen and "./z3check" in seen

  test "z3check.nim imports only leaves":
    let seen = importsOf(readSmt("z3check.nim"))
    checkpoint $seen
    for s in seen: check s in zcAllowed

  test "runtime.nim imports both and includes neither":
    let rt = readSmt("runtime.nim")
    for m in ["heap_model", "z3check"]:
      check rt.contains("\nimport ./" & m)
      check not rt.contains("include \"" & m & ".nim\"")

  test "heap_model and z3check name no runtime.nim symbol":
    let priv = definedNames(readSmt("runtime.nim"))
    for f in ["heap_model.nim", "z3check.nim"]:
      checkpoint f
      let text = readSmt(f)
      var allowed = definedNames(text) + boundHere(text)
      let named = referenced(viaHooks(text), priv - allowed)
      checkpoint $named
      check named.len == 0

  test "runtime.nim defines none of the names that moved":
    let rtDefs = definedNames(readSmt("runtime.nim"))
    let hp = definedNames(readSmt("runtime_heap.nim"))
    for f in ["heap_model.nim", "z3check.nim"]:
      for n in definedNames(readSmt(f)):
        if n in perModuleNames: continue
        checkpoint f & " " & n
        check n notin rtDefs
        check n notin hp

  test "every run-state threadvar of heap_model.nim is reset by resetHeapModel":
    let hm = readSmt("heap_model.nim")
    let at = hm.find("proc resetHeapModel*(")
    check at >= 0
    let resetBody = hm[at .. ^1]
    var tvs: seq[string]
    for l in hm.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    check tvs.len == 39   # RFC-0016 INT-82: +4 (provenance); INT-81: +1 (field owners);
                          # INT-83: +5 (pointer facts, views, sorts, read sorts,
                          # decls); INT-84: +2 (input domain, holes made);
                          # INT-85: +1 (made-value decl kinds, process-stable);
                          # INT-90: +7 (sort types, facts, fact ids, desync,
                          # facts off, accessed, written); INT-93: +3 (frame
                          # object ids, frame cells, frame pointers)
                          # int6-f: +1 (unionImageProgram, reset per run)
    for n in tvs:
      checkpoint n
      if n in hmProcessStable:
        check not resetBody.contains("\n  " & n & " = ")
      else:
        check resetBody.contains("\n  " & n & " = ")

  test "resetSymexRunState calls resetHeapModel":
    let rt = readSmt("runtime.nim")
    let at = rt.find("proc resetSymexRunState(")
    check at >= 0
    check rt[at .. ^1].contains("\n  resetHeapModel()")

  test "the heap include keeps the walker arm, not the algebra":
    let hp = readSmt("runtime_heap.nim")
    for n in ["walkHeapArm", "nilDerefFork", "freshRef", "assertFreshness"]:
      check hp.contains("\nproc " & n)
    for n in ["heapSelect", "svLeafAsts", "mkHeapArrayVar", "svCellWf"]:
      check not hp.contains("\nproc " & n)

const
  ## D3c-7: what `string_lower_support.nim` may import, and the names that
  ## moved into it, `symval.nim` and `z3check.nim`.
  slsAllowed = ["std/tables", "std/options", "std/sets", "std/algorithm",
                "std/strutils", "z3", "./types",
                "./z3check",        ## K9e: the sort-checked builders (S8m audit)
                "../thread_state"]  ## S8ck-r: the Z3-free per-thread release leaf
  strAllowed = ["std/tables", "std/options", "std/sets", "std/strutils", "z3",
                "./types", "./abstraction", "./symval", "./walk_state",
                "./z3check", "./heap_model", "./string_lower_support",
                "./regex_parser", "./pcre_select", "./pcre_engine",
                "./pcre_syntax", "./errorkind", "./stdlib_rows",
                "../thread_state"]  ## S8ck-r: the Z3-free per-thread release leaf
  d3c7Moved = ["literalStringBytes", "IndexSplit", "indexSplits",
               "indexSplitOf", "indexSplitCounter", "splitNeedle",
               "literalLen", "NotInForm", "notInForm", "NotIn",
               "indexSplitAxioms", "indexSplitChain", "indexSplitLastLink",
               "lowerIndexSplit", "registeredIndexSplit", "indexSplitRoots",
               "lambdaOver", "mkSeqSV"]

suite "RFC-0016 D3c-7: the strings module and string_lower_support leaf":
  test "string_lower_support.nim and runtime_strings.nim import only leaves":
    let sls = importsOf(readSmt("string_lower_support.nim"))
    checkpoint $sls
    for s in sls: check s in slsAllowed
    let str = importsOf(readSmt("runtime_strings.nim"))
    checkpoint $str
    for s in str: check s in strAllowed
    check "./string_lower_support" in str and "./symval" in str

  test "string_lower_support names no runtime.nim symbol":
    let priv = definedNames(readSmt("runtime.nim"))
    let text = readSmt("string_lower_support.nim")
    let named = referenced(viaHooks(text),
                           priv - definedNames(text) - boundHere(text))
    checkpoint $named
    check named.len == 0

  test "runtime.nim imports string_lower_support and defines none of its names":
    let rt = readSmt("runtime.nim")
    check rt.contains("\nimport ./string_lower_support")
    check not rt.contains("\nexport string_lower_support")   # R2-3: not facade API
    let defs = definedNames(rt)
    for n in d3c7Moved:
      checkpoint n
      check n notin defs
    for n in definedNames(readSmt("string_lower_support.nim")):
      if n in perModuleNames: continue
      checkpoint n
      check n notin defs

  test "every run-state threadvar of the string leaves is reset":
    let sls = readSmt("string_lower_support.nim")
    let at = sls.find("proc resetStringSupport*(")
    check at >= 0
    let body = sls[at .. ^1]
    var tvs: seq[string]
    for l in sls.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    # the test hook and the linked-Z3 probe are the same in every run
    # 5 -> 6, RFC-0016 INT-57: `intRenders`, the run's registered integer
    # renderings. It holds Z3 terms of the run's context, so it is one the
    # per-run reset must clear, and the loop below checks that it does.
    check tvs.len == 6
    for n in tvs:
      checkpoint n
      if n in ["notInFormOverride", "linkedNotInForm"]:
        check not body.contains("\n  " & n & " = ")
      else:
        check body.contains("\n  " & n & " = ")
    # `runtime_strings.nim`: strCharsCounter is reset; `regexReachCache` is a
    # pure function of the pattern text (no Z3 term) and stays
    let st = readSmt("runtime_strings.nim")
    let at2 = st.find("proc resetStringLowering*(")
    check at2 >= 0
    var tvs2: seq[string]
    for l in st.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs2.add leadIdent(l[4 .. ^1])
    check tvs2 == @["strCharsCounter", "regexReachCache"]
    check st[at2 .. ^1].contains("\n  strCharsCounter = 0")
    let rt = readSmt("runtime.nim")
    let ar = rt.find("proc resetSymexRunState(")
    check ar >= 0
    check rt[ar .. ^1].contains("\n  resetStringSupport()")
    check rt[ar .. ^1].contains("\n  resetStringLowering()")

const
  ## RFC-0016 INT-34 B2. What `walk_types.nim` may import: std, `z3`, and the
  ## leaves its field types come from (no module with walk code).
  wtAllowed = ["std/tables", "std/options", "std/sets", "z3", "./types",
               "./symval", "./walk_state", "./exits", "./concolictaxonomy"]
  ## A sample of what B2 moved out of `runtime.nim`; the test below checks
  ## every name `walk_types.nim` defines, this list keeps the intent legible.
  wtMoved = ["Path", "Degrade", "Survivors", "CapKind", "DegradeSink",
             "RawWitness", "RawResult", "SatCandidate", "LoopFrame",
             "CallFrame", "CallFrameCtx", "WalkCtx", "LoopExits",
             "PendingLowerEffects", "forEachExitGroup",
             "collectExitGroupFields"]

proc exportedFieldNames(text: string): HashSet[string] =
  ## The field names an object body declares exported (`  name*: T`,
  ## `  a*, b*: T`, `  case kind*: K`): a field shares its name with a
  ## `runtime.nim` threadvar it mirrors (`WalkCtx.heapDepthErrors`) without
  ## naming it.
  for raw in codeOf(text).splitLines:
    var t = raw.strip()
    if raw.len == 0 or raw[0] != ' ': continue
    if t.startsWith("case "): t = t[5 .. ^1]
    let colon = t.find(':')
    if colon <= 0: continue
    for w in t[0 ..< colon].split(','):
      let n = w.strip()
      if n.len > 1 and n[^1] == '*':
        let id = leadIdent(n[0 ..< n.len - 1])
        if id.len == n.len - 1: result.incl id

suite "RFC-0016 INT-34 B2: the walk_types leaf":
  test "walk_types.nim imports only the allowed leaves":
    let seen = importsOf(readSmt("walk_types.nim"))
    checkpoint $seen
    for s in seen: check s in wtAllowed
    check "./symval" in seen and "./walk_state" in seen

  test "walk_types.nim resets every threadvar it owns (it owns none)":
    # Types only: a threadvar added here holds run state, which belongs in
    # `walk_state.nim` with its reset. Owning one fails until this test names
    # the proc that resets it.
    var tvs: seq[string]
    for l in readSmt("walk_types.nim").splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    checkpoint $tvs
    check tvs.len == 0

  test "walk_types names no runtime.nim symbol":
    let priv = definedNames(readSmt("runtime.nim"))
    let text = readSmt("walk_types.nim")
    let named = referenced(viaHooks(text),
                           priv - definedNames(text) - boundHere(text) -
                             exportedFieldNames(text))
    checkpoint $named
    check named.len == 0

  test "runtime.nim imports walk_types, re-exports names not the module, and defines none of its names":
    let rt = readSmt("runtime.nim")
    check rt.contains("\nimport ./walk_types")
    # the public surface is kept by `export walk_types.<name>`; a whole-module
    # export would publish every walker type (`WalkCtx`, `Path`, `Degrade`)
    check not rt.contains("\nexport walk_types\n")
    check not rt.contains("\nexport walk_types except")
    let defs = definedNames(rt)
    let wt = definedNames(readSmt("walk_types.nim"))
    for n in wtMoved:
      checkpoint n
      check n in wt
    for n in wt:
      if n in perModuleNames: continue
      checkpoint n
      check n notin defs

const
  ## RFC-0016 INT-34 B3. What `walk_path.nim` may import: std, `z3`, and the
  ## leaves below it (no module with walk code above the value core).
  wpAllowed = ["std/tables", "std/options", "z3", "./types", "./symval",
               "./walk_state", "./walk_types", "./heap_model", "./z3check"]
  ## A sample of what B3 moved out of `runtime.nim`; the test below checks
  ## every name `walk_path.nim` defines, this list keeps the intent legible.
  wpMoved = ["forkPathTaintPrimitive", "forkPath", "forkPathTainted",
             "forkPathMerged", "deepCopyHeapState", "taintInPlace",
             "cellValue", "tabValAt", "tabMoreEq", "containerCardConds",
             "probeProto", "unwrittenResultZero", "h1ForkIsolation"]
  ## The routines `runtime.nim` exported before the move: re-exported by
  ## name, and no other.
  wpPublic = ["h1PathHasHeapFields", "h1ForkIsolation",
              "seedCallerHeapInWalkCtx", "isFollowConcreteWalk", "svWithRaw",
              "c1ClosurePoCApply"]

suite "RFC-0016 INT-34 B3: the walk_path leaf":
  test "walk_path.nim imports only the allowed leaves":
    let seen = importsOf(readSmt("walk_path.nim"))
    checkpoint $seen
    for s in seen: check s in wpAllowed
    check "./walk_types" in seen and "./walk_state" in seen

  test "walk_path.nim resets every threadvar it owns (it owns none)":
    # R0's threadvars stayed in `runtime.nim` with the routines that read
    # them. Owning one fails until this test names the proc that resets it
    # (called from `resetSymexRunState`) and its thread-state release.
    var tvs: seq[string]
    for l in readSmt("walk_path.nim").splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    checkpoint $tvs
    check tvs.len == 0

  test "walk_path names no runtime.nim symbol":
    let priv = definedNames(readSmt("runtime.nim"))
    let text = readSmt("walk_path.nim")
    let named = referenced(viaHooks(text),
                           priv - definedNames(text) - boundHere(text))
    checkpoint $named
    check named.len == 0

  test "noteUbAtFork is reached through walk_path's typed hook, its empty test inline":
    let text = codeOf(readSmt("walk_path.nim"))
    check text.count("pathHooks.noteUbAtFork(") == 2
    check text.count("lowerHooks.") == 0
    check text.count("if newUb != {}:") == 2
    # the typed hook is declared in walk_path, and walk_state holds no copy
    check text.contains("\ntype PathHooks* = object")
    check text.contains("\n  noteUbAtFork*: proc(")
    check text.contains("\nvar pathHooks*: PathHooks")
    check not codeOf(readSmt("walk_state.nim")).contains("noteUbAtFork")
    # runtime fills it once beside `lowerHooks`, with the proc itself: no
    # adapter and no pointer cast
    let rt = codeOf(readSmt("runtime.nim"))
    check rt.count("pathHooks = PathHooks(noteUbAtFork: noteUbAtFork)") == 1
    check not rt.contains("noteUbAtForkHook")
    check not rt.contains("cast[Path]")
    # the body is R4's, in `walk_expr.nim` since INT-34 B6b (still above
    # runtime.nim, which fills the hook with it), with no forward declaration
    check readSmt("walk_expr.nim").count("\nproc noteUbAtFork*(") == 1
    check not readSmt("runtime.nim").contains("\nproc noteUbAtFork")

  test "runtime.nim imports walk_path, re-exports names not the module, and defines none of its names":
    let rt = readSmt("runtime.nim")
    check rt.contains("\nimport ./walk_path")
    check not rt.contains("\nexport walk_path\n")
    check not rt.contains("\nexport walk_path except")
    var exported, want: HashSet[string]
    for l in codeOf(rt).splitLines:
      for w in l.split({' ', ','}):
        if w.startsWith("walk_path."): exported.incl w["walk_path.".len .. ^1]
    for n in wpPublic: want.incl n
    checkpoint $exported
    check exported == want
    let defs = definedNames(rt)
    let wp = definedNames(readSmt("walk_path.nim"))
    for n in wpMoved:
      checkpoint n
      check n in wp
    for n in wp:
      if n in perModuleNames: continue
      checkpoint n
      check n notin defs

const
  ## RFC-0016 INT-34 B4. What `lower_expr.nim` may import: std, `z3`, and the
  ## leaves below it (the value core, the walk state and types, the path
  ## leaf, the heap algebra, and the lowering arms that were includes).
  leAllowed = ["std/tables", "std/options", "std/typetraits", "std/sets",
               "std/hashes", "std/algorithm", "std/math", "std/strutils",
               "z3", "./buildprofile", "./types", "./admission",
               "./arith_regime", "./definedness", "./variant_layout",
               "./abstraction", "./symval", "./walk_state", "./walk_types",
               "./walk_path", "./stdlib_rows", "./runtime_floats",
               "./runtime_exceptions", "./z3check", "./heap_model",
               "./string_lower_support", "./runtime_strings",
               "./runtime_closures", "../thread_state"]
  ## A sample of what B4 moved out of `runtime.nim`; the test below checks
  ## every name `lower_expr.nim` defines, this list keeps the intent legible.
  leMoved = ["lower", "lowerExpr", "lowerBool", "lowerArith", "lowerSeqLit",
             "lowerTupleLit", "lowerVariantLit", "storeSeqElem",
             "entryValueOf", "globalInitValue", "degradeStrArm",
             "checkedNow", "resetArith", "pendingEnvWriteIx",
             "closureEnvWrites", "arithFrames", "obligationLog"]
  ## The names `runtime.nim` exported before the move: re-exported by name,
  ## and no other.
  lePublic = ["obligationLog", "sliceViewCounter", "variantLitFreshCounter",
              "variantConstructSymFreshCounter", "walkerWorkUnits",
              "walkerTermUnits", "walkerContextUnits", "arrayAccessTooWide",
              "bsCard", "reconcileFloat", "symbolicPositions", "termDepth",
              "termTooDeep"]
  ## Threadvars `resetLowerExprState` leaves alone: the thread's running
  ## work total, and the linked Z3's decl kinds (probed once per thread).
  leNotPerRun = ["walkerWorkUnits", "uninitArrKinds", "bvIvlDeclKinds"]
  ## Reset by `resetArith`, which `resetLowerExprState` calls.
  leViaResetArith = ["arithFrames", "checkScopes"]

suite "RFC-0016 INT-34 B4: the lower_expr leaf":
  let le = readSmt("lower_expr.nim")

  test "lower_expr.nim imports only the allowed leaves":
    let seen = importsOf(le)
    checkpoint $seen
    for s in seen: check s in leAllowed
    check "./walk_path" in seen and "./walk_types" in seen

  test "every threadvar of lower_expr.nim is reset by resetLowerExprState or named":
    let at = le.find("proc resetLowerExprState*(")
    check at >= 0
    let resetBody = le[at .. ^1]
    let ra = le.find("proc resetArith*(")
    check ra >= 0
    let arithBody = le[ra .. ^1]
    check resetBody.contains("\n  resetArith()")
    var tvs: seq[string]
    for l in le.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    check tvs.len == 30   # 5 from R0, 25 from R1 (`injectedShape` sits in a `when`)
    for n in tvs:
      checkpoint n
      if n in leNotPerRun:
        check not resetBody.contains("\n  " & n & " = ")
      elif n in leViaResetArith:
        check arithBody.contains("\n  " & n & " = ")
      else:
        check resetBody.contains("\n  " & n & " = ") or
              resetBody.contains("\n  " & n & ".clear()")
    # the S8ce injection threadvar sits in a `when` block
    check resetBody.contains("\n    injectedShape = \"\"")

  test "every threadvar of lower_expr.nim is released when its thread exits":
    let at = le.find("proc releaseThreadState()")
    check at >= 0
    let body = le[at .. ^1]
    check le.contains("\nregisterThreadStateRelease(releaseThreadState)")
    for l in le.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        let n = leadIdent(l[4 .. ^1])
        checkpoint n
        check body.contains(n)
    check body.contains("releaseToDefault(injectedShape)")

  test "resetSymexRunState calls resetLowerExprState":
    let rt = readSmt("runtime.nim")
    let at = rt.find("proc resetSymexRunState(")
    check at >= 0
    check rt[at .. ^1].contains("\n  resetLowerExprState()")
    check not rt.contains("\n  resetArith()")

  test "lower_expr names no runtime.nim symbol":
    let priv = definedNames(readSmt("runtime.nim"))
    let named = referenced(viaHooks(le),
                           priv - definedNames(le) - boundHere(le))
    checkpoint $named
    check named.len == 0

  test "lowerHofCall is reached through lower_expr's typed hook":
    let text = codeOf(le)
    check text.count("lowerExprHooks.lowerHofCall(") == 1
    check text.contains("\ntype LowerExprHooks* = object")
    check text.contains("\n  lowerHofCall*: proc(")
    check text.contains("\nvar lowerExprHooks*: LowerExprHooks")
    # runtime fills it once beside `lowerHooks`, with the proc itself
    let rt = codeOf(readSmt("runtime.nim"))
    check rt.count("lowerExprHooks = LowerExprHooks(lowerHofCall: lowerHofCall)") == 1
    # the body stays in runtime.nim (R7), with no forward declaration
    check readSmt("runtime.nim").count("\nproc lowerHofCall(") == 1

  test "runtime.nim imports lower_expr, re-exports names not the module, and defines none of its names":
    let rt = readSmt("runtime.nim")
    check rt.contains("\nimport ./lower_expr")
    check not rt.contains("\nexport lower_expr\n")
    check not rt.contains("\nexport lower_expr except")
    var exported, want: HashSet[string]
    for l in codeOf(rt).splitLines:
      for w in l.split({' ', ','}):
        if w.startsWith("lower_expr."): exported.incl w["lower_expr.".len .. ^1]
    for n in lePublic: want.incl n
    checkpoint $exported
    check exported == want
    let defs = definedNames(rt)
    let ld = definedNames(le)
    for n in leMoved:
      checkpoint n
      check n in ld
    for n in ld:
      if n in perModuleNames: continue
      checkpoint n
      check n notin defs

const
  ## RFC-0016 INT-34 B5. What `walk_solve.nim` may import: std, `z3`, and the
  ## leaves below it (the value core, the walk state and types, the path and
  ## lowering leaves, the heap algebra, the string support and the regex
  ## parser the point check reads).
  slvAllowed = ["std/tables", "std/options", "std/sets", "std/hashes",
               "std/algorithm", "std/math", "std/monotimes", "std/strutils",
               "std/importutils", "std/exitprocs", ## the query-stats summary
               "z3", "./walk_log", "./types",
               "./abstraction", "./symval", "./walk_state", "./walk_types",
               "./walk_path", "./lower_expr", "./regex_parser", "./z3check",
               "./heap_model", "./string_lower_support", "./runtime_strings",
               "../thread_state"]
  ## A sample of what B5 moved out of `runtime.nim`; the test below checks
  ## every name `walk_solve.nim` defines, this list keeps the intent legible.
  slvMoved = ["trySolve", "pathInfeasible", "pathRoots", "globalRoots",
             "extractWitness", "modelPins", "buildHeapSnapshot",
             "checkCapped", "checkExact", "querySolver", "ptrSelKey",
             "ptrIdxKey", "ptrKeyKey", "ptrObjKey", "ptrTargetCode",
             "loopArmInfeasible", "satModels", "walkWorkExhausted",
             "currentVariantHeaps", "currentClosureCallAxioms"]
  ## The names `runtime.nim` exported before the move: re-exported by name,
  ## and no other (the last ten under `-d:symexQueryStats` only).
  slvPublic = ["currentVariantHeaps", "heapWitnessNominalRegistry",
              "currentClosureCallAxioms", "extractionErrors",
              "unknownExnWarnings", "maxWitnessSeqLen", "ptrTargetCode",
              "ptrAimPrefix", "symexTargetSolveStats", "ownContextUnits",
              "symexZ3CallCount", "seqLenBoundFacts", "fpIntervalRefutes",
              "seqRangeFacts", "dropImpliedByteDomains", "deepTermsLeftAlone",
              "mergeMemberships", "stallBackstopMs", "querySolver",
              "divRangeFacts", "factsFirstRLimit", "bvOffsetLinks",
              "bvIntInverseFacts", "bvViewRangeFacts", "cardFreeAbstraction",
              "recFactsRLimit", "defaultLoopPruneRLimit", "loopPruneRLimit",
              "symexIfArmsPruned", "symexIfArmsChecked",
              "symexLoopIterations", "limitWorldRLimit",
              "SymexQueryStat", "symexQueryStats", "symexQueryStatsPaused",
              "symexFactsFirstOff", "SymexStepStat", "symexStepStats",
              "symexPerturbConsts", "symexQueryStatsSummary",
              "symexQueryStatsTotals", "symexEqsSplits"]
  ## Threadvars `resetWalkSolveState` leaves alone: the thread's running
  ## totals and the counters a suite resets itself, the linked Z3's decl
  ## kinds (probed once per thread), and the stall deadline
  ## `beginStallDeadline` arms per walk.
  slvNotPerRun = ["symexTargetSolveStats", "ownContextUnits",
                 "symexZ3CallCount", "seqCapDeclKinds", "fpIntervalDeclKinds",
                 "byteDomainKinds", "deepTermsLeftAlone",
                 "theoryFreeNeedsSimple", "stallDeadline", "eqsSplitCaps",
                 "intDivDeclKinds", "int2bvDeclKind", "eqDeclKind",
                 "bvExtDeclKinds", "symexIfArmsPruned", "symexIfArmsChecked",
                 "symexLoopIterations"]
  ## The `-d:symexQueryStats` threadvars (in a `when`): never reset by the
  ## engine, released under the same `when`.
  slvQueryStats = ["symexQueryStats", "symexQueryStatsPaused",
                  "symexFactsFirstOff", "symexStepStats",
                  "symexPerturbConsts", "perturbSerial", "symexEqsSplits"]

suite "RFC-0016 INT-34 B5: the walk_solve leaf":
  let ws = readSmt("walk_solve.nim")

  test "walk_solve.nim imports only the allowed leaves":
    let seen = importsOf(ws)
    checkpoint $seen
    for s in seen: check s in slvAllowed
    check "./lower_expr" in seen and "./walk_types" in seen

  test "every threadvar of walk_solve.nim is reset by resetWalkSolveState or named":
    let at = ws.find("proc resetWalkSolveState*(")
    check at >= 0
    let resetBody = ws[at .. ^1]
    var tvs: seq[string]
    for l in ws.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    check tvs.len == 37   # 4 from R0, 33 from R2 (the query stats sit in `when`s)
    for n in tvs:
      checkpoint n
      if n in slvNotPerRun:
        check not resetBody.contains("\n  " & n & " = ")
      else:
        check resetBody.contains("\n  " & n & " = ")

  test "every threadvar of walk_solve.nim is released when its thread exits":
    let at = ws.find("proc releaseThreadState()")
    check at >= 0
    let body = ws[at .. ^1]
    check ws.contains("\nregisterThreadStateRelease(releaseThreadState)")
    var n = 0
    for l in ws.splitLines:
      if l.strip.startsWith("var ") and "{.threadvar.}" in l:
        let name = leadIdent(l.strip[4 .. ^1])
        checkpoint name
        check body.contains(name)
        inc n
    check n == 37 + slvQueryStats.len
    let qs = body.find("when defined(symexQueryStats):")
    check qs >= 0
    for name in slvQueryStats:
      checkpoint name
      check body[qs .. ^1].contains(name)

  test "resetSymexRunState calls resetWalkSolveState and no longer resets its threadvars":
    let rt = readSmt("runtime.nim")
    let at = rt.find("proc resetSymexRunState(")
    check at >= 0
    let e = rt.find("\n  ctx\n", at)
    check e > at
    let body = rt[at .. e]
    check body.contains("\n  resetWalkSolveState(settings)")
    for l in ws.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        let n = leadIdent(l[4 .. ^1])
        checkpoint n
        check not body.contains("\n  " & n & " = ")

  test "walk_solve names no runtime.nim symbol, and needs no hook":
    let priv = definedNames(readSmt("runtime.nim"))
    let named = referenced(ws, priv - definedNames(ws) - boundHere(ws))
    checkpoint $named
    check named.len == 0
    # R2 calls nothing above it: no typed hook table (`d3_hooks` pins it)
    check not codeOf(ws).contains("Hooks* = object")

  test "runtime.nim imports walk_solve, re-exports names not the module, and defines none of its names":
    let rt = readSmt("runtime.nim")
    check rt.contains("\nimport ./walk_solve")
    check not rt.contains("\nexport walk_solve\n")
    check not rt.contains("\nexport walk_solve except")
    var exported, want: HashSet[string]
    for l in codeOf(rt).splitLines:
      for w in l.split({' ', ','}):
        if w.startsWith("walk_solve."): exported.incl w["walk_solve.".len .. ^1]
    for n in slvPublic: want.incl n
    checkpoint $exported
    check exported == want
    let defs = definedNames(rt)
    let wd = definedNames(ws)
    for n in slvMoved:
      checkpoint n
      check n in wd
    for n in wd:
      if n in perModuleNames: continue
      checkpoint n
      check n notin defs

const
  ## RFC-0016 INT-34 B6a. What `walk_ctx.nim` may import: std, `z3`, and the
  ## leaves below it (the value core, the walk state and types, the path,
  ## lowering and solving leaves, the heap algebra and the exit channels).
  wcxAllowed = ["std/tables", "std/options", "std/hashes", "std/math",
                "std/strutils", "std/importutils", "z3", "./types",
                "./symval", "./walk_state", "./walk_types", "./walk_path",
                "./lower_expr", "./walk_solve", "./heap_model", "./exits",
                "../thread_state"]
  ## A sample of what B6a moved out of `runtime.nim`; the test below checks
  ## every name `walk_ctx.nim` defines, this list keeps the intent legible.
  wcxMoved = ["degrade", "halted", "exact", "shouldStop", "pushFrame",
              "popFrame", "initCallFrame", "initLoopFrame", "solveTargetHit",
              "takePendingLowerEffects", "restorePendingLowerEffects",
              "decideVerdict", "havocOpaqueWrites", "pruneFactsHold",
              "currentCallerHeaps", "currentClosureExitPc",
              "currentClosureCallErrors", "rfc0005RawStatus"]
  ## The names `runtime.nim` exported before the move: re-exported by name,
  ## and no other.
  wcxPublic = ["heapDepthErrors", "newFieldZeroErrors", "currentCallerHeaps",
               "currentCallerHeapDepth", "currentCallerAllocCounters",
               "currentCallerLiveRefs", "currentClosureExitHeaps",
               "currentClosureExitAllocCounters",
               "currentClosureExitLiveRefs", "currentClosureDidMutateHeap",
               "currentClosureExitPc", "currentClosureCallErrors",
               "rfc0005S1CarrierProbe", "rfc0005S1LeakPinProbe",
               "defaultConcreteBranchRLimit", "taintedSolveRLimit",
               "classifyTargetSolve", "decideVerdict", "rfc0005RawStatus"]

suite "RFC-0016 INT-34 B6a: the walk_ctx leaf":
  let wc = readSmt("walk_ctx.nim")

  test "walk_ctx.nim imports only the allowed leaves":
    let seen = importsOf(wc)
    checkpoint $seen
    for s in seen: check s in wcxAllowed
    check "./walk_solve" in seen and "./walk_types" in seen

  test "every threadvar of walk_ctx.nim is reset by resetWalkCtxState":
    let at = wc.find("proc resetWalkCtxState*(")
    check at >= 0
    let resetBody = wc[at .. ^1]
    var tvs: seq[string]
    for l in wc.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    check tvs.len == 13   # 12 from R0, `rfc0005RawStatus` from R3
    for n in tvs:
      checkpoint n
      check resetBody.contains("\n  " & n & " = ")

  test "every threadvar of walk_ctx.nim is released when its thread exits":
    let at = wc.find("proc releaseThreadState()")
    check at >= 0
    let body = wc[at .. ^1]
    check wc.contains("\nregisterThreadStateRelease(releaseThreadState)")
    var n = 0
    for l in wc.splitLines:
      if l.strip.startsWith("var ") and "{.threadvar.}" in l:
        let name = leadIdent(l.strip[4 .. ^1])
        checkpoint name
        check body.contains(name)
        inc n
    check n == 13

  test "resetSymexRunState calls resetWalkCtxState and no longer resets its threadvars":
    let rt = readSmt("runtime.nim")
    let at = rt.find("proc resetSymexRunState(")
    check at >= 0
    let e = rt.find("\n  ctx\n", at)
    check e > at
    let body = rt[at .. e]
    check body.contains("\n  resetWalkCtxState()")
    for l in wc.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        let n = leadIdent(l[4 .. ^1])
        checkpoint n
        check not body.contains("\n  " & n & " = ")

  test "walk_ctx names no runtime.nim symbol, and needs no hook":
    let priv = definedNames(readSmt("runtime.nim"))
    let named = referenced(wc, priv - definedNames(wc) - boundHere(wc))
    checkpoint $named
    check named.len == 0
    # R3 calls nothing above it: no typed hook table (`d3_hooks` pins it)
    check not codeOf(wc).contains("Hooks* = object")

  test "runtime.nim imports walk_ctx, re-exports names not the module, and defines none of its names":
    let rt = readSmt("runtime.nim")
    check rt.contains("\nimport ./walk_ctx")
    check not rt.contains("\nexport walk_ctx\n")
    check not rt.contains("\nexport walk_ctx except")
    var exported, want: HashSet[string]
    for l in codeOf(rt).splitLines:
      for w in l.split({' ', ','}):
        if w.startsWith("walk_ctx."): exported.incl w["walk_ctx.".len .. ^1]
    for n in wcxPublic: want.incl n
    checkpoint $exported
    check exported == want
    let defs = definedNames(rt)
    let wd = definedNames(wc)
    for n in wcxMoved:
      checkpoint n
      check n in wd
    for n in wd:
      if n in perModuleNames: continue
      checkpoint n
      check n notin defs

const
  ## RFC-0016 INT-34 B6b. What `walk_expr.nim` may import: std, `z3`, and the
  ## leaves below it (the build profile and the axes, the value core, the
  ## walk state and types, the path, lowering, solving and context leaves,
  ## the regex and exception tables, the heap algebra, the string support
  ## and the exit channels).
  wexAllowed = ["std/tables", "std/options", "std/sets", "std/hashes",
                "std/algorithm", "std/math", "std/strutils",
                "std/importutils", "z3", "./buildprofile", "./types",
                "./admission", "./readonlyaxes", "./arith_regime",
                "./definedness", "./variant_layout", "./abstraction",
                "./symval", "./walk_state", "./walk_types", "./walk_path",
                "./lower_expr", "./walk_solve", "./walk_ctx",
                "./regex_parser", "./exn_hierarchy", "./nativestack",
                "./z3check", "./heap_model", "./string_lower_support",
                "./exits", "./concolictaxonomy", "../thread_state"]
  ## A sample of what B6b moved out of `runtime.nim`; the test below checks
  ## every name `walk_expr.nim` defines, this list keeps the intent legible.
  wexMoved = ["lowerInExpr", "lowerBoolInExpr", "lowerLeafInExpr",
              "drainPendingLowerEffects", "drainScalarRaiseForks",
              "drainClosureExitHeap", "crashRaise", "haltUndefined",
              "haltExcludedDefect", "noteUbAtFork", "raiseSplit",
              "forkDefect", "depthBail", "concreteBranchOutcome",
              "mergeJoinPaths", "joinSV", "completeReturn", "haltFrontier",
              "boundsUnchecked", "seedCallerHeapThreadvars",
              "lastDrainedClosureExitPc", "closureBodyCallerPc"]
  ## The names `runtime.nim` exported before the move: re-exported by name,
  ## and no other.
  wexPublic = ["seedCallerHeapThreadvars", "typeIdToDefectKind",
               "concretelyInfeasible", "concreteBranchRLimit",
               "concreteBranchOutcome"]
  ## The threadvars that are not per-run: `scratchCapped` is set and cleared
  ## around each concrete-branch ask, `uninterpDeclKind` caches the linked
  ## Z3's decl kind for the thread.
  wexNotPerRun = ["scratchCapped", "uninterpDeclKind"]

suite "RFC-0016 INT-34 B6b: the walk_expr leaf":
  let we = readSmt("walk_expr.nim")

  test "walk_expr.nim imports only the allowed leaves":
    let seen = importsOf(we)
    checkpoint $seen
    for s in seen: check s in wexAllowed
    check "./walk_ctx" in seen and "./lower_expr" in seen

  test "every per-run threadvar of walk_expr.nim is reset by resetWalkExprState":
    let at = we.find("proc resetWalkExprState*(")
    check at >= 0
    let resetBody = we[at .. ^1]
    var tvs: seq[string]
    for l in we.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        tvs.add leadIdent(l[4 .. ^1])
    check tvs.len == 7   # 5 from R0, 2 from R4
    for n in tvs:
      checkpoint n
      if n in wexNotPerRun:
        check not resetBody.contains("\n  " & n & " = ")
      else:
        check resetBody.contains("\n  " & n & " = ")

  test "every threadvar of walk_expr.nim is released when its thread exits":
    let at = we.find("proc releaseThreadState()")
    check at >= 0
    let body = we[at .. ^1]
    check we.contains("\nregisterThreadStateRelease(releaseThreadState)")
    var n = 0
    for l in we.splitLines:
      if l.strip.startsWith("var ") and "{.threadvar.}" in l:
        let name = leadIdent(l.strip[4 .. ^1])
        checkpoint name
        check body.contains(name)
        inc n
    check n == 7

  test "resetSymexRunState calls resetWalkExprState and no longer resets its threadvars":
    let rt = readSmt("runtime.nim")
    let at = rt.find("proc resetSymexRunState(")
    check at >= 0
    let e = rt.find("\n  ctx\n", at)
    check e > at
    let body = rt[at .. e]
    check body.contains("\n  resetWalkExprState()")
    for l in we.splitLines:
      if l.startsWith("var ") and "{.threadvar.}" in l:
        let n = leadIdent(l[4 .. ^1])
        checkpoint n
        check not body.contains("\n  " & n & " = ")

  test "walk_expr names no runtime.nim symbol but through its hook":
    let priv = definedNames(readSmt("runtime.nim"))
    let named = referenced(viaHooks(we),
                           priv - definedNames(we) - boundHere(we))
    checkpoint $named
    check named.len == 0

  test "routeRaise is reached through walk_expr's typed hook":
    let text = codeOf(we)
    check text.count("walkExprHooks.routeRaise(") == 8
    check text.contains("\n  WalkExprHooks* = object")
    check text.contains("\n    routeRaise*: proc(")
    check text.contains("\nvar walkExprHooks*: WalkExprHooks")
    # no bare call of the runtime proc is left in the leaf
    check text.replace("walkExprHooks.routeRaise(", "").count("routeRaise(") == 0
    # runtime fills it once beside `lowerExprHooks`, with the proc itself
    let rt = codeOf(readSmt("runtime.nim"))
    check rt.count("walkExprHooks = WalkExprHooks(routeRaise: routeRaise)") == 1
    # the body stays in runtime.nim (R7); R6 calls it before it, so its
    # forward declaration stays too
    check readSmt("runtime.nim").count("\nproc routeRaise(") == 2

  test "runtime.nim imports walk_expr, re-exports names not the module, and defines none of its names":
    let rt = readSmt("runtime.nim")
    check rt.contains("\nimport ./walk_expr")
    check not rt.contains("\nexport walk_expr\n")
    check not rt.contains("\nexport walk_expr except")
    var exported, want: HashSet[string]
    for l in codeOf(rt).splitLines:
      for w in l.split({' ', ','}):
        if w.startsWith("walk_expr."): exported.incl w["walk_expr.".len .. ^1]
    for n in wexPublic: want.incl n
    checkpoint $exported
    check exported == want
    let defs = definedNames(rt)
    let wd = definedNames(we)
    for n in wexMoved:
      checkpoint n
      check n in wd
    for n in wd:
      if n in perModuleNames: continue
      checkpoint n
      check n notin defs
