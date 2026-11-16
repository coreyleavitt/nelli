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
  hmAllowed = ["std/tables", "std/options", "std/sets", "std/strutils", "z3",
               "./types", "./symval", "./walk_state", "./z3check"]
  zcAllowed = ["z3", "./types", "./symval"]

  ## The decl-kind caches of the linked Z3: the same in every run, read in a
  ## probe context (`probeContext`), so `resetHeapModel` leaves them alone.
  hmProcessStable = ["storeDeclKind", "selectDeclKind", "constArrayDeclKind",
                     "iteDeclKind", "heapChainKinds"]

  heapPinned = [
    "AddrCellEntry", "Degrade", "ElemCell", "Path", "PtrLeafAim",
    "PtrStore", "WalkCtx", "activeMemberTracked", "activeOf", "allocateSym",
    "bitsPlace", "callGuardedNames", "cellOf", "cellValue", "coerceIntLit",
    "crashRaise", "deadElemRefs", "defaultZero", "defaultZeroTotal",
    "degrade", "discConst", "drainPendingLowerEffects",
    "drainScalarRaiseForks", "effectiveHeapDepthLimit", "entryValueOf",
    "exact", "fieldsUnchecked", "forkAssignRangeCheck", "forkDefect",
    "forkPath", "forkPathTainted", "freshnessCapHints", "globalEntryVals",
    "globalHiddenRoute", "globalInitValue", "guardLiteral", "halted",
    "heapInputName", "heapKeyValTy", "heapStepsOf", "imgReadDef",
    "imgWrite", "inactiveFieldSide", "isConcolicFollowWalk", "iteFolded",
    "iteSV", "liveFrame", "loopArmInfeasible", "lowerInExpr",
    "lowerLeafInExpr", "maybeForkDefect", "noteTableKey", "overlaps",
    "pathInfeasible", "placeBits", "programGlobal", "ptrFamilyHints",
    "ptrFamilyKey", "ptrIdxKey", "ptrKeyKey", "ptrLeafAims",
    "ptrLeafPathStr", "ptrObjKey", "ptrScalarPointee", "ptrSelKey",
    "ptrTargetCode", "sameBranchSymCond", "sameSymVal", "seqArrs",
    "seqElemAt", "seqElemProto", "seqStoreArrs", "shouldStop",
    "stampHeapSteps", "storeSeqElem", "symEq", "tabValAt", "tabValTerms",
    "taintInPlace", "unionCellCount", "unionImageGate", "unwrittenImage",
    "unwrittenIn", "unwrittenKind", "unwrittenMsg", "unwrittenReadMsg",
    "unwrittenUb", "withSeqArrsOf", "writeExactArm", "zeroImage"]

  ## The imports `symval.nim` may have: stdlib, `z3`, and the existing leaves.
  symvalAllowed = ["std/tables", "std/options", "std/sets", "std/hashes",
                   "std/strutils", "std/algorithm", "std/math", "z3",
                   "./types", "./abstraction"]

  ## What slice D3c-1 moved out of `runtime.nim`.
  movedNames = [
    "SVKind", "SymVal", "Env", "plainEnglishSymValKind", "liftBV", "ofBool",
    "bvVar", "bvRangeConds", "lowerDegrade", "StrBuf", "VariantAxisSym",
    "truncBV"]

proc stripLine(line: string): string =
  ## Drops string literals and the `#` comment; keeps identifiers.
  var i = 0
  var inStr = false
  while i < line.len:
    let c = line[i]
    if inStr:
      if c == '\\': inc i
      elif c == '"': inStr = false
    elif c == '"': inStr = true
    elif c == '#': break
    else: result.add c
    inc i

proc leadIdent(s: string): string =
  for c in s:
    if c in IdentChars: result.add c else: break
  if result.len > 0 and result[0] notin IdentStartChars: result = ""

proc definedNames(text: string): HashSet[string] =
  ## Top-level definitions: `proc|func|template|macro|iterator|converter|
  ## method|type|var|let|const NAME` at column 0, and the NAME lines
  ## (indent 2) of a bare `type`/`var`/`let`/`const` block.
  var inBlock = false
  for raw in text.splitLines:
    if raw.strip().len == 0 or raw[0] == '#': continue
    if raw[0] != ' ':
      inBlock = false
      let l = stripLine(raw)
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
        if ws.len > 1:
          let n = leadIdent(ws[1])
          if n.len > 0: result.incl n
      else: discard
    elif inBlock and raw.len > 2 and raw[1] == ' ' and raw[2] != ' ':
      let n = leadIdent(stripLine(raw).strip())
      if n.len > 0: result.incl n

proc referenced(text: string, names: HashSet[string]): HashSet[string] =
  for raw in text.splitLines:
    var cur = ""
    for c in stripLine(raw) & " ":
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
  for raw in text.splitLines:
    let l = stripLine(raw)
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
  const tag = "lowerHooks."
  var i = 0
  while i < text.len:
    if text.continuesWith(tag, i):
      i += tag.len
      while i < text.len and text[i] in IdentChars: inc i
    else:
      result.add text[i]
      inc i

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
    for f in ["symval.nim", "walk_state.nim", "z3check.nim", "heap_model.nim",
              "string_lower_support.nim"]:
      check f in listed
    for f in runtimeFamilyFiles:
      check fileExists(smt / f)

  test "a module is imported, never included, and names no runtime symbol":
    let priv = definedNames(rt)
    for f in movedToModules:
      checkpoint f
      let m = f[0 ..< f.len - 4]
      check not rt.contains("include \"" & f & "\"")
      check rt.contains("\nimport ./" & m)
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
    let priv = definedNames(rt)
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
    for l in sv.splitLines:
      let t = stripLine(l).strip()
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
    check tvs.len == 3
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
               "./definedness", "./errorkind", "./pcre_syntax"]

  wsMoved = [
    "currentWalkCtxPtr", "currentRefSorts", "currentNilConsts",
    "currentMaxSplitParts", "currentInFlightTypeId", "currentInFlightMsg",
    "currentExnRefCounter", "lastGetCurrentExnRef", "currentClosureSyms",
    "currentClosureBodies", "currentDistinctSorts",
    "convFloatToIntBoundConds", "rangeDefectConds", "divByZeroConds",
    "overflowConds", "strIndexOobConds", "regexRaiseMsgs",
    "parseIntRaiseConds", "regexRecDefConds", "regexRecFactConds",
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
    for l in ws.splitLines:
      let t = stripLine(l).strip()
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
    check tvs.len == 26
    for n in tvs:
      checkpoint n
      check resetBody.contains("\n  " & n & " = ")

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
    check rt.contains("    sinks:     LowerSinks")
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
    for h in ["lower", "lowerClosureCall", "seqElemAt", "storeSeqElem",
              "sameSymVal", "entryValueOf", "iteSV", "allocateSym",
              "currentFrameId", "registerCapCell", "depositStrIndexOob"]:
      checkpoint h
      check ws.contains("\n  " & h & "*: proc(")
    check not ws.contains("sortOfTuple*:")   # D3c-6: read directly from heap_model
    check readSmt("runtime_floats.nim").contains("lowerHooks.lower(")
    check readSmt("runtime_closures.nim").contains("lowerHooks.allocateSym(")
    check readSmt("runtime.nim").contains("\nlowerHooks = LowerHooks(")

proc importsOf(text: string): seq[string] =
  for l in text.splitLines:
    let t = stripLine(l).strip()
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
    check tvs.len == 15
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
                "std/strutils", "z3", "./types"]
  strAllowed = ["std/tables", "std/options", "std/sets", "std/strutils", "z3",
                "./types", "./abstraction", "./symval", "./walk_state",
                "./z3check", "./heap_model", "./string_lower_support",
                "./regex_parser", "./pcre_select", "./pcre_engine",
                "./pcre_syntax", "./errorkind", "./stdlib_rows"]
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
    check rt.contains("\nexport string_lower_support")
    let defs = definedNames(rt)
    for n in d3c7Moved:
      checkpoint n
      check n notin defs
    for n in definedNames(readSmt("string_lower_support.nim")):
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
    check tvs.len == 5
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
