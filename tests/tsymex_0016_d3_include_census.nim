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
##   * the forward-declaration block in `runtime.nim` (`allocRefSort` ..
##     `svCellWf`) names only symbols that `runtime_heap.nim` defines;
##   * the `symval.nim` and `walk_state.nim` leaves import only the allowed
##     leaves, `walk_state` resets every threadvar it owns in one proc, its
##     `sync*` procs append on the sinks pointer (no forward declaration is
##     left in `runtime.nim`), and `runtime.nim`
##     defines none of the names that moved into it.
import std/[unittest, os, strutils, sets, tables]

const
  root = currentSourcePath().parentDir() / ".."
  smt = root / "src" / "nelli" / "smt"

  expectedIncludes = [
    "runtime_strings.nim", "runtime_closures.nim", "runtime_heap.nim"]

  ## Includes that became real modules (D3c-3: exceptions, D3c-4: floats).
  movedToModules = ["runtime_exceptions.nim", "runtime_floats.nim"]

  ## Ratchet-down only: the measured count of distinct runtime-private
  ## symbols each include references (D3c-0: 62/21/9/26/151; D3c-1: 52/14/6/23/146; D3c-2, once the walk state left runtime.nim: as below).
  ceilings = {
    "runtime_strings.nim": 21,
    "runtime_closures.nim": 9,
    "runtime_heap.nim": 136}.toTable

  fwdFirst = "proc allocRefSort*("
  fwdLast = "proc allocateSeqDataRaw("

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
  ## (indent 2) of a `type`/`var`/`let`/`const` block.
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
        inBlock = true
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

  test "a module is imported, never included, and names no runtime symbol":
    let priv = definedNames(rt)
    for f in movedToModules:
      checkpoint f
      let m = f[0 ..< f.len - 4]
      check not rt.contains("include \"" & f & "\"")
      check rt.contains("\nimport ./" & m)
      let text = readSmt(f)
      check text.contains("\nimport ./symval")
      let named = referenced(viaHooks(text), priv - definedNames(text))
      checkpoint $named
      check named.len == 0

  test "per-include runtime-private symbol ceilings only go down":
    let priv = definedNames(rt)
    for f in expectedIncludes:
      let text = readSmt(f)
      let own = definedNames(text)
      let n = referenced(text, priv - own).len
      checkpoint f & " references " & $n & " (ceiling " & $ceilings[f] & ")"
      check n <= ceilings[f]

  test "the forward-declaration block names only heap symbols":
    let a = rt.find(fwdFirst)
    let b = rt.find(fwdLast)
    check a >= 0 and b > a
    let heap = readSmt("runtime_heap.nim")
    var names: seq[string]
    for l in rt[a ..< b].splitLines:
      if l.startsWith("proc "):
        names.add leadIdent(l[5 .. ^1])
    check names.len == 14
    for n in names:
      checkpoint n
      check heap.contains("\nproc " & n & "*(") or
            heap.contains("\nproc " & n & "(")

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
              "sameSymVal", "entryValueOf", "iteSV"]:
      checkpoint h
      check ws.contains("\n  " & h & "*: proc(")
    check readSmt("runtime_floats.nim").contains("lowerHooks.lower(")
    check readSmt("runtime.nim").contains("\nlowerHooks = LowerHooks(")
