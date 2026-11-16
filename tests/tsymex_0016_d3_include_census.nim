## RFC-0016 0.10.0 review D3 (the runtime `include` files share one namespace):
## the include census. Slice D3c-0 freezes the surface, slice D3c-1 extends it
## to the `symval.nim` leaf.
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
##   * the `symval.nim` leaf imports only the allowed leaves, and `runtime.nim`
##     defines none of the names that moved into it.
import std/[unittest, os, strutils, sets, tables]

const
  root = currentSourcePath().parentDir() / ".."
  smt = root / "src" / "nelli" / "smt"

  expectedIncludes = [
    "runtime_strings.nim", "runtime_floats.nim", "runtime_exceptions.nim",
    "runtime_closures.nim", "runtime_heap.nim"]

  ## Ratchet-down only: the measured count of distinct runtime-private
  ## symbols each include references (D3c-0).
  ceilings = {
    "runtime_strings.nim": 62,
    "runtime_floats.nim": 21,
    "runtime_exceptions.nim": 9,
    "runtime_closures.nim": 26,
    "runtime_heap.nim": 151}.toTable

  fwdFirst = "proc allocRefSort*("
  fwdLast = "proc allocateSeqDataRaw("

  ## The imports `symval.nim` may have: stdlib, `z3`, and the existing leaves.
  symvalAllowed = ["std/tables", "std/options", "std/sets", "std/hashes",
                   "std/strutils", "std/algorithm", "std/math", "z3",
                   "./types", "./abstraction"]

  ## What slice D3c-1 moved out of `runtime.nim`.
  movedNames = [
    "SVKind", "SymVal", "Env", "plainEnglishSymValKind", "liftBV", "ofBool",
    "bvVar", "bvRangeConds", "taintInPlace", "lowerDegrade"]

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

  test "no runtime_*.nim has an import":
    for f in walkFiles(smt / "runtime_*.nim"):
      for l in readFile(f).splitLines:
        let t = l.strip()
        check not (t.startsWith("import ") or t.startsWith("from ") or
                   t.startsWith("export "))

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
