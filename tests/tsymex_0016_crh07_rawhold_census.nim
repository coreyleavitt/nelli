## RFC-0016 CRH-07: the raw-handle census.
##
## The class. Z3's context is reference counted. A call that MAKES an AST
## (`Z3_mk_*`, `Z3_substitute`, `Z3_simplify`, ...) returns a node with no
## reference: Z3 keeps it only in a one-slot trail, which the next call that
## makes an AST replaces, freeing the node. A term is owned once `wrap`ped
## (nim-z3 takes a reference; `=destroy` releases it), and `x.raw` borrows
## from the owner `x` for as long as `x` lives. A raw handle stored past the
## next AST-making call, or past its owner, names freed memory. That is not
## only a crash: CRH-07's first instance (`checkExact`) read stale nodes into a
## query and returned a false `sxUnsat` before it crashed.
##
## Why a census and not a type. The raw types (`RawZ3Ast`, `RawZ3Sort`,
## `RawZ3FuncDecl`, `RawZ3App`) are nim-z3's FFI types: every C call takes
## and returns them, and `.raw` is a field of every typed term. Nim has no
## borrow checker, so no type can say "this handle may be passed but not
## stored": a non-copyable wrapper is still movable into a variable. Narrowing
## `.raw` in nim-z3 would change every one of its FFI signatures and every
## raw call here (several hundred) for a guarantee the compiler still could
## not give. The census is therefore the guard: every place `src/nelli`
## stores a raw handle is a listed, audited site, and a new one fails until it
## is classified.
##
## The sites (comment text after `#` is dropped):
##   rawtype   a line naming a raw type, other than as the element type of the
##             `cast[ptr UncheckedArray[RawZ3*]]` that passes an array to a C
##             call: a raw local, parameter, result, field, tuple or seq;
##   rawlocal  a binding (`let`/`var`, an assignment, or `.add`) whose value
##             is the result of (its first call is) a maker (`Z3_mk_*` but the symbol/config makers,
##             `Z3_substitute*`, `Z3_simplify*`, `Z3_translate`,
##             `Z3_update_term`) or a `src/nelli` proc whose result is a raw
##             type, on a line with no `wrap[`, `wrapFuncDecl[` or `keepRaw(`;
##   rawtemp   a binding that stores `<call>(...).raw` outside any call's
##             argument list (directly, or in a tuple or array literal): the
##             `.raw` of a temporary that is destroyed at the end of the
##             statement;
##   rawctor   a typed term built as an object (`Z3Xxx[...](raw: ...)`), which
##             takes no reference while its `=destroy` releases one.
## A site is `kind:file:context in routine`, context the trimmed line (`#2`,
## ... for a repeat in one routine), as `tsymex_0016_k2a_census` keys its own.
##
## The allowlist is `tests/0016-allowlist/rawhold.txt`, `site<TAB>slice<TAB>
## reason`; the reason opens with the audited disposition in brackets (see
## `dispositions`). `rawtemp` and `rawctor` have no disposition: a site of
## either kind is fixed, never listed. The list's ceiling in `ceilings.txt`
## only falls.
import std/[unittest, os, strutils, sets, tables, algorithm, sequtils]
import ./rfc0016_ids

const
  root = currentSourcePath().parentDir() / ".."
  allowPath = root / "tests" / "0016-allowlist" / "rawhold.txt"
  rfcPath = root / "docs" / "rfc" / "0016-native-parity-hardening.md"
  rawTypes = ["RawZ3Ast", "RawZ3Sort", "RawZ3FuncDecl", "RawZ3App"]
  nonAstMakers = ["Z3_mk_string_symbol", "Z3_mk_int_symbol", "Z3_mk_config",
                  "Z3_mk_context", "Z3_mk_context_rc", "Z3_mk_params"]
  makers = ["Z3_substitute", "Z3_substitute_vars", "Z3_substitute_funs",
            "Z3_simplify", "Z3_simplify_ex", "Z3_translate", "Z3_update_term"]
  owners = ["wrap[", "wrapFuncDecl[", "keepRaw("]
  dispositions* = [
    "signature",    ## a raw parameter or result: the caller owns the term for the call
    "owned-parent", ## a subterm, sort or decl of a term an owner keeps alive throughout
    "plugin-sort",  ## a built-in sort Z3's decl plugin references for the context's life
    "inc-ref",      ## referenced at once (`incRefFD` / `Z3_inc_ref`) and never released
    "used-next",    ## consumed or wrapped before any other call that makes an AST
    "run-owned"]    ## owned for the run (`keepRaw`, a registry or memo of owned terms)

type SrcFile = tuple[path, text: string]

proc isIdent(c: char): bool = c in IdentChars

proc stripComment(line: string): string =
  ## Drops `#` comment text, outside string and char literals.
  var inStr = false
  var i = 0
  while i < line.len:
    let c = line[i]
    if inStr:
      if c == '\\': inc i
      elif c == '"': inStr = false
    elif c == '"': inStr = true
    elif c == '\'' and i + 2 < line.len and line[i + 2] == '\'': i += 2
    elif c == '#': return line[0 ..< i]
    inc i
  line

proc blankStrings(l: string): string =
  ## `l` with each string literal's text blanked (the quotes kept), so a
  ## call named in a message is not a call.
  result = l
  var inStr = false
  var i = 0
  while i < result.len:
    let c = result[i]
    if inStr:
      if c == '\\':
        result[i] = ' '
        if i + 1 < result.len: result[i + 1] = ' '
        inc i
      elif c == '"': inStr = false
      else: result[i] = ' '
    elif c == '"': inStr = true
    inc i

proc hasWord(s, w: string): bool =
  var i = 0
  while true:
    i = s.find(w, i)
    if i < 0: return false
    let e = i + w.len
    if (i == 0 or not isIdent(s[i - 1])) and (e >= s.len or not isIdent(s[e])):
      return true
    i = e

proc rawTypeLine(l: string): bool =
  var s = l
  for t in rawTypes: s = s.replace("cast[ptr UncheckedArray[" & t & "]]", "")
  rawTypes.anyIt(s.hasWord(it))

proc bindingRhs(l: string): int =
  ## The index where a binding's value starts, or -1: `let`/`var x = `, an
  ## assignment `lhs = ` (not `==`, `<=`, ...), or `.add `.
  let s = l.strip(trailing = false)
  let off = l.len - s.len
  if s.startsWith("let ") or s.startsWith("var "):
    let e = s.find('=')
    if e > 0 and (e + 1 >= s.len or s[e + 1] != '='): return off + e + 1
    return -1
  let a = s.find(".add")
  if a > 0 and a + 4 < s.len and s[a + 4] in {' ', '('}: return off + a + 4
  var i = 0
  while i < s.len and (s[i].isIdent or s[i] in {'.', '[', ']', '^'}): inc i
  if i > 0 and i < s.len:
    var j = i
    while j < s.len and s[j] == ' ': inc j
    if j < s.len and s[j] == '=' and (j + 1 >= s.len or s[j + 1] != '='):
      return off + j + 1
  -1

proc callees(s: string): seq[string] =
  ## Identifiers followed by `(` (or by `[...](`, a generic call).
  var i = 0
  while i < s.len:
    if s[i].isIdent and (i == 0 or not s[i - 1].isIdent):
      var j = i
      while j < s.len and s[j].isIdent: inc j
      var k = j
      if k < s.len and s[k] == '[':
        var d = 0
        while k < s.len:
          if s[k] == '[': inc d
          elif s[k] == ']':
            dec d
            if d == 0: break
          inc k
        inc k
      while k < s.len and s[k] == ' ': inc k
      if k < s.len and s[k] == '(': result.add s[i ..< j]
      i = j
    else: inc i

proc makesAst(name: string; rawProcs: HashSet[string]): bool =
  (name.startsWith("Z3_mk_") and name notin nonAstMakers) or name in makers or
    name in rawProcs

proc storesTempRaw(rhs: string): bool =
  ## `<call>(...).raw` at a position no call's argument list encloses.
  var stack: seq[bool]   ## true: a call's parens; false: a tuple/array/group
  var i = 0
  while i < rhs.len:
    let c = rhs[i]
    if c in {'(', '['}:
      var j = i - 1
      while j >= 0 and rhs[j] == ' ': dec j
      let isCall = c == '(' and j >= 0 and (rhs[j].isIdent or rhs[j] == ']') and
                   j == i - 1
      stack.add isCall
    elif c in {')', ']'}:
      if stack.len > 0: stack.setLen(stack.len - 1)
      if c == ')' and rhs.continuesWith(".raw", i + 1) and
         (i + 5 >= rhs.len or not rhs[i + 5].isIdent) and
         not stack.anyIt(it):
        return true
    inc i
  false

proc routineName(l: string): string =
  let s = l.strip()
  for kw in ["proc ", "func ", "method ", "iterator ", "template ", "macro ",
             "converter "]:
    if s.startsWith(kw):
      var n = s[kw.len .. ^1].strip(chars = {' ', '`'})
      var e = 0
      while e < n.len and (n[e].isIdent or n[e] in {'=', '$', '<', '>'}): inc e
      return n[0 ..< e]
  ""

proc rawProcsOf(files: seq[SrcFile]): HashSet[string] =
  ## The `src/nelli` procs whose result is a raw type (the signature may span
  ## lines: the text from the name to the body's `=` is read).
  for f in files:
    let t = f.text
    for kw in ["proc ", "func "]:
      var i = 0
      while true:
        i = t.find(kw, i)
        if i < 0: break
        if i > 0 and t[i - 1] notin {'\n', ' '}: (i += kw.len; continue)
        let name = routineName(t[i ..< min(t.len, i + 200)])
        var depth = 0
        var j = i + kw.len
        var closed = -1
        while j < t.len and j < i + 2000:
          if t[j] == '(': inc depth
          elif t[j] == ')':
            dec depth
            if depth == 0: (closed = j; break)
          inc j
        if closed > 0:
          var k = closed + 1
          while k < t.len and t[k] in {' ', '\n'}: inc k
          if k < t.len and t[k] == ':':
            let tail = t[k + 1 ..< min(t.len, k + 60)].strip()
            if rawTypes.anyIt(tail.startsWith(it)) and name.len > 0:
              result.incl name
        i += kw.len

proc sites*(files: seq[SrcFile]): seq[string] =
  let rawProcs = rawProcsOf(files)
  for f in files:
    var seen = initCountTable[string]()
    var routine = "<top>"
    let lines = f.text.splitLines()
    template add(kd, cx: string) =
      let base = kd & ":" & f.path & ":" & cx & " in " & routine
      seen.inc base
      result.add(if seen[base] == 1: base else: base & "#" & $seen[base])
    for raw in lines:
      if raw.len - raw.strip(trailing = false).len <= 2:
        let r = routineName(raw)
        if r.len > 0: routine = r
      let ctx = stripComment(raw).strip()
      if ctx.len == 0: continue
      let l = blankStrings(stripComment(raw))
      if rawTypeLine(l): add("rawtype", ctx)
      let b = bindingRhs(l)
      if b >= 0:
        let rhs = l[b .. ^1]
        let heads = callees(rhs).filterIt(it != "checkErr")
        if not owners.anyIt(it in rhs) and heads.len > 0 and
           makesAst(heads[0], rawProcs):
          add("rawlocal", ctx)
        if storesTempRaw(rhs): add("rawtemp", ctx)
    # rawctor: `Z3Xxx[...](` then `raw:` (across lines).
    let t = f.text
    var i = 0
    while true:
      i = t.find("Z3", i)
      if i < 0: break
      if i > 0 and t[i - 1].isIdent: (inc i; continue)
      var j = i
      while j < t.len and t[j].isIdent: inc j
      if j < t.len and t[j] == '[':
        var d = 0
        while j < t.len:
          if t[j] == '[': inc d
          elif t[j] == ']':
            dec d
            if d == 0: break
          inc j
        inc j
      if j < t.len and t[j] == '(':
        var k = j + 1
        while k < t.len and t[k] in {' ', '\n'}: inc k
        if t.continuesWith("raw", k):
          var m = k + 3
          while m < t.len and t[m] == ' ': inc m
          if m < t.len and t[m] == ':':
            let line = t[0 ..< i].count('\n') + 1
            routine = "<file>"
            add("rawctor", t[i ..< j].strip() & " at line " & $line)
      i = max(j, i + 1)

proc collect(): seq[SrcFile] =
  for p in walkDirRec(root / "src" / "nelli"):
    if not p.endsWith(".nim"): continue
    result.add (p.relativePath(root).replace('\\', '/'), readFile(p))
  result.sort(proc (a, b: SrcFile): int = cmp(a.path, b.path))

proc kindOf(site: string): string = site.split(':')[0]

proc census*(sites: seq[string]; allow: seq[Allow];
             slices: HashSet[string]): seq[string] =
  let have = sites.toHashSet
  var listed = initHashSet[string]()
  for a in allow:
    result.add entryProblems(a, slices)
    if a.key in listed: result.add "rawhold entry " & a.key & " is listed twice"
    listed.incl a.key
    if kindOf(a.key) in ["rawtemp", "rawctor"]:
      result.add "rawhold entry " & a.key & ": a " & kindOf(a.key) &
                 " site is fixed (own the term), never listed"
    elif not dispositions.anyIt(a.reason.startsWith("[" & it & "]")):
      result.add "rawhold entry " & a.key & ": the reason must open with " &
                 "an audited disposition, one of " & dispositions.join(", ")
    if a.key notin have:
      result.add "stale rawhold entry (the site no longer exists; remove it): " &
                 a.key
  for s in sites:
    if s notin listed:
      result.add "unlisted raw-handle site (own the term, or audit it into " &
                 "tests/0016-allowlist/rawhold.txt): " & s

suite "RFC-0016 CRH-07: raw-handle census (synthetic sources)":
  let slices = toHashSet(["K8c"])
  proc kinds(src: string): seq[string] =
    sites(@[("src/nelli/x.nim", src)]).mapIt(kindOf(it))

  test "RED: CRH-07's first instance, a raw Z3_substitute result held in a var":
    check kinds("proc checkExact() =\n  var t = Z3_get_app_arg(c, a, 1)\n" &
      "  t = ctx.checkErr Z3_substitute(ctx.raw, t, n,\n") ==
      @["rawlocal"]

  test "RED: the .raw of a temporary stored in a tuple":
    check kinds("proc pointCheck() =\n" &
      "  lifted.add (st.exact.raw, pointLit(st, p).raw, st.defs)\n") ==
      @["rawtemp"]
    check kinds("proc f() =\n  let x = simp(a).raw\n") == @["rawtemp"]

  test "RED: a typed term built as an object takes no reference":
    check kinds("proc f() =\n  let fd = Z3FuncDecl[(Z3BitVec[64],), Z3BitVec[64]](\n" &
      "    raw: clo.closureRawFD, ctx: ctx)\n") == @["rawctor"]

  test "RED: a src proc returning a raw handle is a maker":
    check kinds("proc mk*(c: Z3Context): RawZ3Ast =\n  discard\n" &
      "proc g() =\n  let st = mk(ctx)\n") == @["rawtype", "rawlocal"]

  test "owned, passed and borrowed handles are not sites":
    check kinds("proc f() =\n" &
      "  let a = wrap[Z3Bool](ctx, ctx.checkErr Z3_substitute(ctx.raw, r, n, x, y))\n" &
      "  let b = foo(bar(x).raw)\n" &
      "  let c = Z3_get_app_arg(ctx.raw, app, 0)\n" &
      "  let d = ctx.checkErr Z3_mk_string_symbol(ctx.raw, n)\n" &
      "  let e = keepRaw(intToBv[8](v))\n" &
      "  pins.add simplify(subst(subst(r.raw, fs, ts).raw, ff, tt))\n" &
      "  let s = \"Z3_mk_x(#\"  # Z3_mk_y(\n" &
      "  check x == Z3_mk_int(c)\n" &
      "  let p = cast[ptr UncheckedArray[RawZ3Ast]](xs[0].addr)\n").len == 0

  test "a fully listed census is clean; rawtemp and rawctor cannot be listed":
    let s = sites(@[("src/nelli/x.nim",
      "proc f(a: RawZ3Ast) =\n  let x = g(a).raw\n")])
    check s.len == 2
    let ok = Allow(key: s[0], slice: "K8c", reason: "[signature] r")
    check census(s[0 .. 0], @[ok], slices).len == 0
    check census(s, @[ok], slices).anyIt("unlisted" in it)
    check census(s, @[ok, Allow(key: s[1], slice: "K8c",
                                reason: "[used-next] r")], slices).anyIt(
      "is fixed" in it)
    check census(s[0 .. 0], @[Allow(key: s[0], slice: "K8c", reason: "fine")],
                 slices).anyIt("disposition" in it)
    check census(@[], @[ok], slices).anyIt("stale" in it)

suite "RFC-0016 CRH-07: raw-handle census (the tree)":
  test "every raw-handle site of src/nelli is audited and every entry exists":
    let s = sites(collect())
    let allow = parseAllow(readFile(allowPath))
    let problems = census(s, allow, sliceIds11(readFile(rfcPath)))
    if problems.len > 0: echo problems.join("\n")
    check problems.len == 0

  test "the rules find what they must (a rule that finds nothing is broken)":
    let s = sites(collect())
    check s.countIt(kindOf(it) == "rawtype") >= 50
    check s.countIt(kindOf(it) == "rawlocal") >= 10
