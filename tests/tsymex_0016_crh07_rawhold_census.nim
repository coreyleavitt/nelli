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
##
## RFC-0016 int6-z extended the census to the whole class (a raw handle held
## or wrapped outside nim-z3's RC protocol), in three parts.
## (a) Building a wrapper from a raw handle. Only nim-z3's `wrap[T]`,
##   `wrapFuncDecl` and the `wrap<Kind>` procs take the reference; src/nelli
##   builds nothing itself. Never listed (fix: `wrap`): `rawctor` (now with
##   `raw:` in any position), `rawassign` (`x.raw = ...`), `rawcast`
##   (`cast[Z3...]`), `rawborrow` (a `wrap*Borrowed` call, which takes no
##   reference), `rawdec` (a manual `Z3_dec_ref`). Listed: `rawrc`, a manual
##   `Z3_inc_ref`/`incRefFD` (`[inc-ref]`: the pin the RFC's S8ck-r fix added).
## (b) Storing a handle. `rawtype` now names every nim-z3 raw type and the C
##   names (it read four), and a test reads nim-z3's ffi to keep the list
##   whole. Storage no type names: `rawalias` (a `let`/`var` bound to a
##   `.raw`, a tuple/seq/array literal of handles or of getter or maker
##   results), `rawglobal` (a top-level binding of a handle; never listed),
##   `rawaddr` (a handle cast to a pointer or integer and stored or used as a
##   key: the address of a freed node is reused, so the entry must hold the
##   node, `[addr-owned]`, or name a run-long identity, `[addr-run]`).
## (c) A handle held across a call that can free it. Not decidable without
##   types, so it is approximated, and every approximation errs toward a
##   site: `rawget` (a local or container bound to a borrowing getter whose
##   parent is not an owner: a parameter, an `x.raw` path, a chain rooted in
##   one, or a `.pop()` of an audited worklist), `rawspan` (a maker's raw
##   result read after a LATER statement that itself calls `Z3_mk_*`,
##   `Z3_substitute*`, `Z3_simplify*` or `wrap[`; the lexical scope and the
##   statement that wraps are read, so `wrap[T](ctx, ... a ...)` consumes `a`
##   as an argument; may not be `[used-next]`), `rawstr` (a Z3 string buffer
##   not copied with `$`; never listed). NOT seen: a nim-z3 operator or
##   `mkInt(...)` between the bind and the use (it makes a term without a
##   `Z3_mk_` token), a handle used on a different control-flow branch than
##   its bind, and a binding of a parameter's name rebound elsewhere.
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
  allowLifePath = root / "tests" / "0016-allowlist" / "rawlife.txt"
  ffiPath = root / "_deps" / "z3" / "src" / "z3" / "ffi.nim"
  rawTypes = ["RawZ3Ast", "RawZ3Sort", "RawZ3FuncDecl", "RawZ3App",
              "RawZ3Context", "RawZ3Config", "RawZ3Symbol", "RawZ3Solver",
              "RawZ3Model", "RawZ3AstVector", "RawZ3Constructor",
              "RawZ3ConstructorList", "RawZ3Pattern", "RawZ3Optimize",
              "RawZ3Fixedpoint", "RawZ3Stats", "RawZ3Goal", "RawZ3Tactic",
              "RawZ3Probe", "RawZ3ApplyResult", "RawZ3Params",
              "RawZ3ParserContext", "RawZ3FuncInterp", "RawZ3FuncEntry",
              "RawZ3ParamDescrs", "RawZ3AstMap", "RawZ3RcfNum",
              "RawZ3Simplifier", "RawZ3PropagatorCtxBox",
              # the C names, should a header type be named directly
              "Z3_ast", "Z3_sort", "Z3_func_decl", "Z3_app", "Z3_context",
              "Z3_model", "Z3_solver", "Z3_symbol", "Z3_pattern",
              "Z3_ast_vector", "Z3_func_interp", "Z3_params"]
  nonAstMakers = ["Z3_mk_string_symbol", "Z3_mk_int_symbol", "Z3_mk_config",
                  "Z3_mk_context", "Z3_mk_context_rc", "Z3_mk_params"]
  makers = ["Z3_substitute", "Z3_substitute_vars", "Z3_substitute_funs",
            "Z3_simplify", "Z3_simplify_ex", "Z3_translate", "Z3_update_term",
            "Z3_model_eval", "Z3_model_get_const_interp",
            "Z3_func_interp_get_else", "Z3_func_interp_get_entry",
            "Z3_ast_vector_get", "Z3_pattern_to_ast", "Z3_ast_map_find",
            "Z3_solver_get_model", "Z3_solver_get_proof"]
  ## Calls that return a handle BORROWED from their first handle argument: the
  ## result lives only as long as that parent does.
  borrowGetters = ["Z3_get_app_arg", "Z3_get_app_decl", "Z3_get_sort",
                   "Z3_get_range", "Z3_get_domain", "Z3_get_array_sort_range",
                   "Z3_get_array_sort_domain", "Z3_get_quantifier_body",
                   "Z3_to_app", "Z3_sort_to_ast", "Z3_func_decl_to_ast",
                   "Z3_to_func_decl", "Z3_get_quantifier_bound_name"]
  ## Calls that return a `const char*` into a buffer Z3 reuses on its next
  ## call; the text must be copied (`$`) in the statement that reads it.
  strGetters = ["Z3_get_numeral_string", "Z3_ast_to_string",
                "Z3_sort_to_string", "Z3_get_symbol_string",
                "Z3_func_decl_to_string", "Z3_model_to_string",
                "Z3_get_string", "Z3_get_full_version", "Z3_get_error_msg",
                "Z3_solver_to_string", "Z3_get_decl_name_string"]
  rcCalls = ["Z3_inc_ref", "incRefFD"]
  decCalls = ["Z3_dec_ref", "decRefFD"]
  addrTypes = ["pointer", "uint", "int", "uint64", "int64", "uint32",
               "int32", "csize_t", "ByteAddress"]
  owners = ["wrap[", "wrapFuncDecl[", "keepRaw("]
  dispositions* = [
    "signature",    ## a raw parameter or result: the caller owns the term for the call
    "owned-parent", ## a subterm, sort or decl of a term an owner keeps alive throughout
    "plugin-sort",  ## a built-in sort Z3's decl plugin references for the context's life
    "inc-ref",      ## referenced at once (`incRefFD` / `Z3_inc_ref`) and never released
    "used-next",    ## consumed or wrapped before any other call that makes an AST
    "run-owned",    ## owned for the run (`keepRaw`, a registry or memo of owned terms)
    "addr-owned",   ## an address used as a key or identity, beside an owner that is held as long as the entry lives
    "addr-run"]     ## an address of a context or object that lives for the whole run, compared only
  neverListed = ["rawtemp", "rawctor", "rawassign", "rawcast", "rawborrow",
                 "rawdec", "rawstr", "rawglobal"]

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

proc closeOf(s: string; open: int): int =
  ## The index of the bracket closing the one at `open`, or -1.
  var d = 0
  for i in open ..< s.len:
    if s[i] in {'(', '['}: inc d
    elif s[i] in {')', ']'}:
      dec d
      if d == 0: return i
  -1

proc splitArgs(s: string): seq[string] =
  ## `s` split at its depth-0 commas.
  var d = 0
  var cur = ""
  for c in s:
    if c in {'(', '['}: inc d
    elif c in {')', ']'}: dec d
    if c == ',' and d == 0:
      result.add cur.strip()
      cur = ""
    else: cur.add c
  if cur.strip().len > 0: result.add cur.strip()

proc firstCall(rhs: string; names: openArray[string]):
    tuple[name, args: string] =
  ## The leftmost call in `rhs` whose callee is in `names`.
  var best = rhs.len
  for n in names:
    var i = 0
    while true:
      i = rhs.find(n & "(", i)
      if i < 0: break
      if i == 0 or not rhs[i - 1].isIdent:
        if i < best:
          best = i
          let c = rhs.closeOf(i + n.len)
          result = (n, rhs[i + n.len + 1 ..< (if c < 0: rhs.len else: c)])
        break
      i += n.len

proc isOwnerPath(a: string): bool =
  ## `x.raw`, `a.b[i].raw`: the `.raw` of a plain path with no call in it (an
  ## owner a local, parameter or field keeps alive).
  let t = a.strip()
  if not t.endsWith(".raw") or t.len <= 4: return false
  for c in t[0 ..< t.len - 4]:
    if not (c.isIdent or c in {'.', '[', ']', ' ', '^', '-', '+'}): return false
  true

proc ownedParent(arg: string; known: HashSet[string]; depth = 0): bool =
  ## The handle argument of a borrowing getter names an owner (or is a getter
  ## chain rooted in one).
  let a = arg.strip()
  if isOwnerPath(a) or a in known: return true
  if depth > 6: return false
  let g = firstCall(a, borrowGetters)
  if g.name.len > 0 and a.startsWith(g.name & "("):
    let ps = splitArgs(g.args)
    return ps.len >= 2 and ownedParent(ps[1], known, depth + 1)
  false

proc rawPlainOutsideCall(rhs: string): bool =
  ## `<path>.raw` (no call in the path) at a position no call's argument list
  ## encloses: stored by a binding, a tuple, an array or a seq literal.
  var stack: seq[bool]
  var i = 0
  while i < rhs.len:
    let c = rhs[i]
    if c in {'(', '['}:
      var j = i - 1
      while j >= 0 and rhs[j] == ' ': dec j
      stack.add(c == '(' and j >= 0 and (rhs[j].isIdent or rhs[j] == ']') and
                j == i - 1)
    elif c in {')', ']'}:
      if stack.len > 0: stack.setLen(stack.len - 1)
    elif c == '.' and rhs.continuesWith(".raw", i) and
         (i + 4 >= rhs.len or (not rhs[i + 4].isIdent and rhs[i + 4] != '.')) and
         i > 0 and (rhs[i - 1].isIdent or rhs[i - 1] == ']') and
         not stack.anyIt(it):
      return true
    inc i
  false

proc callAt(l: string; names: openArray[string]): string =
  ## The first of `names` called in `l` (a whole word followed by `(` or a
  ## space), or "".
  for n in names:
    var i = 0
    while true:
      i = l.find(n, i)
      if i < 0: break
      let e = i + n.len
      if (i == 0 or not l[i - 1].isIdent) and e < l.len and l[e] in {'(', ' '}:
        return n
      i = e

proc castOfRaw(l: string): bool =
  ## `cast[pointer|uint|int...](..<handle>.raw..)`: a handle laundered into an
  ## address or an integer.
  for t in addrTypes:
    let k = "cast[" & t & "]("
    var i = 0
    while true:
      i = l.find(k, i)
      if i < 0: break
      let c = l.closeOf(i + k.len - 1)
      let inner = l[i + k.len ..< (if c < 0: l.len else: c)]
      if ".raw" in inner or inner.hasWord("Z3_get_app_arg"): return true
      i += k.len
  false

proc assignsRaw(l: string): bool =
  ## `<path>.raw = ...`: a wrapper's handle written in place.
  var i = 0
  while true:
    i = l.find(".raw", i)
    if i < 0: return false
    let e = i + 4
    if e >= l.len or not l[e].isIdent:
      let rest = l[e ..< l.len].strip()
      if rest.startsWith("=") and not rest.startsWith("=="): return true
    i = e

proc indentOf(l: string): int = l.len - l.strip(trailing = false).len

proc localName(l: string): string =
  ## The plain identifier a `let`/`var`/assignment line binds, or "".
  var t = l.strip()
  for kw in ["let ", "var "]:
    if t.startsWith(kw): t = t[kw.len .. ^1]
  var e = 0
  while e < t.len and t[e].isIdent: inc e
  if e == 0: return ""
  var j = e
  while j < t.len and t[j] == ' ': inc j
  if j < t.len and (t[j] == '=' or t[j] == ':') and
     not (j + 1 < t.len and t[j + 1] == '='): return t[0 ..< e]
  ""

proc paramNames(sig: string): HashSet[string] =
  ## The parameter names of the routine whose header starts `sig`. A handle
  ## borrowed from a parameter is borrowed from a term the caller owns for
  ## the call (the `[signature]` disposition).
  let o = sig.find('(')
  if o < 0: return
  let c = sig.closeOf(o)
  if c < 0: return
  for part in splitArgs(sig[o + 1 ..< c].replace(";", ",")):
    var n = part.split(':')[0].strip()
    if n.startsWith("var "): n = n[4 .. ^1].strip()
    if n.len > 0 and n.allIt(it.isIdent): result.incl n

proc lineWraps(l: string): bool =
  ## The statement continues on the next line (it ends in an operator, comma
  ## or open bracket).
  let t = l.strip()
  t.len > 0 and (t[^1] in {',', '(', '[', '=', '+', '-', '*', '/', '&', '|',
                           '<', '>'} or t.endsWith(" and") or
                 t.endsWith(" or"))

proc spanViolation(lines: seq[string]; at: int): bool =
  ## A raw handle bound at `lines[at]` (a maker's result, not wrapped) is used
  ## after a LATER statement that itself makes an AST: Z3 frees the earlier
  ## node when the next maker replaces its one-slot trail. The scan is
  ## lexical: the binding's own statement (its deeper-indented lines) is
  ## skipped, the scope ends at the first line indented less than the binding,
  ## and only a direct `Z3_mk_*`/substitute/simplify call or a `wrap[...]`
  ## counts as the intervening maker (a nim-z3 operator or `mkInt` between is
  ## not seen). `lines` are comment- and string-blind.
  let nm = localName(lines[at])
  if nm.len == 0: return false
  let ind = indentOf(lines[at])
  var stmtEnd = at
  while stmtEnd + 1 < lines.len and lines[stmtEnd + 1].strip().len > 0 and
        indentOf(lines[stmtEnd + 1]) > ind: inc stmtEnd
  var lastUse = -1
  for k in stmtEnd + 1 ..< lines.len:
    let l = lines[k]
    if l.strip().len == 0: continue
    if indentOf(l) < ind: break
    if l.hasWord(nm): lastUse = k
  if lastUse < 0: return false
  # the use sits in a statement that may start on an earlier line (a wrapped
  # call): arguments are evaluated before the call that encloses them
  var useStart = lastUse
  while useStart - 1 > stmtEnd and lineWraps(lines[useStart - 1]): dec useStart
  for k in stmtEnd + 1 ..< useStart:
    let l = lines[k]
    if callees(l).anyIt((it.startsWith("Z3_mk_") and it notin nonAstMakers) or
                        it in makers) or "wrap[" in l: return true
  false

proc sites*(files: seq[SrcFile]): seq[string] =
  let rawProcs = rawProcsOf(files)
  for f in files:
    var seen = initCountTable[string]()
    var routine = "<top>"
    var known = initHashSet[string]()   ## raw locals borrowed from an owner
    let lines = f.text.splitLines()
    template add(kd, cx: string) =
      let base = kd & ":" & f.path & ":" & cx & " in " & routine
      seen.inc base
      result.add(if seen[base] == 1: base else: base & "#" & $seen[base])
    let blind = lines.mapIt(blankStrings(stripComment(it)))
    for idx, raw in lines:
      if raw.len - raw.strip(trailing = false).len <= 2:
        let r = routineName(raw)
        if r.len > 0:
          routine = r
          known = paramNames(lines[idx ..< min(lines.len, idx + 8)].join(" "))
      let ctx = stripComment(raw).strip()
      if ctx.len == 0: continue
      let l = blind[idx]
      if rawTypeLine(l): add("rawtype", ctx)
      let b = bindingRhs(l)
      if b >= 0:
        let rhs = l[b .. ^1]
        let heads = callees(rhs).filterIt(it != "checkErr")
        if not owners.anyIt(it in rhs) and heads.len > 0 and
           makesAst(heads[0], rawProcs):
          add("rawlocal", ctx)
          # (c): the handle must not outlive a later AST-making statement
          if spanViolation(blind, idx): add("rawspan", ctx)
        if storesTempRaw(rhs): add("rawtemp", ctx)
        # (b): a handle stored in an inferred local, tuple, seq or table
        elif rawPlainOutsideCall(rhs) and " == " notin rhs and " != " notin rhs and
             (ctx.startsWith("let ") or ctx.startsWith("var ")):
          add("rawalias", ctx)
        elif (rhs.strip().startsWith("@[") or rhs.strip().startsWith("[")) and
             "wrap[" notin rhs and (firstCall(rhs, borrowGetters).name.len > 0 or
               callees(rhs).anyIt(makesAst(it, initHashSet[string]()))) and
             (ctx.startsWith("let ") or ctx.startsWith("var ")):
          add("rawalias", ctx)   # a literal of getter or maker results
        # (b): a handle stored in a global or threadvar of inferred type
        if raw.len > 0 and raw[0] != ' ' and (".raw" in rhs or
           (heads.len > 0 and makesAst(heads[0], rawProcs))):
          add("rawglobal", ctx)
        # (c): a borrowed handle whose parent is not an owner
        var stmt = rhs
        var k = idx
        while stmt.count('(') > stmt.count(')') and k + 1 < lines.len and
              k < idx + 8:
          inc k
          stmt.add " " & blind[k].strip()
        if ".pop()" in rhs:
          # a traversal worklist's element: its own `seq[Raw...]` declaration
          # is the audited site, and the roots it was seeded from are owned
          var nm = ""
          for ch in l[0 ..< b]:
            if ch.isIdent: nm.add ch
            else:
              if nm.len > 0 and nm notin ["let", "var"]: known.incl nm
              nm = ""
        let g = firstCall(stmt, borrowGetters)
        if g.name.len > 0 and not owners.anyIt(it in rhs) and
           heads.len > 0 and heads[0] == g.name:
          let ps = splitArgs(g.args)
          if ps.len >= 2 and ownedParent(ps[1], known):
            if localName(l).len > 0: known.incl localName(l)
          else:
            add("rawget", ctx)
            known.excl localName(l)
        elif localName(l).len > 0 and ".pop()" notin rhs: known.excl localName(l)
      # (a): a wrapper written over a raw handle, a borrowed wrap, manual RC
      if assignsRaw(l): add("rawassign", ctx)
      if "cast[Z3" in l: add("rawcast", ctx)
      if callees(l).anyIt("Borrowed" in it): add("rawborrow", ctx)
      if callAt(l, rcCalls).len > 0 and routineName(raw).len == 0:
        add("rawrc", ctx)
      if callAt(l, decCalls).len > 0 and routineName(raw).len == 0:
        add("rawdec", ctx)
      # (b): a handle laundered into an address or integer and stored
      if castOfRaw(l) and "==" notin l and "!=" notin l:
        add("rawaddr", ctx)
      # (c): a Z3 string buffer is valid only until Z3's next call
      let sg = callAt(l, strGetters)
      if sg.len > 0:
        let at = l.find(sg & "(")
        if at < 0 or at == 0 or l[at - 1] != '$': add("rawstr", ctx)
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
        # `raw:` among the constructor's fields, first or not
        let ce = t.closeOf(j)
        let body = t[j + 1 ..< (if ce < 0: t.len else: ce)]
        var hasRaw = false
        for part in splitArgs(body):
          let pt = part.strip()
          if pt.startsWith("raw"):
            let rest = pt[3 .. ^1].strip()
            if rest.startsWith(":") and not rest.startsWith("::"): hasRaw = true
        if hasRaw:
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
    if kindOf(a.key) in neverListed:
      result.add "rawhold entry " & a.key & ": a " & kindOf(a.key) &
                 " site is fixed (own the term), never listed"
    elif kindOf(a.key) == "rawspan" and
         (a.reason.startsWith("[used-next]") or
          a.reason.startsWith("[signature]")):
      result.add "rawhold entry " & a.key & ": a rawspan site is used after " &
                 "a later maker, so it is not used-next; say what keeps the " &
                 "term alive (owned-parent, inc-ref, run-owned, plugin-sort)"
    elif not dispositions.anyIt(a.reason.startsWith("[" & it & "]")):
      result.add "rawhold entry " & a.key & ": the reason must open with " &
                 "an audited disposition, one of " & dispositions.join(", ")
    if a.key notin have:
      result.add "stale rawhold entry (the site no longer exists; remove it): " &
                 a.key
  for s in sites:
    if s notin listed:
      result.add "unlisted raw-handle site (own the term, or audit it into " &
                 "tests/0016-allowlist/rawhold.txt or rawlife.txt): " & s

suite "RFC-0016 CRH-07: raw-handle census (synthetic sources)":
  let slices = toHashSet(["K8c"])
  proc kinds(src: string): seq[string] =
    sites(@[("src/nelli/x.nim", src)]).mapIt(kindOf(it))

  test "RED: CRH-07's first instance, a raw Z3_substitute result held in a var":
    check kinds("proc checkExact() =\n  var t = Z3_get_app_arg(c, a, 1)\n" &
      "  t = ctx.checkErr Z3_substitute(ctx.raw, t, n,\n") ==
      @["rawget", "rawlocal"]

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
      "  let c = Z3_get_app_arg(ctx.raw, node.raw, 0)\n" &
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

  test "RED (a): a wrapper built over a raw handle, however written":
    check kinds("proc f() =\n  let b = Z3Bool(ctx: ctx, raw: r)\n") == @["rawctor"]
    check kinds("proc f() =\n  var b: Z3Bool\n  b.raw = r\n") == @["rawassign"]
    check kinds("proc f() =\n  let b = cast[Z3Bool](p)\n") == @["rawcast"]
    check kinds("proc f() =\n  let c = wrapContextBorrowed(r)\n") == @["rawborrow"]
    check kinds("proc f() =\n  Z3_inc_ref(ctx.raw, a)\n") == @["rawrc"]
    check kinds("proc f() =\n  Z3_dec_ref(ctx.raw, a)\n") == @["rawdec"]
    check kinds("proc f() =\n  check b.raw == c.raw\n").len == 0

  test "RED (b): a handle stored where no type names it, or as an address":
    check kinds("proc f() =\n  let t = (a.raw, b.raw)\n") == @["rawalias"]
    check kinds("proc f() =\n  var xs = @[a.raw]\n") == @["rawalias"]
    check kinds("var g = x.raw\n") == @["rawalias", "rawglobal"]
    check kinds("proc f() =\n  var b = [Z3_to_app(ctx.raw, i.raw)]\n") ==
      @["rawalias"]
    check kinds("proc f() =\n  let b = @[wrap[Z3Bool](ctx, Z3_mk_true(ctx.raw))]\n").len == 0
    check kinds("proc f() =\n  seen[cast[uint](x.raw)] = x\n") == @["rawaddr"]
    check kinds("proc f() =\n  let k = cast[pointer](x.raw)\n") == @["rawaddr"]
    check kinds("proc f() =\n  if cast[pointer](a.raw) == cast[pointer](b.raw): 1\n").len == 0
    check kinds("proc f() =\n  var m: RawZ3Model\n  let c: Z3_ast = a\n") ==
      @["rawtype", "rawtype"]
    check kinds("proc f() =\n  let c = x.raw.foo\n  let d = hit.raw.name\n").len == 0

  test "RED (c): a borrowed handle whose parent is no owner":
    check kinds("proc f() =\n  let s = Z3_get_sort(ctx.raw, mkInt(pc, 0).raw)\n") ==
      @["rawget"]
    check kinds("proc f() =\n  let a = Z3_get_array_sort_range(ctx.raw, srt)\n") ==
      @["rawget"]
    # a parameter, an owner's .raw, a getter chain rooted in either, a popped
    # worklist element: borrowed from a term something owns
    check kinds("proc f(ctx: Z3Context; t: RawZ3Ast) =\n" &
      "  let app = Z3_to_app(ctx.raw, t)\n" &
      "  let d = Z3_get_app_decl(ctx.raw, app)\n") == @["rawtype"]   # the signature
    check kinds("proc f() =\n" &
      "  let app = Z3_to_app(ctx.raw, x.raw)\n" &
      "  let a = Z3_get_app_arg(ctx.raw, app, 0)\n" &
      "  let b = Z3_get_app_arg(ctx.raw, Z3_to_app(ctx.raw, y[i].raw), 1)\n").len == 0
    check kinds("proc f() =\n  let t = stack.pop()\n" &
      "  let app = Z3_to_app(ctx.raw, t)\n").len == 0
    # a rebinding to something unowned drops the borrow
    check kinds("proc f() =\n  let app = Z3_to_app(ctx.raw, x.raw)\n" &
      "  app = other(1)\n  let a = Z3_get_app_arg(ctx.raw, app, 0)\n") == @["rawget"]

  test "RED (c): a raw maker result held across a later maker":
    # `a` is read after `b` is made: Z3 frees `a` when `b` replaces its trail
    check kinds("proc f() =\n" &
      "  let a = ctx.checkErr Z3_mk_const(ctx.raw, s, srt)\n" &
      "  let b = ctx.checkErr Z3_mk_not(ctx.raw, x)\n" &
      "  use(a)\n") == @["rawlocal", "rawspan", "rawlocal"]
    # wrapped before the next maker, or consumed by the statement that wraps
    check kinds("proc f() =\n" &
      "  let a = ctx.checkErr Z3_mk_const(ctx.raw, s, srt)\n" &
      "  let w = wrap[Z3Bool](ctx, a)\n" &
      "  let b = ctx.checkErr Z3_mk_not(ctx.raw, x)\n") == @["rawlocal", "rawlocal"]
    check kinds("proc f() =\n" &
      "  let a = ctx.checkErr Z3_mk_const(ctx.raw, s, srt)\n" &
      "  return wrap[Z3Bool](ctx,\n" &
      "    checkedEq(ctx, a, b))\n") == @["rawlocal"]
    # a later maker outside the binding's scope does not count
    check kinds("proc f() =\n  if c:\n" &
      "    let a = ctx.checkErr Z3_mk_const(ctx.raw, s, srt)\n" &
      "    use(a)\n" &
      "  let b = ctx.checkErr Z3_mk_not(ctx.raw, x)\n") == @["rawlocal", "rawlocal"]

  test "RED (c): a Z3 string buffer held, not copied":
    check kinds("proc f() =\n  let s = Z3_ast_to_string(ctx.raw, a.raw)\n") ==
      @["rawstr"]
    check kinds("proc f() =\n  let s = $Z3_ast_to_string(ctx.raw, a.raw)\n").len == 0

  test "the kinds a fix owns cannot be listed; a rawspan is not used-next":
    for src in ["proc f() =\n  var b: Z3Bool\n  b.raw = r\n",
                "proc f() =\n  Z3_dec_ref(ctx.raw, a)\n",
                "proc f() =\n  let s = Z3_ast_to_string(ctx.raw, a.raw)\n"]:
      let s = sites(@[("src/nelli/x.nim", src)])
      check s.len == 1
      check census(s, @[Allow(key: s[0], slice: "K8c",
                              reason: "[owned-parent] r")], slices).anyIt(
        "is fixed" in it)
    let sp = sites(@[("src/nelli/x.nim",
      "proc f() =\n  let a = ctx.checkErr Z3_mk_const(ctx.raw, s, srt)\n" &
      "  let b = ctx.checkErr Z3_mk_not(ctx.raw, x)\n  use(a)\n")])
    let spanKey = sp.filterIt(kindOf(it) == "rawspan")[0]
    check census(@[spanKey], @[Allow(key: spanKey, slice: "K8c",
      reason: "[used-next] r")], slices).anyIt("not used-next" in it)
    check census(@[spanKey], @[Allow(key: spanKey, slice: "K8c",
      reason: "[run-owned] r")], slices).len == 0

  test "the raw-type list covers every raw type nim-z3 declares":
    if fileExists(ffiPath):
      var declared = 0
      for l in readFile(ffiPath).splitLines():
        let t = l.strip()
        if t.startsWith("Raw") and "importc" in t:
          inc declared
          check t.split({' ', '*'})[0] in rawTypes
      check declared > 20
    # no `_deps/z3` (a checkout without its dependencies): nothing to read

suite "RFC-0016 CRH-07: raw-handle census (the tree)":
  test "every raw-handle site of src/nelli is audited and every entry exists":
    let s = sites(collect())
    let allow = parseAllow(readFile(allowPath)) &
                parseAllow(readFile(allowLifePath))
    let problems = census(s, allow, sliceIds11(readFile(rfcPath)))
    if problems.len > 0: echo problems.join("\n")
    check problems.len == 0

  test "the rules find what they must (a rule that finds nothing is broken)":
    let s = sites(collect())
    check s.countIt(kindOf(it) == "rawtype") >= 50
    check s.countIt(kindOf(it) == "rawlocal") >= 10
    check s.countIt(kindOf(it) == "rawget") >= 15
    check s.countIt(kindOf(it) == "rawspan") >= 5
    check s.countIt(kindOf(it) == "rawaddr") >= 10
    check s.countIt(kindOf(it) == "rawrc") >= 4
    # no wrapper is built over a raw handle, no manual release, no held
    # string buffer: these kinds are fixed, never listed
    for k in neverListed: check s.countIt(kindOf(it) == k) == 0
