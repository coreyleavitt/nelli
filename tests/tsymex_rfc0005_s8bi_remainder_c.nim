## RFC-0005 (soundness channels) slice S8bi -- S8bb's remainder, part A:
## the soundness and crash items S8bb reported and did not fix.
##
## Item 1: every node that can raise counts as a raise site in
## `rhsHasInlineDefectFork`. A call through a closure, a `map`/`filter`
## over a closure, a borrowed arithmetic operator and a regex call were
## carriers only (their operands could raise, they could not), so in a
## `while` guard -- where `parseAtomicOperand` hoists nothing and the
## predicate is the only protection -- D1c's flat fast path lowered them
## whether or not the short circuit reached them: `b >= 0 and f(b)` forked
## `f`'s raise for `b < 0`, a false `sxSat`.
##
## Item 2: each raise carries only the facts of what was evaluated before
## it. A closure call's exit facts (its body did not raise) were appended
## to every raise of the expression, also those evaluated before the call:
## in `while ord(s[i]) + f(x) > 0` the `IndexDefect` was forked only with
## `x <= 5`, a false `sxUnsat`. And an operand left inline (`s[i]`) was
## evaluated after a later operand's hoisted `let`s.
##
## Item 3: `newSeq[T](n)`, `newSeq(s, n)`, `newSeqOfCap[T](n)` and
## `newSeqUninit[T](n)` aborted the compile ("node has no type").
##
## Item 4: `k in {..}` / `k notin {..}` over a set literal was
## `feUnsupportedExprKind` (nnkCurly).
##
## Item 5: every recursive Z3 definition carries a decreasing fuel bound
## (Z3 unfolds one without spending `rlimit`); a source scan pins it.
##
## RFC-0005 S8cm: part 3 of 3 of this suite, with
## `tsymex_rfc0005_s8bi_remainder`, `tsymex_rfc0005_s8bi_remainder_b`. Split so
## that each part compiles and runs in under 60 s on the Windows legs (the
## whole file took 76 s).

import std/[unittest, strutils, re, sequtils, os, tables]
import nelli/symex
import nelli/smt/types
import nelli/smt/canonicalize

proc show(errs: seq[SymexErrorInfo]): string =
  var parts: seq[string]
  for e in errs: parts.add $e.kind & "/" & $e.severity & ": " & e.msg
  "[" & parts.join(", ") & "]"

template verdict(sut: untyped; label: string): SymexResult =
  let r = symexFind(sut, tLabel(label))
  checkpoint label & ": " & $r.status & " " & show(r.errors) & " witness=" &
             (if r.status == sxSat: $r.witness else: "-")
  r

# ---- item 1: raise sites behind a while guard's short circuit ---------------

type M = distinct int
proc `==`(a, b: M): bool {.borrow.}

# RFC-0005 batch 5: a size argument is evaluated once. In a `while` guard
# `parseAtomicOperand` hoists nothing, and `parseExpr` leaves a closure
# call inline: the length guard's two branches and the length itself each
# applied `f` (and `initTable`'s size guard, twice, anywhere).

proc nsGuardOnce(x: int) =
  if x < 0 or x > 1000: return
  var cnt = 0
  let f = proc (k: int): int =
    inc cnt
    k
  var it = 0
  while newSeq[int](f(x)).len > 2 and it < 1:
    inc it
  if cnt > 2: symexTarget("bi_ns_guard_once")

proc nsGuardTwo(x: int) =
  if x < 0 or x > 1000: return
  var cnt = 0
  let f = proc (k: int): int =
    inc cnt
    k
  var it = 0
  while newSeq[int](f(x)).len > 2 and it < 1:
    inc it
  if cnt == 2: symexTarget("bi_ns_guard_two")

proc initSizeOnce(x: int) =
  if x < 0 or x > 1000: return
  var cnt = 0
  let f = proc (k: int): int =
    inc cnt
    k
  let t = initTable[int, int](f(x))
  if cnt != 1 or t.len != 0: symexTarget("bi_init_size_once")

# ---- item 4: set literals ---------------------------------------------------

type E = enum eA, eB, eC, eD
const Ident = {'a'..'z', '_'}

proc setNotin(c: char) =
  if c notin {'a'..'z', '_'} and (c == 'y' or c == '_'):
    symexTarget("bi_set_notin")

proc setNotinSat(c: char) =
  if c notin {'a'..'z', '_'} and (c == '{' or c == 'a'):
    symexTarget("bi_set_notin_sat")

proc setNotinNone(c: char) =
  if c notin {'\0'..'\255'}:
    symexTarget("bi_set_notin_none")

proc setInInt(x: int) =
  if x in {1, 3, 5..7} and x > 5:
    symexTarget("bi_set_in_int")

proc setInIntOut(x: int) =
  if x in {1, 3} and (x < 0 or x > 255):
    symexTarget("bi_set_in_int_out")

proc setInEnum(e: E) =
  if e in {eA, eC..eD} and e != eA and e != eD:
    symexTarget("bi_set_in_enum")

proc setInEnumNo(e: E) =
  if e in {eA, eC..eD} and e == eB:
    symexTarget("bi_set_in_enum_no")

proc setConst(c: char) =
  if c in Ident and c notin {'b'..'z'} and c != '_':
    symexTarget("bi_set_const")

proc setU8(u: uint8) =
  if u in {1'u8, 200'u8} and u > 100'u8:
    symexTarget("bi_set_u8")

proc setBool(b: bool) =
  if b in {true}:
    symexTarget("bi_set_bool")

const NoChars: set[char] = {}

proc setEmpty(c: char) =
  if c in NoChars:
    symexTarget("bi_set_empty")

proc setKeyIdx(s: string; i: int) =
  # A raising key is read once, before membership.
  try:
    if s[i] in {'a', 'b'}:
      symexTarget("bi_set_key_idx")
  except IndexDefect:
    discard

proc setWhile(s: string) =
  var i = 0
  while i < s.len and s[i] notin {'0'..'9'}:
    inc i
  if s.len == 3 and i == 2:
    symexTarget("bi_set_while")

proc setValue(c: char) =
  let ss: set[char] = {'a', 'b'}
  if c in ss:
    symexTarget("bi_set_value")

# ---- item 5: recursive definitions carry fuel -------------------------------

proc stripComments(src: string): string =
  ## Drop `#` comments (outside string and char literals) so the scan sees
  ## code only.
  var inStr = false
  var i = 0
  while i < src.len:
    let c = src[i]
    if inStr:
      result.add c
      if c == '\\' and i + 1 < src.len:
        result.add src[i + 1]
        inc i
      elif c == '"':
        inStr = false
    elif c == '"':
      inStr = true
      result.add c
    elif c == '\'' and i + 2 < src.len and src[i + 2] == '\'':
      result.add src[i .. i + 2]
      i += 2
    elif c == '#':
      while i < src.len and src[i] != '\n': inc i
      continue
    else:
      result.add c
    inc i

proc matchParen(s: string; open: int): int =
  ## The index of the `)` closing the `(` at `open`, or -1.
  var depth = 0
  for k in open ..< s.len:
    if s[k] == '(': inc depth
    elif s[k] == ')':
      dec depth
      if depth == 0: return k
  -1

proc splitTopArgs(s: string): seq[string] =
  var depth = 0
  var cur = ""
  for c in s:
    if c in {'(', '['}: inc depth
    elif c in {')', ']'}: dec depth
    if c == ',' and depth == 0:
      result.add cur.strip
      cur = ""
    else:
      cur.add c
  if cur.strip.len > 0: result.add cur.strip

proc recFuelViolations(code: string; file: string): seq[string] =
  ## Every `defineRecFun[` call: a `fuel: Z3Int` parameter, a
  ## `fuel <= mkInt(0)` base case, and every recursive `self(..)` call
  ## passing `fuel - mkInt(1)` (directly or as `f1`, bound to it) last.
  ## The raw API (`Z3_mk_rec_func_decl` / `Z3_add_rec_def`) and SMT-LIB
  ## `define-fun-rec` are not to be used around it.
  for raw in ["Z3_mk_rec_func_decl", "Z3_add_rec_def", "define-fun-rec"]:
    if raw in code:
      result.add file & ": raw recursive definition `" & raw & "`"
  var at = code.find("defineRecFun[")
  while at >= 0:
    let open = code.find('(', code.find(']', at))
    let close = matchParen(code, open)
    if open < 0 or close < 0:
      result.add file & ": unparsable defineRecFun call"
      break
    let call = code[open .. close]
    let line = code[0 ..< at].count('\n') + 1
    let where = file & ":" & $line
    let lam = call.find("proc")
    let pOpen = call.find('(', lam)
    let pClose = matchParen(call, pOpen)
    if lam < 0 or pClose < 0:
      result.add where & ": no lambda body"
    else:
      let params = call[pOpen .. pClose]
      if "fuel: Z3Int" notin params:
        result.add where & ": no `fuel: Z3Int` parameter"
      let body = call[pClose + 1 .. ^1]
      if "fuel <= mkInt(0)" notin body:
        result.add where & ": no `fuel <= mkInt(0)` base case"
      let f1Bound = "f1 = fuel - mkInt(1)" in body
      var selfAt = body.find("self(")
      var calls = 0
      while selfAt >= 0:
        inc calls
        let sOpen = selfAt + "self".len
        let sClose = matchParen(body, sOpen)
        let args = splitTopArgs(body[sOpen + 1 ..< sClose])
        let last = if args.len > 0: args[^1] else: ""
        if not (last == "fuel - mkInt(1)" or (last == "f1" and f1Bound)):
          result.add where & ": recursive call `self(" &
                     body[sOpen + 1 ..< sClose] & ")` does not pass " &
                     "`fuel - mkInt(1)` last"
        selfAt = body.find("self(", sClose)
      if calls == 0:
        result.add where & ": no recursive `self(..)` call found"
    at = code.find("defineRecFun[", close)

const srcRoot = currentSourcePath.parentDir() / ".." / "src"

suite "batch 5: a size argument is evaluated once":
  test "native: the guard applies f once per test":
    var cnt = 0
    let f = proc (k: int): int =
      inc cnt
      k
    var it = 0
    while newSeq[int](f(5)).len > 2 and it < 1:
      inc it
    check cnt == 2
    var c2 = 0
    let g = proc (k: int): int =
      inc c2
      k
    let t = initTable[int, int](g(5))
    check c2 == 1 and t.len == 0
  test "newSeq's length in a while guard":
    # Before: f applied three times per test, so cnt > 2 was sxSat and the
    # count Nim makes (2, at x = 5) sxUnsat.
    check verdict(nsGuardOnce, "bi_ns_guard_once").status == sxUnsat
    check verdict(nsGuardTwo, "bi_ns_guard_two").status == sxSat
  test "initTable's size":
    check verdict(initSizeOnce, "bi_init_size_once").status == sxUnsat

suite "S8bi (4): set literals in `in` / `notin`":
  test "notin over a char range and a char":
    check verdict(setNotin, "bi_set_notin").status == sxUnsat
    let r = verdict(setNotinSat, "bi_set_notin_sat")
    check r.status == sxSat
    check $r.witness == "('{',)"
  test "notin over every char":
    check verdict(setNotinNone, "bi_set_notin_none").status == sxUnsat
  test "in over ints and an int range":
    let r = verdict(setInInt, "bi_set_in_int")
    check r.status == sxSat
    check r.errors.len == 0
  test "a key outside the set's base range is not a member and does not raise":
    check verdict(setInIntOut, "bi_set_in_int_out").status == sxUnsat
  test "in over enum fields and an enum range":
    check verdict(setInEnum, "bi_set_in_enum").status == sxSat
    check verdict(setInEnumNo, "bi_set_in_enum_no").status == sxUnsat
  test "a const set":
    check verdict(setConst, "bi_set_const").status == sxSat
  test "unsigned elements":
    check verdict(setU8, "bi_set_u8").status == sxSat
  test "bool elements":
    check verdict(setBool, "bi_set_bool").status == sxSat
  test "the empty set":
    check verdict(setEmpty, "bi_set_empty").status == sxUnsat
  test "a raising key":
    check verdict(setKeyIdx, "bi_set_key_idx").status == sxSat
  test "notin in a while guard":
    check verdict(setWhile, "bi_set_while").status == sxSat
  test "a set-typed value (RFC-0005 S8bq: modelled)":
    # S8bi declined it, classified; S8bq models builtin `set[T]` values.
    let r = verdict(setValue, "bi_set_value")
    check r.status == sxSat
    check r.errors.len == 0

suite "S8bi (5): recursive definitions carry fuel":
  test "the scan rejects a definition without fuel":
    let bad = """
  let f = defineRecFun[Z3String, Z3String](ctx, "g",
    proc (self: Z3FuncDecl[(Z3String,), Z3String]; u: Z3String): Z3String =
      ite(len(u) == mkInt(0), u, self(substr(u, mkInt(1), len(u))))))
"""
    check recFuelViolations(bad, "fixture").len >= 3
    let noDecrease = """
  let f = defineRecFun[Z3String, Z3Int, Z3String](ctx, "g",
    proc (self: Z3FuncDecl[(Z3String, Z3Int), Z3String]; u: Z3String;
          fuel: Z3Int): Z3String =
      ite(fuel <= mkInt(0), u, self(u, fuel)))
"""
    check recFuelViolations(noDecrease, "fixture").len == 1
    check recFuelViolations("Z3_add_rec_def(c, f)", "fixture").len == 1
  test "the scan accepts a fueled definition":
    let good = """
  let f = defineRecFun[Z3String, Z3Int, Z3String](ctx, "g",
    proc (self: Z3FuncDecl[(Z3String, Z3Int), Z3String]; u: Z3String;
          fuel: Z3Int): Z3String =
      let f1 = fuel - mkInt(1)
      ite(fuel <= mkInt(0), u, self(substr(u, mkInt(1), len(u)), f1)))
"""
    check recFuelViolations(good, "fixture").len == 0
  test "every recursive definition under src/ carries fuel":
    var violations: seq[string]
    var defs = 0
    for path in walkDirRec(srcRoot):
      if not path.endsWith(".nim"): continue
      let code = stripComments(readFile(path))
      defs += code.count("defineRecFun[")
      violations.add recFuelViolations(code, path.relativePath(srcRoot))
    checkpoint violations.join("\n")
    check violations.len == 0
    check defs >= 4   # the two replace runs, `run` and `rep`
