## Phase 15 — Cluster S, cycle S6a: standalone Nim-regex → Z3-regex parser.
##
## A **self-contained** module — NO walker (`runtime.nim`) / `symex.nim`
## dependency, NO Z3 solving. It translates a Nim `re"..."` pattern *string*
## into a `Z3Regex[Z3String]` combinator tree, built on the `z3/regex`
## primitives. Walker integration (`match`/`find` interception) is S6b.
##
## ## Byte-faithful model (ADR-0006)
##
## Consistent with Cluster S's byte-faithful (≤ 0xFF) string model, character
## classes operate over **bytes**:
##   * `.`  → any single byte: `range('\x00', '\xFF')` (NOT `mkRegexAllChar`,
##           which over a full-Unicode basis would admit codepoints > 0xFF that
##           do not round-trip to a Nim byte). The byte-range `.` keeps `.`
##           inside the same ≤0xFF alphabet as every other construct.
##   * `[a-z]` → `range("a", "z")`.
##   * `\d`  → `range("0", "9")`.
##   * `\w`  → union of `[A-Za-z0-9_]`.
##   * `\s`  → union of ` \t\n\r\f\v` (the standard PCRE whitespace set).
##
## ## Result idiom
##
## The repo has **no `results` package** dependency (grep: 0 hits). Matching the
## codebase's `isOk`-duck-typed convention (`engine/eval.nim`, `fuzz.nim`), the
## parser returns a small `RegexParseResult` object exposing `isOk: bool`, the
## parsed `regex` (valid only when `isOk`), and an `error` message (descriptive,
## suitable to build a classified `seUnsupportedRegex` error in S6b).
##
## ## Grammar / precedence
##
## Recursive-descent over the pattern, lowest-to-highest binding:
##   alternation `|`  <  concatenation  <  quantifier (`*` `+` `?` `{n,m}`)
##   <  atom (`literal` `.` `[...]` `(...)` `\<esc>`).
## Escapes `\.` `\*` `\(` … are literal; `\d` `\w` `\s` are classes.

import std/strutils
import z3/regex
import z3/strings  # mkString (for byte-exact range endpoints)
import z3/context  # Z3Context
import z3/error    # checkErr (expanded by the regex varargs templates)
import z3/ffi      # FFI symbols referenced by the varargs template bodies

type
  RegexParseResult* = object
    ## `isOk`-duck-typed result (repo convention; no `results` dep).
    ## `regex` is meaningful only when `isOk`; `error` only when not.
    isOk*: bool
    regex*: Z3Regex[Z3String]
    error*: string

proc ok(r: Z3Regex[Z3String]): RegexParseResult =
  RegexParseResult(isOk: true, regex: r)

proc err(msg: string): RegexParseResult =
  RegexParseResult(isOk: false, error: msg)

# ---------------------------------------------------------------------------
# Byte-faithful char helpers
# ---------------------------------------------------------------------------

proc byteStr(b: int): Z3String =
  ## A single-byte Z3 string for a 0..255 codepoint (byte-exact endpoint).
  mkString($char(b))

proc byteRange(lo, hi: int): Z3Regex[Z3String] =
  ## `[lo-hi]` over bytes — uses the `Z3String`-typed `range` so endpoints
  ## may be any byte 0x00..0xFF (the `(string, string)` overload asserts a
  ## single ASCII codepoint and would reject 0x80..0xFF).
  range(byteStr(lo), byteStr(hi))

proc singleByte(c: char): Z3Regex[Z3String] =
  mkRegex(mkString($c))

const
  whitespaceBytes = [' ', '\t', '\n', '\r', '\f', '\v']

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

type
  Parser = object
    s: string
    i: int
    failed: bool
    errMsg: string

proc fail(p: var Parser, msg: string) =
  if not p.failed:
    p.failed = true
    p.errMsg = msg

proc atEnd(p: Parser): bool = p.i >= p.s.len
proc peek(p: Parser): char = (if p.atEnd: '\0' else: p.s[p.i])
proc peekAt(p: Parser, k: int): char =
  (if p.i + k >= p.s.len: '\0' else: p.s[p.i + k])

# forward decls
proc parseAlternation(p: var Parser): Z3Regex[Z3String]

proc classFor(p: var Parser, c: char): Z3Regex[Z3String] =
  ## `\d` `\w` `\s` character-class shorthands (byte-faithful unions).
  case c
  of 'd':
    byteRange(ord('0'), ord('9'))
  of 'w':
    union(byteRange(ord('A'), ord('Z')),
          byteRange(ord('a'), ord('z')),
          byteRange(ord('0'), ord('9')),
          singleByte('_'))
  of 's':
    var parts: seq[Z3Regex[Z3String]]
    for ch in whitespaceBytes:
      parts.add singleByte(ch)
    union(parts)
  else:
    p.fail("unsupported escape class: \\" & c)
    mkRegexEmpty[Z3String]()

proc parseEscape(p: var Parser): Z3Regex[Z3String] =
  ## Called with `p.i` pointing at the backslash.
  inc p.i  # consume '\'
  if p.atEnd:
    p.fail("dangling backslash at end of pattern")
    return mkRegexEmpty[Z3String]()
  let c = p.peek
  inc p.i
  case c
  of '1', '2', '3', '4', '5', '6', '7', '8', '9':
    p.fail("backreference \\" & c & " is not supported (seUnsupportedRegex)")
    mkRegexEmpty[Z3String]()
  of 'd', 'w', 's':
    p.classFor(c)
  else:
    # \. \* \( \\ etc — literal escaped char.
    singleByte(c)

proc parseCharClass(p: var Parser): Z3Regex[Z3String] =
  ## `[...]` — called with `p.i` at the opening `[`.
  inc p.i  # consume '['
  var negated = false
  if p.peek == '^':
    negated = true
    inc p.i
  var parts: seq[Z3Regex[Z3String]]
  var sawClose = false
  while not p.atEnd:
    let c = p.peek
    if c == ']':
      inc p.i
      sawClose = true
      break
    if c == '\\':
      inc p.i
      if p.atEnd:
        p.fail("dangling backslash in character class")
        return mkRegexEmpty[Z3String]()
      let ec = p.peek
      inc p.i
      case ec
      of 'd': parts.add byteRange(ord('0'), ord('9'))
      of 'w':
        parts.add byteRange(ord('A'), ord('Z'))
        parts.add byteRange(ord('a'), ord('z'))
        parts.add byteRange(ord('0'), ord('9'))
        parts.add singleByte('_')
      of 's':
        for ch in whitespaceBytes: parts.add singleByte(ch)
      else:
        parts.add singleByte(ec)
      continue
    # range a-z (when not the last char before ']')
    if p.peekAt(1) == '-' and p.peekAt(2) != ']' and p.peekAt(2) != '\0':
      let lo = c
      let hi = p.peekAt(2)
      p.i += 3
      parts.add byteRange(ord(lo), ord(hi))
    else:
      parts.add singleByte(c)
      inc p.i
  if not sawClose:
    p.fail("unterminated character class '['")
    return mkRegexEmpty[Z3String]()
  if parts.len == 0:
    p.fail("empty character class '[]'")
    return mkRegexEmpty[Z3String]()
  var cls = (if parts.len == 1: parts[0] else: union(parts))
  if negated:
    # [^...] — complement, intersected with "single byte" so it still
    # matches exactly one byte (complement alone admits any-length seqs).
    cls = intersect(complement(cls), byteRange(0, 255))
  cls

proc parseGroup(p: var Parser): Z3Regex[Z3String] =
  ## `(...)`, `(?:...)`, and the rejected `(?=...)`/`(?!...)`/`(?P<...>...)`.
  inc p.i  # consume '('
  if p.peek == '?':
    let q = p.peekAt(1)
    case q
    of ':':
      p.i += 2  # non-capturing group — transparent
    of '=', '!':
      p.fail("lookahead (?" & q & "...) is not supported (seUnsupportedRegex)")
      return mkRegexEmpty[Z3String]()
    of 'P', '<', '\'':
      p.fail("named group (?" & q & "...) is not supported (seUnsupportedRegex)")
      return mkRegexEmpty[Z3String]()
    else:
      p.fail("unsupported group flag (?" & q & "...) (seUnsupportedRegex)")
      return mkRegexEmpty[Z3String]()
  let inner = p.parseAlternation()
  if p.failed:
    return mkRegexEmpty[Z3String]()
  if p.peek != ')':
    p.fail("unterminated group '('")
    return mkRegexEmpty[Z3String]()
  inc p.i  # consume ')'
  inner  # capturing groups are transparent for language membership

proc parseAtom(p: var Parser): Z3Regex[Z3String] =
  let c = p.peek
  case c
  of '.':
    inc p.i
    byteRange(0, 255)  # byte-faithful '.' (any single byte)
  of '[':
    p.parseCharClass()
  of '(':
    p.parseGroup()
  of '\\':
    p.parseEscape()
  else:
    inc p.i
    singleByte(c)

proc parseQuantified(p: var Parser): Z3Regex[Z3String] =
  ## atom followed by an optional quantifier `* + ? {n,m}`.
  var atom = p.parseAtom()
  if p.failed: return mkRegexEmpty[Z3String]()
  let c = p.peek
  case c
  of '*':
    inc p.i
    star(atom)
  of '+':
    inc p.i
    plus(atom)
  of '?':
    inc p.i
    option(atom)
  of '{':
    # {n} / {n,} / {n,m}
    let save = p.i
    inc p.i
    var loStr = ""
    while p.peek in {'0'..'9'}: loStr.add p.peek; inc p.i
    if loStr.len == 0:
      # not a quantifier — treat '{' as a literal (restore)
      p.i = save
      return atom
    var hiStr = loStr
    var hasComma = false
    if p.peek == ',':
      hasComma = true
      inc p.i
      hiStr = ""
      while p.peek in {'0'..'9'}: hiStr.add p.peek; inc p.i
    if p.peek != '}':
      p.i = save
      return atom
    inc p.i  # consume '}'
    let lo = parseInt(loStr)
    # CR-10: cuint is 32-bit; Z3_mk_re_loop / power take cuint bounds. A
    # repetition count ≥ 2^32 would silently truncate, producing a regex with
    # WRONG bounds (potential false UNSAT/SAT).  Guard: if `lo` or `hi` exceeds
    # high(cuint) treat the repetition as unsupported → honest sxUnknown.
    if lo > int(high(cuint)):
      p.fail("repetition lower bound " & loStr & " exceeds 2^32-1; " &
             "unsupported (seUnsupportedRegex)")
      return mkRegexEmpty[Z3String]()
    if hasComma and hiStr.len == 0:
      # {n,} — n or more.
      concat(power(atom, lo), star(atom))
    else:
      let hi = parseInt(hiStr)
      if hi > int(high(cuint)):
        p.fail("repetition upper bound " & hiStr & " exceeds 2^32-1; " &
               "unsupported (seUnsupportedRegex)")
        return mkRegexEmpty[Z3String]()
      if hi < lo:
        p.fail("invalid counted repetition {n,m} with m < n")
        return mkRegexEmpty[Z3String]()
      loop(atom, lo, hi)
  else:
    atom

proc parseConcat(p: var Parser): Z3Regex[Z3String] =
  var parts: seq[Z3Regex[Z3String]]
  while not p.atEnd and p.peek != '|' and p.peek != ')':
    parts.add p.parseQuantified()
    if p.failed: return mkRegexEmpty[Z3String]()
  if parts.len == 0:
    mkRegex(mkString(""))  # empty concatenation matches the empty string
  elif parts.len == 1:
    parts[0]
  else:
    concat(parts)

proc parseAlternation(p: var Parser): Z3Regex[Z3String] =
  var branches: seq[Z3Regex[Z3String]]
  branches.add p.parseConcat()
  if p.failed: return mkRegexEmpty[Z3String]()
  while p.peek == '|':
    inc p.i
    branches.add p.parseConcat()
    if p.failed: return mkRegexEmpty[Z3String]()
  if branches.len == 1:
    branches[0]
  else:
    union(branches)

proc parseNimRegexToZ3Regex*(pattern: string): RegexParseResult =
  ## Translate a Nim `re"..."` pattern string into a `Z3Regex[Z3String]`.
  ##
  ## Requires a current Z3 context (`newContext()`); the byte-faithful AST is
  ## built against it. Returns `RegexParseResult(isOk: true, regex: …)` on
  ## success, or `isOk: false` with a descriptive `error` for unsupported
  ## constructs (backreferences, lookahead, named groups) and malformed input.
  var p = Parser(s: pattern, i: 0)
  let r = p.parseAlternation()
  if p.failed:
    return err(p.errMsg)
  if not p.atEnd:
    # leftover usually means an unbalanced ')'.
    return err("unexpected trailing input near position " & $p.i &
               " (unbalanced ')'?)")
  ok(r)
