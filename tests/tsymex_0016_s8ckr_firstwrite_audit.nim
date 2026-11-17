## RFC-0016 S8ck-r (INF-04) -- permanent audit: the Nim 2.2.10 first-write
## leak shape does not come back under src/.
##
## Leak A (tests/asan/nim_firstwrite_leak.nim): Nim 2.2.10, stock and patched,
## leaks a variable's old value when
##
##   var x: T            # no initializer, T owns heap
##   for ...: x.add ...  # a write under a for/while/if/case/try
##   x = expr            # the first plain assignment at the declaring level
##
## sempass2 drops the nested write from the definitely-initialized set when
## the construct ends, marks `x = expr` a first write, and the assignment is
## compiled to a bitwise copy that never destroys what `x` held. nelli met it
## in `pcre_select.normalize` (1272 bytes under tsymex_phase15_S6b_regex) and
## works around it there with an initializer (`var nx: seq[Item[T]] = @[]`),
## which makes the declaration the first write. Until the toolchain is fixed,
## a recurrence anywhere under src/ fails this audit.
##
## The scan is a shape check over code read comment- and string-blind
## (`codeOf`), conservative by design: a `var` with a type and no initializer,
## whose type is not a plain scalar, written under a control-flow header and
## then plainly assigned at its own level. A line inside an open bracket (a
## named argument such as `guarded = guarded`) is not an assignment. A hit
## that is reviewed safe carries `[firstwrite-audited: <reason>]` on its
## declaration line; the fix is otherwise an initializer.
import std/[unittest, strutils, os, algorithm]
import audit_scan_utils

const
  srcDir = currentSourcePath().parentDir() / ".." / "src"
  auditMarker = "[firstwrite-audited: "
  scalarTypes = ["int", "int8", "int16", "int32", "int64", "uint", "uint8",
    "uint16", "uint32", "uint64", "float", "float32", "float64", "bool",
    "char", "byte", "Natural", "Positive", "pointer", "cint", "cuint",
    "csize_t", "BiggestInt"]
  ctlWords = ["if", "elif", "else", "for", "while", "case", "of", "try",
    "except", "finally", "when"]
  mutators = ["add", "incl", "insert", "setLen", "del", "delete", "excl",
    "clear", "mgetOrPut", "inc", "swap", "shrink", "reset"]

type Hit* = object
  file*: string
  declLine*, nestedLine*, assignLine*: int
  name*, ty*: string

proc indentOf(s: string): int =
  while result < s.len and s[result] == ' ': inc result

proc wordAt(s: string, i: int, w: string): bool =
  s.continuesWith(w, i) and (i == 0 or not isIdentChar(s[i - 1])) and
    (i + w.len >= s.len or not isIdentChar(s[i + w.len]))

proc writes(s, name: string): bool =
  ## `s` mutates or assigns `name`: `name = `, `name[..] = `, `name &= `,
  ## `name.add ...`, `add(name, ...)` and the other mutators.
  var i = 0
  while i < s.len:
    if wordAt(s, i, name):
      var j = i + name.len
      while j < s.len and s[j] == ' ': inc j
      if j < s.len:
        if s[j] == '=' and (j + 1 >= s.len or s[j + 1] != '='): return true
        if s.continuesWith("&=", j): return true
        if s[j] == '[':
          let e = s.find(']', j)
          if e > 0:
            var k = e + 1
            while k < s.len and s[k] == ' ': inc k
            if k < s.len and s[k] == '=' and (k + 1 >= s.len or s[k + 1] != '='):
              return true
        if s[j] == '.':
          var k = j + 1
          while k < s.len and s[k] == ' ': inc k
          for m in mutators:
            if wordAt(s, k, m): return true
      # `add(name` and friends
      var b = i - 1
      while b >= 0 and s[b] == ' ': dec b
      if b >= 0 and s[b] == '(':
        var a = b - 1
        while a >= 0 and isIdentChar(s[a]): dec a
        if s[a + 1 ..< b] in mutators: return true
    inc i
  false

proc plainAssign(s, name: string): bool =
  let t = s.strip(trailing = false)
  if not wordAt(t, 0, name): return false
  var j = name.len
  while j < t.len and t[j] == ' ': inc j
  j < t.len and t[j] == '=' and (j + 1 >= t.len or t[j + 1] != '=')

proc ctlHeader(s: string): bool =
  ## A line that opens a control-flow construct. A condition may continue on
  ## the next lines (deeper-indented), so the colon is not required here.
  let t = s.strip()
  for w in ctlWords:
    if wordAt(t, 0, w): return true
  false

proc bracketDelta(s: string): int =
  for c in s:
    if c in {'(', '[', '{'}: inc result
    elif c in {')', ']', '}'}: dec result

proc heapType(ty: string): bool =
  let t = ty.strip()
  t notin scalarTypes and not t.startsWith("set[") and
    not t.startsWith("range[")

proc scanFirstWrite*(file, text: string): seq[Hit] =
  let lines = codeOf(text).splitLines()
  let raw = text.splitLines()
  # bracket depth at the START of each line, so continuation lines are known
  var depthAt = newSeq[int](lines.len)
  var d = 0
  for i, l in lines:
    depthAt[i] = d
    d = max(0, d + bracketDelta(l))
  for i, l in lines:
    if depthAt[i] > 0: continue
    let t = l.strip()
    if not t.startsWith("var "): continue
    let body = t[4 .. ^1].strip()
    let colon = body.find(':')
    if colon <= 0 or '=' in body: continue
    let name = body[0 ..< colon].strip()
    if name.len == 0 or not name.allCharsInSet(IdentChars): continue
    let ty = body[colon + 1 .. ^1].strip()
    if ty.len == 0 or not heapType(ty): continue
    if i < raw.len and auditMarker in raw[i]: continue
    let ind = indentOf(l)
    var nested = 0
    var ctl: seq[int]
    for j in i + 1 ..< min(lines.len, i + 600):
      let s = lines[j]
      if s.strip().len == 0: continue
      let sind = indentOf(s)
      if sind < ind: break
      if depthAt[j] > 0: continue
      while ctl.len > 0 and ctl[^1] >= sind: discard ctl.pop()
      if ctlHeader(s):
        let after = s.split(':', 1)
        if after.len == 2 and writes(after[1], name) and nested == 0:
          nested = j + 1
        ctl.add sind
        continue
      if ctl.len > 0:
        if nested == 0 and writes(s, name): nested = j + 1
        continue
      if plainAssign(s, name):
        if nested > 0:
          result.add Hit(file: file, declLine: i + 1, nestedLine: nested,
                         assignLine: j + 1, name: name, ty: ty)
        break

proc srcFiles(): seq[tuple[label, path: string]] =
  for p in walkDirRec(srcDir):
    if p.endsWith(".nim"):
      result.add (label: "src/" & p.relativePath(srcDir), path: p)
  result.sort(proc (a, b: tuple[label, path: string]): int = cmp(a.label, b.label))

const
  normalizeFixed = "    var nx: seq[Item[T]] = @[]"
  normalizeBare = "    var nx: seq[Item[T]]"

suite "S8ck-r: the Nim 2.2.10 first-write leak shape stays out of src/":

  test "no first-write leak shape under src/":
    var hits: seq[Hit]
    var files = 0
    for (label, path) in srcFiles():
      hits.add scanFirstWrite(label, readFile(path))
      inc files
    checkpoint("scanned " & $files & " files")
    for h in hits:
      checkpoint(h.file & ":" & $h.declLine & ": var " & h.name & ": " & h.ty &
        " | nested write " & $h.nestedLine & " | first-write assign " &
        $h.assignLine & " -- give the declaration an initializer")
    check hits.len == 0
    check files > 100

  test "fixed case: pcre_select.normalize without its initializer is caught":
    let path = srcDir / "nelli" / "smt" / "pcre_select.nim"
    let text = readFile(path)
    check text.count(normalizeFixed & "\n") == 1
    check scanFirstWrite("pcre_select.nim", text).len == 0
    let bare = text.replace(normalizeFixed & "\n", normalizeBare & "\n")
    let hits = scanFirstWrite("pcre_select.nim", bare)
    check hits.len == 1
    check hits.len == 1 and hits[0].name == "nx"

  test "fixed cases: the reproducer's shapes, and what is not the shape":
    let repro = readFile(currentSourcePath().parentDir() / "asan" /
                         "nim_firstwrite_leak.nim")
    var names: seq[int]
    for h in scanFirstWrite("nim_firstwrite_leak.nim", repro):
      names.add h.declLine
    check names.len == 2   # leaksAdd and leaksIf; `fixed` is clean
    # a named argument on a continuation line is not an assignment
    check scanFirstWrite("na.nim",
      "proc p() =\n  var g: seq[int]\n  for x in 0..2:\n    g.add x\n" &
      "  q(1,\n    g = g)\n").len == 0
    # a write under a condition that continues on the next line is nested
    check scanFirstWrite("ml.nim",
      "proc p(a: bool) =\n  var g: seq[int]\n  if a:\n    g = @[1]\n" &
      "  elif a and\n       a:\n    g = @[2]\n  else:\n    return\n").len == 0
    # a scalar is not the shape
    check scanFirstWrite("sc.nim",
      "proc p() =\n  var g: int\n  for x in 0..2:\n    inc g\n  g = 3\n").len == 0
    # the marker exempts a reviewed hit
    check scanFirstWrite("mk.nim",
      "proc p() =\n  var g: seq[int]  # [firstwrite-audited: test]\n" &
      "  if true: g.add 1\n  g = @[]\n").len == 0
    check scanFirstWrite("mk.nim",
      "proc p() =\n  var g: seq[int]\n  if true: g.add 1\n  g = @[]\n").len == 1
