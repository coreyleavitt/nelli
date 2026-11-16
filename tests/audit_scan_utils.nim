## Shared scan primitives for the source-level regression-audit test suites
## (the "house scan-and-marker technique" `tsymex_r6_n27_placeholder_read_
## audit.nim`'s header describes). Round-6 mechanical-debt slice: these two
## procs were byte-identical, independently copy-pasted, across five audit
## suites (`tsymex_r6_n27_placeholder_read_audit`, `tsymex_phase15_N2_
## kindgate_audit`, `tsymex_phase15_A2a_atomicir_audit`, `tsymex_phase15_A2a_
## chokepoint_audit`, `tsymex_r6_n36_raise_class_audit`). Extracted here so a
## future fix to either applies once instead of drifting across five copies.
##
## Deliberately NOT a home for every scan helper the audits use: each suite's
## other primitives (`fieldNameAt`, `routineVocabWordLenAt`, `matchesAt`, ...)
## look superficially similar but encode different word-boundary/marker rules
## for that suite's own vocabulary -- forcing them into one shared proc would
## couple suites that should stay independently editable. Only genuinely
## byte-identical pieces belong here.

import std/strutils

proc isCommentLine*(trimmed: string): bool =
  ## Nim `#`/`##` doc and ordinary comments both start with `#` once leading
  ## whitespace is stripped. Prose narrating a scanned token (an audit file's
  ## own header included) must never trip a scanner.
  trimmed.startsWith("#")

proc isIdentChar*(c: char): bool = c.isAlphaNumeric or c == '_'
  ## Word-boundary test shared by every audit's separator-aware identifier
  ## matching (so `.seqLenXyz`/`notSeqLen`-style near-misses never match a
  ## bare target-token scan).

# ---------------------------------------------------------------------------
# The runtime family: the one list every source audit of the walker reads.
# ---------------------------------------------------------------------------

import std/os

const
  smtSrcDir* = currentSourcePath().parentDir() / ".." / "src" / "nelli" / "smt"

  runtimeFamilyFiles* = [
    # The walker proper, and the file still textually included into it.
    "runtime.nim", "runtime_heap.nim",
    # Includes that became real modules (RFC-0016 D3c-3, -4, -5, -7).
    "runtime_exceptions.nim", "runtime_floats.nim", "runtime_closures.nim",
    "runtime_strings.nim",
    # Leaves that code moved into out of `runtime.nim` (RFC-0016 D3c-1, -2,
    # -6, -7): the shared value types, the run state, the sort-checked Z3
    # term builders, the heap algebra, and the string lowering support.
    "symval.nim", "walk_state.nim", "z3check.nim", "heap_model.nim",
    "string_lower_support.nim"]
    ## Every file that holds, or has held, code that was `runtime.nim`'s. A
    ## source audit that pins "the walker's sites of kind K" counts K over THIS
    ## set, never over a hand-picked subset: a file move then changes which
    ## file a site is in, not the total, and an audit written against the
    ## total does not break. A new leaf cut out of `runtime.nim` is added here,
    ## once, and every audit follows it. `tsymex_0016_d3_include_census`
    ## checks that no `runtime*.nim` and no named leaf is missing from it.

proc runtimeFamilySources*(exclude: openArray[string] = []):
    seq[tuple[label, path: string]] =
  ## (repo-relative label, path) for each family file, in list order, less any
  ## basename in `exclude` (an audit whose scope never covered a file says so
  ## at its own call site, with the reason). Read the files at test RUNTIME
  ## with `readFile` (never `staticRead`: MSVC's C2026 string-literal limit).
  for f in runtimeFamilyFiles:
    if f in exclude: continue
    result.add (label: "src/nelli/smt/" & f, path: smtSrcDir / f)

# ---------------------------------------------------------------------------
# Comment/string-blind source reading (RFC-0016 review round 4, Low findings).
# ---------------------------------------------------------------------------

proc codeOf*(text: string): string =
  ## `text` with every comment and every string/char literal body removed and
  ## line structure kept (one output line per input line, so a line index in
  ## the result is the same line in the source). A small lexer over the whole
  ## text, because a per-line scan cannot see state that spans lines. It
  ## understands: `#` line comments (doc comments included); nested `#[ ]#`
  ## and `##[ ]##` block comments, multi-line; `"..."` strings with
  ## backslash escapes; `"""..."""` triple-quoted strings, multi-line; raw
  ## strings (`r"..."`, any `ident"..."`) where a backslash escapes nothing
  ## and `""` is a quote; and the character literals `'"'`, `'\''`, `'\"'`
  ## (a `'` after an identifier character or digit is a numeric suffix, not a
  ## literal). Removed text leaves nothing behind (not a blank).
  var i = 0
  let n = text.len
  while i < n:
    let c = text[i]
    if c == '#':
      if i + 1 < n and text[i + 1] == '[' or
         (i + 2 < n and text[i + 1] == '#' and text[i + 2] == '['):
        let doc = text[i + 1] == '#'
        i += (if doc: 3 else: 2)
        var depth = 1
        while i < n and depth > 0:
          if text[i] == '#' and i + 1 < n and text[i + 1] == '[':
            inc depth
            i += 2
          elif text[i] == ']' and i + 1 < n and text[i + 1] == '#':
            dec depth
            i += 2
            if doc and depth == 0 and i < n and text[i] == '#': inc i
          else:
            if text[i] == '\n': result.add '\n'
            inc i
      else:
        while i < n and text[i] != '\n': inc i
    elif c == '"':
      if i + 2 < n and text[i + 1] == '"' and text[i + 2] == '"':
        i += 3
        while i < n:
          if text[i] == '"' and i + 2 < n and text[i + 1] == '"' and
             text[i + 2] == '"':
            i += 3
            while i < n and text[i] == '"': inc i   # `""""` closes on the last three
            break
          if text[i] == '\n': result.add '\n'
          inc i
      else:
        let raw = i > 0 and isIdentChar(text[i - 1])
        inc i
        while i < n and text[i] != '\n':
          if raw:
            if text[i] == '"':
              if i + 1 < n and text[i + 1] == '"': i += 2; continue
              inc i
              break
          else:
            if text[i] == '\\' and i + 1 < n and text[i + 1] != '\n':
              i += 2
              continue
            if text[i] == '"':
              inc i
              break
          inc i
    elif c == '\'' and (i == 0 or not (isIdentChar(text[i - 1]))):
      if i + 2 < n and text[i + 1] != '\\' and text[i + 2] == '\'':
        i += 3                                  # 'x', '"', '#'
      elif i + 3 < n and text[i + 1] == '\\':
        var j = i + 3                           # '\n', '\'', '\"', '\x41'...
        while j < n and j < i + 8 and text[j] != '\'' and text[j] != '\n': inc j
        if j < n and text[j] == '\'': i = j + 1
        else:
          result.add c
          inc i
      else:
        result.add c
        inc i
    else:
      result.add c
      inc i

proc stripLine*(line: string): string =
  ## One line's code: `codeOf` on that line alone. A line cannot know whether
  ## it sits inside a block comment or a triple-quoted string; a scan that must
  ## respect those goes through `codeOf` on the whole file and indexes lines.
  codeOf(line)

proc relImports*(text: string): seq[string] =
  ## The `./name` modules a file imports: `import ./a`, `import ./a as b`,
  ## `import ./a except x`, `import ./a, ./b` (also split over lines), the
  ## bracket form `import ./[a, b as c]` (also split over lines), a bare
  ## `import` whose list is on the indented lines below, and
  ## `from ./a import ...`. Comments and strings are not read.
  let lines = codeOf(text).splitLines
  var li = 0
  while li < lines.len:
    let t = lines[li].strip()
    inc li
    var rest = ""
    var isFrom = false
    if t == "import": rest = ""
    elif t.startsWith("import "): rest = t[7 .. ^1].strip()
    elif t.startsWith("from "):
      rest = t[5 .. ^1].strip()
      isFrom = true
    else: continue
    var specs: seq[string]
    if isFrom:
      let w = rest.splitWhitespace
      if w.len > 0: specs.add w[0]
    else:
      # continuation: an open `[`, a trailing `,`, or a bare `import`
      template depthOf(s: string): int =
        s.count('[') - s.count(']')
      while li < lines.len and
            (depthOf(rest) > 0 or rest.endsWith(",") or rest.len == 0):
        let nx = lines[li].strip()
        if rest.len == 0 and lines[li].len > 0 and lines[li][0] != ' ': break
        inc li
        rest.add " " & nx
      let ex = rest.find(" except ")
      if ex >= 0: rest = rest[0 ..< ex]
      var depth = 0
      var cur = ""
      var parts: seq[string]
      for c in rest:
        if c == '[': inc depth
        elif c == ']': dec depth
        if c == ',' and depth == 0:
          parts.add cur
          cur = ""
        else: cur.add c
      parts.add cur
      for p in parts:
        let q = p.strip()
        let lb = q.find("/[")
        if lb >= 0 and q.endsWith("]"):
          let dir = q[0 .. lb]
          for m in q[lb + 2 ..< q.len - 1].split(','):
            specs.add dir & m.strip()
        else: specs.add q
    for m in specs:
      var x = m.strip()
      let k = x.find(" as ")
      if k >= 0: x = x[0 ..< k]
      if x.startsWith("./"): result.add x[2 .. ^1]
