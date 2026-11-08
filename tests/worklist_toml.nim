## RFC-0016 section 8.2: the work list is data. A flat TOML reader (arrays of
## tables; string and string-array fields only), the row/table model, and the
## renderer that turns the data back into section 5's tables.
##
## Shared by `scripts/render_worklist.nim` (write and check modes) and
## `tests/tsymex_0016_ids.nim` (the id join and the staleness check). It reads
## the TOML, never the markdown; the markdown is only the render target.
import std/[strutils, tables, sets]

type
  WTable* = object
    name*: string               ## the marker id: `worklist:begin <name>`
    columns*, fields*: seq[string]   ## header texts, and the row field each shows

  WRow* = object
    str*: Table[string, string]
    arr*: Table[string, seq[string]]

  Worklist* = object
    tables*: seq[WTable]
    rows*: seq[WRow]            ## file order is render order

const
  states* = ["open", "closed", "merged", "moved", "never"]
  rowStrKeys = ["id", "table", "title", "class", "state", "note", "slice",
                "home", "source", "evidence", "cause", "moves", "why",
                "never_reason", "sha"]
  rowArrKeys = ["cells", "pins", "aliases"]
  tableFieldKeys* = ["id", "title", "class", "home", "source", "evidence",
                     "cause", "moves", "why", "status"]

func get*(r: WRow; k: string): string = r.str.getOrDefault(k, "")
func list*(r: WRow; k: string): seq[string] = r.arr.getOrDefault(k, @[])
func id*(r: WRow): string = r.get("id")

func stateWord*(r: WRow): string =
  ## The state's base word: `owned:RFC-0014` is "owned".
  let s = r.get("state")
  if s.startsWith("owned:"): "owned" else: s

# --- the reader ------------------------------------------------------------

proc unq(s: string; i: var int; where: string): string =
  ## Reads a basic string starting at s[i] == '"'; leaves i past the closer.
  doAssert i < s.len and s[i] == '"', where & ": expected a string"
  inc i
  while i < s.len:
    case s[i]
    of '"': inc i; return
    of '\\':
      inc i
      doAssert i < s.len, where & ": dangling escape"
      case s[i]
      of '\\': result.add '\\'
      of '"': result.add '"'
      of 't': result.add '\t'
      of 'n': result.add '\n'
      else: doAssert false, where & ": unknown escape \\" & s[i]
      inc i
    else:
      result.add s[i]; inc i
  doAssert false, where & ": unterminated string"

proc skipWs(s: string; i: var int) =
  while i < s.len and s[i] in {' ', '\t'}: inc i

proc parseWorklist*(text: string; file = "worklist.toml"): Worklist =
  ## Fails (doAssert) on anything outside the flat subset or an unknown key,
  ## so a typo in a field name cannot silently drop data.
  var kind = ""
  var curT: WTable
  var curR: WRow
  proc flush(w: var Worklist) =
    if kind == "table": w.tables.add curT
    elif kind == "row": w.rows.add curR
    curT = WTable(); curR = WRow(); kind = ""
  var n = 0
  for raw in text.splitLines():
    inc n
    let where = file & ":" & $n
    let line = raw.strip()
    if line.len == 0 or line.startsWith("#"): continue
    if line == "[[table]]" or line == "[[row]]":
      flush(result); kind = line[2 .. ^3]; continue
    doAssert kind.len > 0, where & ": a key before any [[table]] or [[row]]"
    let eq = line.find('=')
    doAssert eq > 0, where & ": expected key = value"
    let key = line[0 ..< eq].strip()
    var i = eq + 1
    skipWs(line, i)
    var sval = ""
    var aval: seq[string]
    var isArr = false
    if i < line.len and line[i] == '[':
      isArr = true
      inc i
      while true:
        skipWs(line, i)
        doAssert i < line.len, where & ": unterminated array"
        if line[i] == ']': inc i; break
        aval.add unq(line, i, where)
        skipWs(line, i)
        if i < line.len and line[i] == ',': inc i
    else:
      sval = unq(line, i, where)
    skipWs(line, i)
    doAssert i == line.len or line[i] == '#', where & ": trailing text"
    if kind == "table":
      case key
      of "name": doAssert not isArr; curT.name = sval
      of "columns": doAssert isArr; curT.columns = aval
      of "fields": doAssert isArr; curT.fields = aval
      else: doAssert false, where & ": unknown table key " & key
    else:
      if key in rowStrKeys:
        doAssert not isArr, where & ": " & key & " is a string"
        curR.str[key] = sval
      elif key in rowArrKeys:
        doAssert isArr, where & ": " & key & " is an array"
        curR.arr[key] = aval
      else: doAssert false, where & ": unknown row key " & key
  flush(result)

proc quote*(s: string): string =
  result = "\""
  for c in s:
    case c
    of '\\': result.add "\\\\"
    of '"': result.add "\\\""
    of '\t': result.add "\\t"
    else: result.add c
  result.add '"'

# --- validation ------------------------------------------------------------

proc validate*(w: Worklist): seq[string] =
  ## Structural problems of the data itself (one message each).
  var names = initHashSet[string]()
  for t in w.tables:
    if t.name.len == 0: result.add "a [[table]] has no name"
    if t.name in names: result.add "table " & t.name & " is listed twice"
    names.incl t.name
    if t.columns.len != t.fields.len or t.columns.len == 0:
      result.add "table " & t.name & ": columns and fields differ in length"
    for f in t.fields:
      if f notin tableFieldKeys:
        result.add "table " & t.name & ": unknown field " & f
  var ids = initHashSet[string]()
  var aliases = initHashSet[string]()
  for r in w.rows:
    let i = r.id
    if i.len == 0: result.add "a [[row]] has no id"
    if i in ids: result.add "id " & i & " is listed twice"
    ids.incl i
    if r.get("table") notin names:
      result.add i & ": table \"" & r.get("table") & "\" is not a [[table]]"
    let s = r.get("state")
    if not (s in states or (s.startsWith("owned:RFC-") and s.len == 14)):
      result.add i & ": state \"" & s & "\" is outside the vocabulary " &
                 "(open, closed, merged, moved, never, owned:RFC-NNNN)"
    if r.get("title").len == 0 and r.get("table") != "":
      discard   # tables without an Item column carry no title
  for r in w.rows:
    for a in r.list("aliases"):
      if a in ids: result.add r.id & ": alias " & a & " is also a row id"
      if a in aliases: result.add r.id & ": alias " & a & " is listed twice"
      aliases.incl a

# --- the render ------------------------------------------------------------

proc statusCell*(r: WRow): string =
  ## The last column: begins with the vocabulary word (section 5.0's rule).
  let note = r.get("note")
  let word =
    case r.stateWord
    of "open": ""
    of "owned": r.get("state")["owned:".len .. ^1]
    else: r.get("state")
  if r.stateWord == "open": return note
  if note.len == 0: return word
  if note[0] in {':', ';', ','}: word & note else: word & " " & note

proc cellOf(r: WRow; field: string): string =
  if field == "status": r.statusCell else: r.get(field)

func rowLine(cells: seq[string]): string =
  result = "|"
  for c in cells:
    result.add (if c.len == 0: " " else: " " & c & " ")
    result.add "|"

proc renderTable*(w: Worklist; t: WTable): string =
  ## The table's markdown lines (header, separator, rows) and one blank line.
  var lines = @[rowLine(t.columns), "|" & "---|".repeat(t.columns.len)]
  for r in w.rows:
    if r.get("table") != t.name: continue
    var cells: seq[string]
    for f in t.fields: cells.add cellOf(r, f)
    lines.add rowLine(cells)
  lines.join("\n") & "\n\n"

func beginMark*(name: string): string = "<!-- worklist:begin " & name & " -->"
func endMark*(name: string): string = "<!-- worklist:end " & name & " -->"

proc renderRfc*(rfc: string; w: Worklist): tuple[text: string; problems: seq[string]] =
  ## `rfc` with every marked region replaced by the render. A table with no
  ## marker pair, a marker pair with no table, or a stray marker is a problem.
  let lines = rfc.splitLines()
  var outp: seq[string]
  var seenT = initHashSet[string]()
  var i = 0
  while i < lines.len:
    let l = lines[i]
    if l.startsWith("<!-- worklist:begin ") and l.endsWith(" -->"):
      let name = l["<!-- worklist:begin ".len ..< l.len - 4]
      var j = i + 1
      while j < lines.len and lines[j] != endMark(name): inc j
      if j == lines.len:
        result.problems.add "marker " & name & " has no end marker"
        outp.add l; inc i; continue
      var tbl = -1
      for k, t in w.tables:
        if t.name == name: tbl = k
      if tbl < 0:
        result.problems.add "marker " & name & " names no [[table]]"
        for k in i .. j: outp.add lines[k]
      else:
        if name in seenT: result.problems.add "marker " & name & " appears twice"
        seenT.incl name
        outp.add l
        outp.add w.renderTable(w.tables[tbl]).splitLines()[0 .. ^2]
        outp.add lines[j]
      i = j + 1
    else:
      if l.startsWith("<!-- worklist:end "):
        result.problems.add "stray end marker: " & l
      outp.add l; inc i
  for t in w.tables:
    if t.name notin seenT:
      result.problems.add "table " & t.name & " has no marker pair in the RFC"
  result.text = outp.join("\n")

proc lineDiff*(have, want: string; limit = 30): string =
  ## `- line` for what the committed file has, `+ line` for what the render has.
  let a = have.splitLines()
  let b = want.splitLines()
  var n = 0
  var i = 0
  while (i < a.len or i < b.len) and n < limit:
    let x = if i < a.len: a[i] else: "<end>"
    let y = if i < b.len: b[i] else: "<end>"
    if x != y:
      result.add "line " & $(i + 1) & "\n- " & x[0 ..< min(x.len, 160)] &
                 "\n+ " & y[0 ..< min(y.len, 160)] & "\n"
      inc n
    inc i
