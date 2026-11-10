## RFC-0016 K2a (section 8.2, the rule for introducing an axis): the dispatch
## census, as a test over the sites K2-s (`scripts/census-k2.sh`) counts.
##
## Five kinds of site are counted:
##   nimcase      every `case <expr>.kind` in `src/nelli/**/*.nim` whose subject
##                is a NimNode (see "NimNode cases" below), classified by its
##                `else`; only the TRANSPARENT ones are sites (kind
##                `nimcase_transparent`);
##   survivors    every `Survivors(` literal in `src/nelli` (AUD-09);
##   degrade      every `Degrade(` literal in `src/nelli` (word boundary:
##                `allocDegrade(` and `lowerDegrade(` do not count);
##   bare_skip    every `skip(` call under `tests/` (`skipCell(` is another
##                identifier and is the recorded form);
##   platform     every platform arm (`defined(windows)`, `hostOS`, ...) in a
##                `tests/` file that never mentions `skipCell`: such a file
##                has no way to record that an arm did not run.
## The literal `case n.kind` total is still cross-checked against
## `scripts/census-k2.sh` (K2-s); it is no longer an allowlist kind.
##
## NimNode cases (RFC section 8.1, Constructs). A dispatch is found by text:
## a line holding `case <subject>.kind` (the subject is any dotted expression,
## not only `n`), whose first branch is an `of`. Its subject is a NimNode when
## a branch label names an `nnk*` member: the label is typed by the language,
## so it cannot be an IR, type or value enum. This replaces a `parseStmt` walk
## at compile time: that walk has no types either (it cannot tell a NimNode
## `.kind` from an `IRStmt` `.kind`), and it would run a 30k-line parse in the
## VM per file. The labels decide the type exactly where the parse could not.
## Branch columns follow Nim's layout rule: the first `of` sets the column;
## `of` and `else` at that column belong to the case; the first other line at
## or left of it ends it.
##
## The `else` disposition, by its body (comments dropped):
##   none         no `else`: the case lists its kinds (the `classOf` shape);
##   decline      the body calls a decline: `decline*`, `degrade`, `addError`,
##                `error(`, `raise`, `fail(`, `notInert`, `unlisted`,
##                `unsupported`, `quit(`, `assert false`;
##   sentinel     the whole body is one literal: `false`, `true`, `nil`,
##                `""`, `-1`, `none(..)`, a bare `return` or `break`, with an
##                optional `return ` / `result = ` in front. The test cannot
##                see the caller, so a sentinel carries its audited polarity
##                in a comment on its `else` lines (RFC-0016 K2F-4):
##                `# k2: fail-closed: <who reads it how>` (every caller takes
##                the literal as decline / unknown / may) or `# k2: n/a:
##                <why>` (a utility whose literal only means "no name" or
##                "not this idiom", and what follows is the exact path).
##                A sentinel with no tag, or with any other polarity, fails:
##                a fail-open sentinel is fixed, never listed. The tag lives
##                at the site, not in census.txt: it is a classification of
##                the caller contract, not owed work, so it stays out of the
##                debt ratchet (ceilings.txt);
##   transparent  anything else (`discard`, a recursion over the children, a
##                value computed from the node, a delegate): the node kind
##                falls through to whatever follows. Transparent is the
##                disposition section 8.1 forbids, so it is an allowlisted
##                finding: each one is a census entry tagged `[transparent]`,
##                and a new one is an unlisted site.
##
## The survivors, degrade and bare_skip kinds use K2-s's rules exactly (comment text after the first
## `#` is dropped; a hit needs a non-identifier character before it). The
## platform kind is K2a's own: K2-s does not count platform arms.
##
## The ratchet. `tests/0016-allowlist/census.txt` lists every site, one line
## `site<TAB>slice<TAB>reason`. A site is `kind:file:context`, where context is
## the comment-stripped trimmed line (a second identical line in one file gets
## `#2`, and so on), so a refactor that moves a line does not churn it. The test
## fails on
##   * an UNLISTED site: a new transparent NimNode case, `Survivors(`/`Degrade(` literal, bare
##     `skip(` or platform arm must be classified in the commit that adds it;
##   * a STALE entry: a listed site that no longer exists, so the list cannot
##     rot the other way;
##   * a duplicate entry, `UNASSIGNED` or an unknown slice id, or no reason.
## On Linux the K2-s kinds are also cross-checked against the totals
## `scripts/census-k2.sh` prints, when bash is on the PATH.
##
## K2a-fail (Wave 4) turns the bare `skip(` rows from listed into failing.
import std/[unittest, os, strutils, sequtils, sets, tables, algorithm,
            osproc]
import ./rfc0016_ids

const
  root = currentSourcePath().parentDir() / ".."
  allowPath = root / "tests" / "0016-allowlist" / "census.txt"
  rfcPath = root / "docs" / "rfc" / "0016-native-parity-hardening.md"
  scriptPath = root / "scripts" / "census-k2.sh"
  selfName = "tsymex_0016_k2a_census.nim"
  # Built by concatenation so this file's own text never matches a census rule.
  skTok = "ski" & "p("
  kinds = ["nimcase_transparent", "survivors", "degrade", "bare_skip", "platform"]

type SrcFile = tuple[path, text: string]  ## repo-relative, forward slashes

proc isIdent(c: char): bool = c in IdentChars

proc stripComment(line: string): string =
  let i = line.find('#')
  if i >= 0: line[0 ..< i] else: line

proc countTok(s, tok: string): int =
  ## Occurrences of `tok` not preceded by an identifier character.
  var i = 0
  while true:
    i = s.find(tok, i)
    if i < 0: break
    if i == 0 or not isIdent(s[i - 1]): inc result
    i += tok.len

proc countCaseNKind(s: string): int =
  ## The literal `case n.kind` (K2-s's `case_n_kind` row), kept for the
  ## cross-check against `scripts/census-k2.sh`.
  var i = 0
  while true:
    i = s.find("case", i)
    if i < 0: break
    let startOk = i == 0 or not isIdent(s[i - 1])
    var j = i + 4
    let blanksFrom = j
    while j < s.len and s[j] in {' ', '\t'}: inc j
    if startOk and j > blanksFrom and s.continuesWith("n.kind", j):
      let e = j + 6
      if e >= s.len or not isIdent(s[e]): inc result
    i += 4

type
  Disp = enum dNone = "none", dDecline = "decline", dSentinel = "sentinel",
              dTransparent = "transparent"
  NimCase = object
    line: int            ## 1-based line of the `case`
    subject, owner: string   ## the dotted subject; the enclosing routine
    disp: Disp
    audit: string        ## a sentinel's `k2:` tag text ("" when untagged)

const declineToks = ["decline", "degrade", "addError", "error(", "raise ",
                     "fail(", "notInert", "unlisted", "nsupported",
                     "wsUnlisted", "quit(", "assert false"]

proc indentOf(l: string): int =
  while result < l.len and l[result] == ' ': inc result

proc isSentinel(body: string): bool =
  var t = body.strip()
  for pre in ["return ", "result = "]:
    if t.startsWith(pre):
      t = t[pre.len .. ^1].strip()
      break
  if t in ["false", "true", "nil", "\"\"", "-1", "return", "break"]: return true
  t.startsWith("none(") and t.endsWith(")")

proc classifyElse(body: seq[string]; hasElse: bool): Disp =
  if not hasElse: return dNone
  var t = body.mapIt(it.strip()).join(" ").strip()
  if t.startsWith("else"): t = t[4 .. ^1].strip()
  if t.startsWith(":"): t = t[1 .. ^1].strip()
  for d in declineToks:
    if d in t: return dDecline
  if isSentinel(t): dSentinel else: dTransparent

proc routineAt(lines: seq[string]; i: int): string =
  for k in countdown(i, 0):
    let l = lines[k]
    for kw in ["proc ", "func ", "method ", "iterator ", "template ", "macro ",
               "converter "]:
      if l.startsWith(kw):
        var j = kw.len
        if j < l.len and l[j] == '`': inc j
        var e = j
        while e < l.len and (isIdent(l[e]) or l[e] == '`'): inc e
        return l[j ..< e]
  "?"

proc auditTag(line: string): string =
  ## The `k2:` tag in a raw line's comment, from `k2:` on; "" when none.
  let c = line.find('#')
  if c < 0: return ""
  let t = line.find("k2:", c)
  if t < 0: "" else: line[t .. ^1].strip()

const auditPolarities = ["fail-closed", "n/a"]
  ## RFC-0016 K2F-4. The polarities a sentinel may carry. `fail-open` is not
  ## one: such a sentinel is fixed in the commit that finds it.

proc auditProblem(c: NimCase; path: string): string =
  ## "" when `c` needs no audit or carries a valid one, else the failure.
  if c.disp != dSentinel: return ""
  let at = path & ":" & $c.line & " (case " & c.subject & ".kind in " &
           c.owner & ")"
  if c.audit.len == 0:
    return "unaudited sentinel else at " & at & ": tag it `# k2: " &
           "fail-closed: <how the caller reads it>` or `# k2: n/a: <why>`"
  let body = c.audit[3 .. ^1].strip()
  for p in auditPolarities:
    if body.startsWith(p & ":") and body[p.len + 1 .. ^1].strip().len > 0:
      return ""
  "sentinel else at " & at & " has tag `" & c.audit & "`: the polarity " &
    "must be fail-closed or n/a, then `:` and how the caller reads it"

proc caseSubject(s: string): string =
  ## The subject of a `case <subject>.kind` header on this (comment-free)
  ## line, or "". The subject has no blanks and ends at the `.kind`.
  var i = 0
  while true:
    i = s.find("case", i)
    if i < 0: return ""
    let startOk = i == 0 or s[i - 1] in {' ', '\t', '=', '('}
    var j = i + 4
    let from0 = j
    while j < s.len and s[j] in {' ', '\t'}: inc j
    if startOk and j > from0:
      var e = j
      while e < s.len and s[e] notin {' ', '\t', ':'}: inc e
      let word = s[j ..< e]
      if word.endsWith(".kind") and word.len > 5:
        let rest = s[e .. ^1].strip()
        if rest.len == 0 or rest == ":":
          return word[0 .. ^6]
    i += 4

proc nimCases(text: string): seq[NimCase] =
  ## Every `case <expr>.kind` of the file whose labels name `nnk*` members.
  let raw = text.splitLines()
  let lines = raw.mapIt(stripComment(it).strip(
    leading = false, chars = {'\r', ' ', '\t'}))
  for i in 0 ..< lines.len:
    let subj = caseSubject(lines[i])
    if subj.len == 0: continue
    var j = i + 1
    while j < lines.len and lines[j].strip().len == 0: inc j
    if j >= lines.len or not lines[j].strip().startsWith("of "): continue
    let col = indentOf(lines[j])
    var labels: seq[string]
    var elseBody: seq[string]
    var hasElse = false
    var audit = ""
    var cur = ""
    var k = j
    while k < lines.len:
      let t = lines[k]
      if t.strip().len == 0:
        # A comment-only line inside the `else` body (indented past it).
        if cur == "else" and indentOf(raw[k]) > col: audit.add auditTag(raw[k])
        inc k
        continue
      let ind = indentOf(t)
      let st = t.strip()
      if ind < col: break
      if ind == col:
        if st.startsWith("of "):
          cur = "of"
          var lab = st
          while lab.endsWith(",") and k + 1 < lines.len:
            inc k
            lab.add " " & lines[k].strip()
          labels.add lab
        elif st.startsWith("else"):
          cur = "else"
          hasElse = true
          elseBody = @[st]
          audit.add auditTag(raw[k])
        else: break
      elif cur == "else":
        elseBody.add st
        audit.add auditTag(raw[k])
      inc k
    if labels.anyIt(it.contains("nnk")):
      result.add NimCase(line: i + 1, subject: subj,
                         owner: routineAt(lines, i),
                         disp: classifyElse(elseBody, hasElse), audit: audit)

const platformToks = ["defined(windows)", "defined(linux)", "defined(macosx)",
                      "defined(posix)", "defined(mingw)", "defined(vcc)",
                      "defined(msvc)", "defined(bsd)", "defined(unix)",
                      "hostOS"]

proc countPlatform(s: string): int =
  for t in platformToks:
    result += countTok(s, t)

proc context(line: string): string =
  stripComment(line).strip().replace('\t', ' ')

proc sites*(files: seq[SrcFile]): seq[string] =
  ## Every census site of the given files, as `kind:file:context[#n]`.
  var seen = initCountTable[string]()
  for f in files:
    let inSrc = f.path.startsWith("src/nelli/")
    let inTests = f.path.startsWith("tests/")
    let recorded = "skipCell" in f.text
    for raw in f.text.splitLines():
      let line = raw.strip(trailing = true, chars = {'\r', ' ', '\t'})
      let s = stripComment(line)
      var hits: seq[string]
      if inSrc:
        for _ in 1 .. countTok(s, "Survivors("): hits.add "survivors"
        for _ in 1 .. countTok(s, "Degrade("): hits.add "degrade"
      elif inTests:
        for _ in 1 .. countTok(s, skTok): hits.add "bare_skip"
        if not recorded:
          for _ in 1 .. countPlatform(s): hits.add "platform"
      for k in hits:
        let base = k & ":" & f.path & ":" & context(line)
        seen.inc base
        result.add (if seen[base] == 1: base else: base & "#" & $seen[base])
    if inSrc:
      for c in nimCases(f.text):
        if c.disp != dTransparent: continue
        let base = "nimcase_transparent:" & f.path & ":case " & c.subject &
                   ".kind in " & c.owner
        seen.inc base
        result.add (if seen[base] == 1: base else: base & "#" & $seen[base])

proc kindOf(site: string): string = site.split(':')[0]

proc census*(sites: seq[string]; allow: seq[Allow]; slices: HashSet[string]):
    seq[string] =
  ## One message per failing site or entry.
  let have = sites.toHashSet
  var listed = initHashSet[string]()
  for a in allow:
    result.add entryProblems(a, slices)
    if a.key in listed: result.add "allowlist entry " & a.key & " is listed twice"
    if kindOf(a.key) == "nimcase_transparent" and
       not a.reason.startsWith("[transparent"):
      result.add "allowlist entry " & a.key &
                 ": a transparent else is listed as a finding; the reason " &
                 "must start with `[transparent:<role>]`"
    listed.incl a.key
    if a.key notin have:
      result.add "stale allowlist entry (the site no longer exists; remove the line): " & a.key
  for s in sites:
    if s notin listed:
      result.add "unlisted census site (classify it in tests/0016-allowlist/census.txt): " & s

proc collect(): seq[SrcFile] =
  for sub in ["src/nelli", "tests"]:
    for p in walkDirRec(root / sub):
      if not p.endsWith(".nim"): continue
      let rel = p.relativePath(root).replace('\\', '/')
      if rel.startsWith("tests/fixtures/") or rel == "tests/" & selfName:
        continue
      result.add (rel, readFile(p))
  result.sort(proc (a, b: SrcFile): int = cmp(a.path, b.path))

proc tally(sites: seq[string]): CountTable[string] =
  for s in sites: result.inc kindOf(s)

suite "RFC-0016 K2a: dispatch census (synthetic sources)":
  let slices = toHashSet(["K2a", "K2a-fail", "K7c", "K4a-dispatch"])
  proc ent(key: string; slice = "K2a-fail"; reason = "r"): Allow =
    Allow(key: key, slice: slice, reason:
          (if reason == "r" and key.startsWith("nimcase_transparent"):
             "[transparent:t] r" else: reason))

  let srcA: SrcFile = ("src/nelli/a.nim",
    "proc f(n: NimNode) =\n  case n.kind\n  of nnkA: discard\n  else: discard\n" &
    "  # case n.kind in a comment\n  let s = Survivors(live: @[])\n" &
    "  let d = Degrade(path: p)\n  allocDegrade(k, m)\n" &
    "  lowerDegrade(k, m)\n  case xn.kind\n  of a: discard\n")
  let tstA: SrcFile = ("tests/t.nim",
    "test \"x\":\n  " & skTok & ")\n  skipCell(c)\n  # " & skTok & ")\n")
  let plat: SrcFile = ("tests/p.nim",
    "when defined(windows):\n  discard\nelif hostOS == \"linux\":\n  discard\n")
  let platOk: SrcFile = ("tests/q.nim",
    "when defined(windows):\n  skipCell(c)\n")

  test "the rules count what K2-s counts and ignore what it ignores":
    let t = tally(sites(@[srcA, tstA, plat, platOk]))
    check t.getOrDefault("nimcase_transparent") == 1  # comment and `xn.kind` ignored
    check t.getOrDefault("survivors") == 1
    check t.getOrDefault("degrade") == 1       # allocDegrade/lowerDegrade not
    check t.getOrDefault("bare_skip") == 1     # skipCell and the comment not
    check t.getOrDefault("platform") == 2      # q.nim has skipCell: not counted

  test "a repeated case in one routine gets #n and stays distinct":
    let two = "proc g(n: NimNode) =\n  case n.kind\n  of nnkA: discard\n" &
              "  else: discard\n  case n.kind\n  of nnkB: discard\n  else: discard\n"
    let s = sites(@[("src/nelli/b.nim", two)])
    check s == @["nimcase_transparent:src/nelli/b.nim:case n.kind in g",
                 "nimcase_transparent:src/nelli/b.nim:case n.kind in g#2"]

  proc dispOf(src: string): seq[Disp] =
    nimCases(src).mapIt(it.disp)

  test "every case over a NimNode kind is found, whatever the subject is called":
    let src = "proc h(lhs, impl: NimNode) =\n" &
              "  case lhs.kind\n  of nnkIdent: discard\n" &
              "  case impl.kind\n  of nnkSym, nnkIdent: discard\n" &
              "  let w = case p.ty.kind\n    of nnkCall: 1\n    else: 2\n"
    check nimCases(src).mapIt(it.subject) == @["lhs", "impl", "p.ty"]

  test "a case whose labels are not NimNodeKind members is not a NimNode case":
    check nimCases("proc h(s: IRStmt) =\n  case s.kind\n  of isBlock: discard\n" &
                   "  else: discard\n").len == 0

  test "the else disposition: none, decline, sentinel, transparent":
    let head = "proc h(n: NimNode) =\n  case n.kind\n  of nnkA: discard\n"
    check dispOf(head) == @[dNone]
    check dispOf(head & "  else: ctx.declineAtSite(feX, \"m\")\n") == @[dDecline]
    check dispOf(head & "  else:\n    error(\"x\", n)\n") == @[dDecline]
    check dispOf(head & "  else: raise newSymexError(\"x\")\n") == @[dDecline]
    check dispOf(head & "  else: false\n") == @[dSentinel]
    check dispOf(head & "  else:\n    return nil\n") == @[dSentinel]
    check dispOf(head & "  else: none(string)\n") == @[dSentinel]
    check dispOf(head & "  else: discard\n") == @[dTransparent]
    check dispOf(head & "  else:\n    for c in n: h(c)\n") == @[dTransparent]
    check dispOf(head & "  else: n.repr\n") == @[dTransparent]

  test "K2F-4: a sentinel else carries an audited polarity":
    let head = "proc h(n: NimNode): bool =\n  case n.kind\n  of nnkA: true\n"
    proc probs(src: string): seq[string] =
      for c in nimCases(src):
        let p = auditProblem(c, "src/nelli/x.nim")
        if p.len > 0: result.add p
    check probs(head & "  else: false\n").len == 1
    check "unaudited sentinel" in probs(head & "  else: false\n")[0]
    check probs(head & "  else: false  # k2: fail-closed: f declines\n").len == 0
    check probs(head & "  else:\n    # k2: n/a: no name\n    return false\n").len == 0
    check probs(head & "  else: false  # k2: fail-open: trusted\n").len == 1
    check probs(head & "  else: false  # k2: fail-closed\n").len == 1   # no reading
    check probs(head & "  else: false\n  # k2: n/a: a later line's\n").len == 1
    check probs(head & "  else: discard\n").len == 0   # transparent: census.txt's
    check probs(head & "  else: decline(n)\n").len == 0

  test "the case ends where the layout says: a later else is not its else":
    check dispOf("proc h(n: NimNode) =\n  case n.kind\n  of nnkA: discard\n" &
                 "  if x: discard\n  else: false\n") == @[dNone]
    check dispOf("proc h(n: NimNode) =\n  if q:\n    case n.kind\n" &
                 "    of nnkA: discard\n  else: discard\n") == @[dNone]

  test "RED: a new transparent else is an unlisted site":
    let src = "proc h(n: NimNode) =\n  case n.kind\n  of nnkA: discard\n" &
              "  else: discard\n"
    let s = sites(@[("src/nelli/c.nim", src)])
    check s.len == 1
    let problems = census(s, @[], slices)
    check problems.len == 1 and "unlisted census site" in problems[0]

  test "a transparent entry must say it is transparent":
    let src = "proc h(n: NimNode) =\n  case n.kind\n  of nnkA: discard\n" &
              "  else: discard\n"
    let s = sites(@[("src/nelli/c.nim", src)])
    check census(s, @[ent(s[0], reason = "benign")], slices).anyIt(
      "[transparent" in it)
    check census(s, @[ent(s[0], reason = "[transparent:ignore] r")],
                 slices).len == 0

  test "RED: a new site with no allowlist entry fails as unlisted":
    let s = sites(@[srcA])
    let problems = census(s, s[1 .. ^1].mapIt(ent(it)), slices)
    check problems.len == 1
    check "unlisted census site" in problems[0]
    check s[0] in problems[0]

  test "RED: an entry whose site no longer exists fails as stale":
    let s = sites(@[srcA])
    let gone = "bare_skip:tests/gone.nim:" & skTok & ")"
    let problems = census(s, (s & gone).mapIt(ent(it)), slices)
    check problems.len == 1
    check "stale allowlist entry" in problems[0]
    check gone in problems[0]

  test "a fully listed census is clean":
    let s = sites(@[srcA, tstA, plat])
    check census(s, s.mapIt(ent(it)), slices).len == 0

  test "an entry needs a real slice id and a reason; a duplicate fails":
    let s = sites(@[srcA])
    var allow = s.mapIt(ent(it))
    allow[0].slice = "UNASSIGNED"
    allow[1].reason = ""
    allow.add ent(s[2])
    let problems = census(s, allow, slices)
    check problems.anyIt("UNASSIGNED" in it)
    check problems.anyIt("has no reason" in it)
    check problems.anyIt("listed twice" in it)

suite "RFC-0016 K2a: dispatch census (the tree)":
  let allow = parseAllow(readFile(allowPath))
  let slices = sliceIds11(readFile(rfcPath))
  let files = collect()
  let found = sites(files)

  test "every site of the tree is listed and every entry still exists":
    let problems = census(found, allow, slices)
    if problems.len > 0: echo problems.join("\n")
    check problems.len == 0
    echo "K2a census: ", tally(found), "; allowlist entries: ", allow.len

  test "every kind is counted (a rule that finds nothing is broken)":
    let t = tally(found)
    for k in ["survivors", "degrade", "bare_skip"]:
      check t.getOrDefault(k) > 0

  test "K2F-4: every sentinel else carries its audited polarity":
    var problems: seq[string]
    var audited = 0
    for f in files:
      if not f.path.startsWith("src/nelli/"): continue
      for c in nimCases(f.text):
        let p = auditProblem(c, f.path)
        if p.len > 0: problems.add p
        elif c.disp == dSentinel: inc audited
    if problems.len > 0: echo problems.join("\n")
    check problems.len == 0
    check audited > 0
    echo "K2F-4 audited sentinels: ", audited

  test "every case over a NimNode kind is classified (the dispositions)":
    var by = initCountTable[Disp]()
    var total = 0
    for f in files:
      if f.path.startsWith("src/nelli/"):
        for c in nimCases(f.text):
          by.inc c.disp
          inc total
    echo "NimNode cases: ", total, " ", by
    check total > 100                       # the literal `case n.kind` is 53
    check by.getOrDefault(dNone) > 0        # the classOf shape exists
    check by.getOrDefault(dDecline) > 0
    check by.getOrDefault(dTransparent) > 0
    var transparent = 0
    for s in found:
      if kindOf(s) == "nimcase_transparent": inc transparent
    check transparent == by.getOrDefault(dTransparent)

  test "the literal `case n.kind` is one NimNode case or a non-NimNode enum":
    # The 53 sites of K2-s's case_n_kind row: each is found as a NimNode case
    # here, or its labels are an IR/choice enum (4 sites today).
    var literal, nim = 0
    for f in files:
      if not f.path.startsWith("src/nelli/"): continue
      for raw in f.text.splitLines(): literal += countCaseNKind(stripComment(raw))
      for c in nimCases(f.text):
        if c.subject == "n": inc nim
    check literal > 0 and nim <= literal

  test "the totals agree with scripts/census-k2.sh (K2-s)":
    let bash = findExe("bash")
    if bash.len == 0 or not fileExists(scriptPath) or defined(windows):
      echo "skipped: no bash/K2-s script on this host"
    else:
      let (outp, rc) = execCmdEx(quoteShell(bash) & " " &
                                 quoteShell(scriptPath) & " --root " &
                                 quoteShell(root))
      check rc == 0
      var want = initCountTable[string]()
      for l in outp.splitLines():
        let f = l.split('\t')
        if f.len >= 3 and f[0] == "summary" and ':' notin f[1]:
          want[f[1]] = parseInt(f[2])
      let t = tally(found)
      for k in ["survivors", "degrade", "bare_skip"]:
        check t.getOrDefault(k) == want.getOrDefault(k)
      var literal = 0
      for f in files:
        if f.path.startsWith("src/nelli/"):
          for raw in f.text.splitLines():
            literal += countCaseNKind(stripComment(raw))
      check literal == want.getOrDefault("case_n_kind")
