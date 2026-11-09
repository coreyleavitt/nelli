## RFC-0016 K2a (section 8.2, the rule for introducing an axis): the dispatch
## census, as a test over the sites K2-s (`scripts/census-k2.sh`) counts.
##
## Four kinds of site are counted:
##   case_n_kind  every `case n.kind` in `src/nelli/**/*.nim` (the construct
##                axis's dispatch sites);
##   survivors    every `Survivors(` literal in `src/nelli` (AUD-09);
##   degrade      every `Degrade(` literal in `src/nelli` (word boundary:
##                `allocDegrade(` and `lowerDegrade(` do not count);
##   bare_skip    every `skip(` call under `tests/` (`skipCell(` is another
##                identifier and is the recorded form);
##   platform     every platform arm (`defined(windows)`, `hostOS`, ...) in a
##                `tests/` file that never mentions `skipCell`: such a file
##                has no way to record that an arm did not run.
## The first four kinds use K2-s's rules exactly (comment text after the first
## `#` is dropped; a hit needs a non-identifier character before it). The
## fifth is K2a's own: K2-s does not count platform arms.
##
## The ratchet. `tests/0016-allowlist/census.txt` lists every site, one line
## `site<TAB>slice<TAB>reason`. A site is `kind:file:context`, where context is
## the comment-stripped trimmed line (a second identical line in one file gets
## `#2`, and so on), so a refactor that moves a line does not churn it. The test
## fails on
##   * an UNLISTED site: a new dispatch, `Survivors(`/`Degrade(` literal, bare
##     `skip(` or platform arm must be classified in the commit that adds it;
##   * a STALE entry: a listed site that no longer exists, so the list cannot
##     rot the other way;
##   * a duplicate entry, `UNASSIGNED` or an unknown slice id, or no reason.
## On Linux the four K2-s kinds are also cross-checked against the totals
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
  kinds = ["case_n_kind", "survivors", "degrade", "bare_skip", "platform"]

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
  ## `case n.kind` with one or more blanks, then a non-identifier or EOL.
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
        for _ in 1 .. countCaseNKind(s): hits.add "case_n_kind"
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

proc kindOf(site: string): string = site.split(':')[0]

proc census*(sites: seq[string]; allow: seq[Allow]; slices: HashSet[string]):
    seq[string] =
  ## One message per failing site or entry.
  let have = sites.toHashSet
  var listed = initHashSet[string]()
  for a in allow:
    result.add entryProblems(a, slices)
    if a.key in listed: result.add "allowlist entry " & a.key & " is listed twice"
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
    Allow(key: key, slice: slice, reason: reason)

  let srcA: SrcFile = ("src/nelli/a.nim",
    "proc f(n: Node) =\n  case n.kind\n  of nkA: discard\n" &
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
    check t.getOrDefault("case_n_kind") == 1   # comment and `xn.kind` ignored
    check t.getOrDefault("survivors") == 1
    check t.getOrDefault("degrade") == 1       # allocDegrade/lowerDegrade not
    check t.getOrDefault("bare_skip") == 1     # skipCell and the comment not
    check t.getOrDefault("platform") == 2      # q.nim has skipCell: not counted

  test "a repeated line in one file gets #n and stays distinct":
    let s = sites(@[("src/nelli/b.nim", "case n.kind\ncase n.kind\n")])
    check s == @["case_n_kind:src/nelli/b.nim:case n.kind",
                 "case_n_kind:src/nelli/b.nim:case n.kind#2"]

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
    for k in ["case_n_kind", "survivors", "degrade", "bare_skip"]:
      check t.getOrDefault(k) > 0

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
      for k in ["case_n_kind", "survivors", "degrade", "bare_skip"]:
        check t.getOrDefault(k) == want.getOrDefault(k)
