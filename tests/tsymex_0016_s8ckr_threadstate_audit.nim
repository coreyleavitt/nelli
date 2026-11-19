## RFC-0016 S8ck-r (INF-04) -- permanent audit: no threadvar under src/nelli
## escapes `releaseSymexThreadState`.
##
## Nim never destroys a threadvar when its thread exits, so a threadvar that
## holds heap and is not released leaks with every thread that ran nelli
## (tsymex_rfc0005_s8cb_replay's foreign thread: about 100 KB under
## LeakSanitizer before S8ck-r). src/nelli/thread_state.nim holds the
## registry; each module that declares threadvars sets them back to default
## in a `releaseToDefault(...)` inside a proc it registers with
## `registerThreadStateRelease`. A new threadvar that is not added there
## would leak silently: the LSan leg only sees it if a nightly slice happens
## to run a thread that touches it. This audit makes that impossible.
##
## Rules, per file under src/nelli (read comment- and string-blind through
## `codeOf`, so prose and doc comments never count):
##   * every `{.threadvar.}` declaration is named in a `releaseToDefault(...)`
##     of the SAME file, or its declaration line carries the reviewed marker
##     `[thread-state: kept -- <reason>]` (a threadvar the release must not
##     undo; the reason is required);
##   * a file with a `releaseToDefault(...)` registers a release
##     (`registerThreadStateRelease(`);
##   * a name in a `releaseToDefault(...)` is a threadvar of that file (no
##     stale entries), and no threadvar is both released and kept;
##   * a threadvar pragma whose declaration the scanner cannot read fails.
import std/[unittest, strutils, os, algorithm]
import audit_scan_utils

const
  nelliSrcDir = currentSourcePath().parentDir() / ".." / "src" / "nelli"
  keptMarker = "[thread-state: kept -- "

type Violation = object
  file: string
  lineNo: int
  msg: string

proc identAt(s: string, i: int): string =
  var j = i
  while j < s.len and isIdentChar(s[j]): inc j
  s[i ..< j]

proc releasedNames(code: string): seq[string] =
  ## Every name inside every `releaseToDefault(...)` of `code`.
  var i = 0
  const call = "releaseToDefault("
  while true:
    let k = code.find(call, i)
    if k < 0: break
    if k > 0 and isIdentChar(code[k - 1]):
      i = k + call.len
      continue
    let e = code.find(')', k)
    if e < 0: break
    for part in code[k + call.len ..< e].split(','):
      let n = part.strip()
      if n.len > 0: result.add n
    i = e + 1

proc auditThreadState*(file, text: string, violations: var seq[Violation]):
    tuple[declared, kept: int] =
  let code = codeOf(text)
  let codeLines = code.splitLines()
  let rawLines = text.splitLines()
  let released = releasedNames(code)
  var declared: seq[string]
  var keptNames: seq[string]
  for idx, cl in codeLines:
    let p = cl.find("{.")
    if p < 0: continue
    let pe = cl.find(".}", p)
    let prag = if pe < 0: cl[p + 2 .. ^1] else: cl[p + 2 ..< pe]
    var isTv = false
    for w in prag.split({',', ' ', ':'}):
      if w.strip() == "threadvar": isTv = true
    if not isTv: continue
    var head = cl[0 ..< p].strip()
    if head.startsWith("var "): head = head[4 .. ^1].strip()
    if head.endsWith("*"): head = head[0 ..< ^1].strip()
    let name = identAt(head, 0)
    if name.len == 0 or name.len != head.len:
      violations.add Violation(file: file, lineNo: idx + 1,
        msg: "a threadvar declaration the audit cannot read: " & cl.strip())
      continue
    declared.add name
    let raw = if idx < rawLines.len: rawLines[idx] else: ""
    let m = raw.find(keptMarker)
    if m >= 0:
      if raw[m + keptMarker.len .. ^1].strip(chars = {' ', ']'}).len == 0:
        violations.add Violation(file: file, lineNo: idx + 1,
          msg: "`" & name & "` is marked kept with no reason")
      keptNames.add name
      if name in released:
        violations.add Violation(file: file, lineNo: idx + 1,
          msg: "`" & name & "` is both released and marked kept")
    elif name notin released:
      violations.add Violation(file: file, lineNo: idx + 1,
        msg: "threadvar `" & name & "` is not released: add it to this " &
          "module's releaseToDefault(...), or mark it `" & keptMarker &
          "<reason>]` after review")
  if released.len > 0 and "registerThreadStateRelease(" notin code:
    violations.add Violation(file: file, lineNo: 0,
      msg: "releaseToDefault(...) is never registered " &
        "(registerThreadStateRelease)")
  for n in released:
    if n notin declared:
      violations.add Violation(file: file, lineNo: 0,
        msg: "releaseToDefault names `" & n & "`, not a threadvar of this file")
  (declared.len, keptNames.len)

proc nelliSources(): seq[tuple[label, path: string]] =
  for p in walkDirRec(nelliSrcDir):
    if p.endsWith(".nim"):
      result.add (label: "src/nelli/" & p.relativePath(nelliSrcDir), path: p)
  result.sort(proc (a, b: tuple[label, path: string]): int = cmp(a.label, b.label))

suite "S8ck-r: every threadvar under src/nelli is released or reviewed":

  test "no threadvar escapes releaseSymexThreadState":
    var violations: seq[Violation]
    var declared, kept, files: int
    for (label, path) in nelliSources():
      let (d, k) = auditThreadState(label, readFile(path), violations)
      declared += d
      kept += k
      if d > 0: inc files
    checkpoint("threadvars " & $declared & " in " & $files & " files, kept " & $kept)
    for v in violations:
      checkpoint(v.file & ":" & $v.lineNo & ": " & v.msg)
    check violations.len == 0
    # The census is at least what S8ck-r found (172 declarations in 17
    # files): a scanner that silently stopped reading declarations fails here.
    # 16 files since RFC-0016 INT-34 (rv0005-lows) scoped the symex DB errors
    # to their run: `engine/types.nim` holds no threadvar any more.
    check declared >= 172
    check files >= 16

  test "fixed cases: an unreleased threadvar, an unregistered release and a reasonless keep trip the audit":
    var v1: seq[Violation]
    discard auditThreadState("fx1.nim",
      "var a {.threadvar.}: seq[int]\nvar b* {.threadvar.}: int\n" &
      "proc r() = releaseToDefault(a)\nregisterThreadStateRelease(r)\n", v1)
    check v1.len == 1
    check v1.len == 1 and "`b`" in v1[0].msg
    var v2: seq[Violation]
    discard auditThreadState("fx2.nim",
      "var a {.threadvar.}: seq[int]\nproc r() = releaseToDefault(a)\n", v2)
    check v2.len == 1
    var v3: seq[Violation]
    discard auditThreadState("fx3.nim",
      "var a {.threadvar.}: bool  # [thread-state: kept -- ]\n", v3)
    check v3.len == 1
    var v4: seq[Violation]
    discard auditThreadState("fx4.nim",
      "var a {.threadvar.}: bool  # [thread-state: kept -- a reason]\n" &
      "## releaseToDefault(b) in prose is not a release\n", v4)
    check v4.len == 0
    var v5: seq[Violation]
    discard auditThreadState("fx5.nim",
      "var\n  a {.threadvar, global.}: int\n", v5)
    check v5.len == 1
