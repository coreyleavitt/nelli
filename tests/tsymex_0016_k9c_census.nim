## RFC-0016 K9c (W-56, F-05): no decline assertion without a kind.
##
## A test that asserts a decline (`check r.status == sxUnknown`) must also say
## WHICH `SymexErrorKind` caused it, in the same test block: a decline for the
## wrong reason (or a walker fault routed to `weInternalWalkerFault`) passes an
## unnamed `sxUnknown`. K9b (Wave 2) built the verbs (`pinDecline`,
## `named`); K9c named the kind of every legacy assertion by running it.
##
## The census. An ASSERTION is a `check`/`doAssert`/`require`/`assert` line
## holding `.status == sxUnknown`. (`rfc0005RawStatus`, the candidate before
## replay, is not a decline verdict and is not counted.) Its BLOCK is the
## nearest enclosing `test`/`template`/`proc`/`func`/`macro`/`iterator`
## (the whole file when there is none). The assertion is KINDED when its block
## names a `SymexErrorKind` member (the enum is the vocabulary, read here
## through `$`), or calls `pinDecline`, `.named(` or `hasKind(`.
##
## THE RATCHET. `ceiling` is the number of unkinded assertions allowed. It
## only falls: the test fails above it (a new unkinded decline) and below it
## (a kind was added and the ceiling did not follow, so a later commit could
## refill the gap). Raising it is the failure this test exists to stop.
import std/[unittest, os, strutils, sets, algorithm]
import nelli/smt/errorkind

const
  ceiling = 0
  testsDir = currentSourcePath().parentDir()
  self = "tsymex_0016_k9c_census.nim"
  heads = ["test ", "test\"", "template ", "proc ", "func ", "macro ",
           "iterator "]

proc indentOf(s: string): int =
  while result < s.len and s[result] == ' ': inc result

proc codeOf(line: string): string =
  ## The line without a full-line or trailing comment (a `#` outside a string).
  var inStr = false
  for i, c in line:
    if c == '"': inStr = not inStr
    elif c == '#' and not inStr: return line[0 ..< i]
  line

proc isAssertion*(line: string): bool =
  ## A `check`/`doAssert`/`require`/`assert` of a decline. A condition that
  ## merely branches on one (`if r.status == sxUnknown:`) asserts nothing, and
  ## a pure-function verdict (`decideVerdict`, which carries no error list) has
  ## no kind to name.
  let c = codeOf(line).strip
  if "decideVerdict(" in c: return false
  if not (c.startsWith("check ") or c.startsWith("doAssert ") or
          c.startsWith("require ") or c.startsWith("assert ")): return false
  ".status == sxUnknown" in c

proc isHead(line: string): bool =
  let t = line.strip(trailing = false)
  for h in heads:
    if t.startsWith(h): return true

proc blockOf*(ls: seq[string]; i: int): Slice[int] =
  ## The enclosing routine/test of line `i`, as a line range.
  var req = indentOf(ls[i])
  var j = i - 1
  while j >= 0:
    if ls[j].strip.len > 0 and codeOf(ls[j]).strip.len > 0 and
       indentOf(ls[j]) < req:
      if isHead(ls[j]): break
      req = indentOf(ls[j])
    dec j
  if j < 0: return 0 .. ls.high
  let h = indentOf(ls[j])
  var k = i + 1
  while k < ls.len and (ls[k].strip.len == 0 or indentOf(ls[k]) > h): inc k
  j .. k - 1

proc kindWords(): HashSet[string] =
  for k in SymexErrorKind: result.incl $k
  result.incl "pinDecline"

proc namesKind*(ls: seq[string]; r: Slice[int]; words: HashSet[string]): bool =
  for n in r:
    # `x.named(k)` and `hasKind(x, k)` take the kind as an argument; the bare
    # identifier `named` (a local boolean in several templates) is not evidence.
    let code = codeOf(ls[n])
    if ".named(" in code or "hasKind(" in code: return true
    var cur = ""
    for c in codeOf(ls[n]) & " ":
      if c in IdentChars: cur.add c
      else:
        if cur.len > 0 and cur in words: return true
        cur.setLen 0

proc callsVerdictRule(ls: seq[string]; r: Slice[int]): bool =
  ## `decideVerdict` is the pure verdict rule: it returns a status and a winner
  ## and carries no error list, so a decline there has no kind to name.
  for n in r:
    if "decideVerdict(" in codeOf(ls[n]): return true

proc unkinded*(text: string; words: HashSet[string]): seq[int] =
  ## 1-based lines of the assertions in `text` whose block names no kind.
  let ls = text.splitLines()
  for i in 0 .. ls.high:
    if isAssertion(ls[i]):
      let r = blockOf(ls, i)
      if not namesKind(ls, r, words) and not callsVerdictRule(ls, r):
        result.add i + 1

proc census(): seq[string] =
  let words = kindWords()
  var files: seq[string]
  for f in walkFiles(testsDir / "*.nim"):
    let n = f.extractFilename
    if n != self and not n.startsWith("zk9c_"): files.add f
  files.sort()
  for f in files:
    for ln in unkinded(readFile(f), words):
      result.add f.extractFilename & ":" & $ln

suite "K9c: every decline assertion names its kind":
  test "the census reads the shapes it claims to":
    let words = kindWords()
    check unkinded("test \"a\":\n  check r.status == sxUnknown\n", words) == @[2]
    check unkinded("test \"a\":\n  check r.status == sxUnknown\n" &
                   "  check r.errors.named(feUnsupportedOp)\n", words).len == 0
    check unkinded("test \"a\":\n  check r.status == sxUnknown\n" &
                   "test \"b\":\n  check r.errors.named(feUnsupportedOp)\n",
                   words) == @[2]
    check unkinded("test \"a\":\n  check r.status == sxUnknown " &
                   "# feUnsupportedOp\n", words) == @[2]
    check unkinded("test \"a\":\n  pinDecline(f, k, feUnsupportedOp)\n" &
                   "  check r.status == sxUnknown\n", words).len == 0
    check unkinded("# check r.status == sxUnknown\n", words).len == 0
    check unkinded("test \"a\":\n  let d = decideVerdict(x)\n" &
                   "  check d.status == sxUnknown\n", words).len == 0
    check unkinded("test \"a\":\n  if r.status == sxUnknown:\n" &
                   "    check true\n", words).len == 0

  test "no decline assertion is left without a kind, ratcheted":
    let found = census()
    if found.len != ceiling:
      checkpoint "unkinded decline assertions (" & $found.len & "): " &
                 found.join(" ")
    check found.len <= ceiling   # a new unkinded decline
    check found.len >= ceiling   # kinds were added: lower `ceiling` to match
