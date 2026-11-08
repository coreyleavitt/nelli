## RFC-0016 K7a -- `Survivors` and `CapKind` (section 8.4, K7).
##
## A refactor: no verdict moves and no walker bump. What K7a makes true is
## that a walk-level degrade can no longer be discarded in place.
##   (a) no `discard w.degrade(` remains: the halt sites go through
##       `halted`, the one sanctioned discard of a token, and the
##       recorded-but-continued site goes through `continued`;
##   (b) every `CapKind` member has exactly one producing site, a
##       `cap = <member>` argument, so K1 can derive cap coverage;
##   (c) the cut runs those caps produce are never `trusted()`.
import std/[unittest, os, strutils]
import nelli/symex
import nelli/smt/types

const smtDir = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "smt"

proc runtimeFiles(): seq[string] =
  for f in walkFiles(smtDir / "runtime*.nim"): result.add f

proc codeLines(f: string): seq[string] =
  for raw in readFile(f).splitLines():
    let t = raw.strip()
    if t.len > 0 and not t.startsWith("#"): result.add t

proc capMembers(): seq[string] =
  ## The `CapKind` members other than `ckNone`, read from its declaration.
  var inEnum = false
  for t in codeLines(smtDir / "runtime.nim"):
    if t.startsWith("CapKind = enum"): inEnum = true; continue
    if inEnum:
      let word = t.split({' ', '\t'})[0]
      if not word.startsWith("ck"): break
      if word != "ckNone": result.add word

suite "RFC-0016 K7a (a) -- no walk-level degrade is discarded in place":

  test "`discard w.degrade(` survives only inside `halted`":
    var hits: seq[string]
    for f in runtimeFiles():
      for t in codeLines(f):
        if "discard w.degrade(" in t: hits.add f.extractFilename & ": " & t
    checkpoint($hits)
    check hits.len == 1
    check hits.len == 1 and "cap = cap" in hits[0]   ## the one in `halted`

  test "the sanctioned halt and continue constructors exist":
    let src = readFile(smtDir / "runtime.nim")
    check "Survivors = object" in src
    check "proc halted(" in src
    check "proc surviving(" in src
    check "proc continued(" in src
    check "func exact(" in src

suite "RFC-0016 K7a (b) -- CapKind: one producing site per member":

  test "CapKind is declared and has members":
    check capMembers().len >= 1

  test "each member is named by exactly one `cap =` argument across runtime*.nim":
    for m in capMembers():
      var sites: seq[string]
      for f in runtimeFiles():
        for t in codeLines(f):
          let at = t.find("cap = " & m)
          let e = at + ("cap = " & m).len
          if at >= 0 and (e >= t.len or not (t[e].isAlphaNumeric or t[e] == '_')):
            sites.add t
      checkpoint(m & ": " & $sites)
      check sites.len == 1

# ---- (c) cut runs are never trusted -----------------------------------------

proc k7aLoopDead(n: int) =
  var i = 0
  var acc = 0
  while i < n:
    acc = acc + 1
    i = i + 1
  if n == 5 and n == 6:
    symexTarget("k7a_loop_dead")

proc k7aZero(n: int): int =
  result = 0

proc k7aDepthDead(n: int) =
  discard k7aZero(n)
  if n == 5 and n == 6:
    symexTarget("k7a_depth_dead")

proc k7aPruneDead(x: int) =
  if x mod 2 == 0:
    if x mod 3 == 0:
      if x == 1 and x == 2:
        symexTarget("k7a_prune_dead")

const depthZero = block:
  var s = defaultSymexSettings()
  s.budget.maxCallDepth = 0
  s

const frontierOne = block:
  var s = defaultSymexSettings()
  s.budget.maxFrontierSize = 1
  s

suite "RFC-0016 K7a (c) -- a cut run is never trusted":

  test "k-unroll cut (ckLoopUnwind)":
    let r = symexFind(k7aLoopDead, tLabel("k7a_loop_dead"))
    check r.status != sxUnsat
    check not r.trusted()

  test "call-depth cut (ckCallDepth)":
    let r = symexFind(k7aDepthDead, tLabel("k7a_depth_dead"), depthZero)
    check r.status != sxUnsat
    check not r.trusted()

  test "frontier cut (ckFrontier)":
    let r = symexFind(k7aPruneDead, tLabel("k7a_prune_dead"), frontierOne)
    check r.status != sxUnsat
    check not r.trusted()
