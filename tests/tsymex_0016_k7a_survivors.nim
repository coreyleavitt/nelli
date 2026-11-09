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
import ./s8cu_helpers

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

proc k7aLoopFork(n: int, x: int) =
  ## Each iteration forks, so one k-unroll's active set grows inside ONE
  ## statement; the target is unreachable.
  var i = 0
  var acc = 0
  while i < n:
    if x > i: acc = acc + 1 else: acc = acc + 2
    i = i + 1
  if acc == 1 and acc == 2:
    symexTarget("k7a_loop_fork")

proc k7aWideRead(i: int) =
  var a: array[300, int]
  if i >= 0 and i < 300:
    if a[i] == 5:
      symexTarget("k7a_wide_read")

proc k7aWideWrite(i: int) =
  var a: array[300, int]
  if i >= 0 and i < 300:
    a[i] = 7
    if a[0] == 7:
      symexTarget("k7a_wide_write")

proc k7aWork(n, x: int) =
  if n >= 0 and n <= 3:
    var acc = 0
    var i = 0
    while i < n:
      if x > i: acc = acc + 1 else: acc = acc + 2
      i = i + 1
    if acc == 100:
      symexTarget("k7a_work")

const workTiny = block:
  var s = defaultSymexSettings()
  s.budget.walkRLimit = 100
  s

const depthZero = block:
  var s = defaultSymexSettings()
  s.budget.maxCallDepth = 0
  s

const frontierOne = block:
  var s = defaultSymexSettings()
  s.budget.maxFrontierSize = 1
  s

suite "RFC-0016 K7a (c) -- a cut run is never trusted":
  ## Each test also writes a pin record naming the cap (`pinCap`), so K1a's
  ## `capkind:` join sees it. The caps with no test here (`ckHeapDepth`,
  ## `ckLoopUnwindFollow`, `ckVariantForks`, `ckVariantFieldAllocs`) stay
  ## allowlisted in `tests/0016-allowlist/capkind.txt` until K7c.

  test "k-unroll cut (ckLoopUnwind)":
    let r = symexFind(k7aLoopDead, tLabel("k7a_loop_dead"))
    check r.status != sxUnsat
    check not r.trusted()
    pinCap(k7aLoopDead, "ckLoopUnwind", tLabel("k7a_loop_dead"))

  test "call-depth cut (ckCallDepth)":
    let r = symexFind(k7aDepthDead, tLabel("k7a_depth_dead"), depthZero)
    check r.status != sxUnsat
    check not r.trusted()
    pinCap(k7aDepthDead, "ckCallDepth", tLabel("k7a_depth_dead"), depthZero)

  test "frontier cut (ckFrontier)":
    let r = symexFind(k7aPruneDead, tLabel("k7a_prune_dead"), frontierOne)
    check r.status != sxUnsat
    check not r.trusted()
    pinCap(k7aPruneDead, "ckFrontier", tLabel("k7a_prune_dead"), frontierOne)

  test "frontier cut inside one k-unroll (ckFrontier)":
    ## RFC-0016 K7 (CRH-01): `maxFrontierSize` also bounds a loop's live set
    ## within its statement, not only between statements.
    let r = symexFind(k7aLoopFork, tLabel("k7a_loop_fork"), frontierOne)
    check r.status != sxUnsat
    check not r.trusted()
    var inUnroll = false
    for e in r.errors:
      if "of a while-loop k-unroll" in e.msg: inUnroll = true
    check inUnroll
    pinCap(k7aLoopFork, "ckFrontier", tLabel("k7a_loop_fork"), frontierOne)

  test "a too-wide array read cut (ckTermWalkRead)":
    pinCap(k7aWideRead, "ckTermWalkRead", tLabel("k7a_wide_read"))

  test "a too-wide array write cut (ckTermWalkWrite)":
    pinCap(k7aWideWrite, "ckTermWalkWrite", tLabel("k7a_wide_write"))

  test "the walk's total solver work cut (ckWalkWork)":
    ## RFC-0016 K7: the sum of every check's Z3 units is bounded, not only
    ## each check. The same SUT with the default (0, unbounded) completes.
    let r = symexFind(k7aWork, tLabel("k7a_work"), workTiny)
    check r.status == sxUnknown
    check not r.trusted()
    pinCap(k7aWork, "ckWalkWork", tLabel("k7a_work"), workTiny)

  test "the same SUT without a walk work cap completes":
    let r = symexFind(k7aWork, tLabel("k7a_work"))
    check r.status == sxUnsat
    for e in r.errors:
      check "walk work cap" notin e.msg

  test "RED: pinCap fails when the run was not cut by that cap":
    expect PinFailure:
      pinCap(k7aLoopDead, "ckFrontier", tLabel("k7a_loop_dead"))
    expect PinFailure:
      pinCap(k7aLoopDead, "ckNoSuchCap", tLabel("k7a_loop_dead"))
