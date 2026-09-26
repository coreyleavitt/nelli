## RFC-0005 (soundness channels) slice S1b -- mint the missing kinds, and the
## runTaint/errors CORRESPONDENCE pin (RFC §2.2 "The premise 'every taint
## site has a kind in hand' is false", §2.2 "The run coordinate is derived,
## not written", §3.1's solver-undef row, §6 item 5).
##
## S1 derived `w.runTaint` from the drained error seqs, but a handful of
## degrade sites recorded NO `SymexErrorInfo` -- they reached the drain only
## through a transitional kindless ⊤ mark, and a run whose ONLY degrade was
## one of them hit the Invariant-7 backstop and was stamped
## `weInternalWalkerFault` ("the walker itself hit a bug") for what is an
## ordinary, classifiable degrade (a solver resource-out, a dropped
## statement, a recursion cycle cut, ...). S1b gives every such site a kind
## and routes it through `degrade()`, which records.
##
## Still all-⊤ (`classOf` maps every kind, old and new, to `dcNoAnswer`), so
## NO verdict changes: the only observable movement is `r.errors` gaining the
## specific kind, and the `weInternalWalkerFault` stamp disappearing where
## that kind now explains the taint.
##
## What this file pins:
##   (a) BEHAVIOURAL correspondence -- per formerly-kindless site, a SUT run
##       through `symexFind` (the real entry point; IR-level `runSymex` only
##       where no surface Nim reaches the site) whose `r.errors` now carries
##       the site's own kind and no `weInternalWalkerFault`;
##   (b) STRUCTURAL correspondence -- a `Degrade` token (the only thing that
##       can taint a path) is constructed ONLY inside the recording funnels,
##       and no kindless shim remains (the last two -- the target/raise-route
##       unsolved skips -- were replaced by the real solve in RFC-0005 S1c).
import std/[unittest, strutils, os, algorithm, sets]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/canonicalize
import audit_scan_utils

proc kindNames(errs: seq[SymexErrorInfo]): seq[string] =
  for e in errs: result.add $e.kind

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

# ---- SUTs (module scope so the macro resolves them via getImpl) -------------

# Solver resource-out. The Phase-13 rlimit exhibit: a four-variable BV
# product under `queryRLimit = 1` makes `trySolve` return `zsUnknown`
# deterministically (rlimit is a logical step count, not wall clock).
const tightRLimit = SymexSettings(
  integerSemantics: isOptimised,
  budget: ResourceBudget(
    queryRLimit: 1'u,
    maxFrontierSize: 0,
    maxCallDepth: 3,
    maxLoopUnwind: 5))

proc s1bSolverUndefLabel(a, b, c, d: int) =
  if a * b * c * d == 1234567:
    symexTarget("s1b_rare")

proc s1bSolverUndefRaise(a, b, c, d: int) =
  if a * b * c * d == 1234567:
    raise newException(ValueError, "s1b rare")

# Class-B `isUnsupported` (no parse-time error of its own): a field-LHS
# augmented assignment is dropped whole (`tsymex_augmented_assign.nim`).
type S1bPoint = object
  x, y: int

proc s1bFieldAug(p: S1bPoint, b: int) =
  var q = p
  q.x += b
  if b > 0:
    symexTarget("s1b_fieldaug")

# Class-A `isUnsupported` (paired with a parse-time `feUnsupportedExprKind`):
# `low(bool)` is outside A0's int-family fold (`tsymex_r6_a0_lowhigh.nim`).
proc s1bLowBool(flag: bool) =
  if flag == low(bool):
    symexTarget("s1b_lowbool")

# Recursion cycle cut: a self-call with an IDENTICAL argument shape is broken
# with a fresh return symbol (`w.activeCalls`), never re-walked.
proc s1bSelfCycle(x: int): int =
  if x > 0:
    result = s1bSelfCycle(x)
  else:
    result = 0

proc s1bCycleUser(x: int) =
  if s1bSelfCycle(x) == 7:
    symexTarget("s1b_cycle")

# Over-cap missing callee: ONE generic at three distinct types under a cap of
# two -- the third instantiation is never registered (`tsymex_phase15_G1c_
# instcap.nim`), so its call reaches the walker's missing-callee arm.
proc s1bSzof[T](x: T): int = sizeof(T)

proc s1bThreeInsts(a: int8, b: int16, c: int32) =
  if s1bSzof(a) == 1 and s1bSzof(b) == 2 and s1bSzof(c) == 4:
    symexTarget("s1b_found")

const s1bLowCap = withSymexSettings() do (s: var SymexSettings):
  s.budget.maxInstantiationsPerProc = 2

# `break` with no enclosing loop: the parser flattens `block:` into its body,
# so a (named) `break` out of a top-level block reaches the walker with an empty loop
# stack and the breaking path is dropped.
proc s1bBlockBreak(x: int) =
  block s1bBlk:
    if x > 0:
      break s1bBlk
    return
  symexTarget("s1b_after_block")

# Handler-stack re-raise: a bare `raise` inside a `try` BODY (handler stack
# non-empty, no in-flight exception yet).
proc s1bTryBodyReraise(x: int) =
  try:
    if x > 0:
      raise
  except ValueError:
    discard
  symexTarget("s1b_after_try")

# Diverged closure body: the closure never produces a value (every path
# raises), so the call has no value-bearing continuation.
proc s1bClosureDiverge(x: int) =
  let f = proc(y: int): int =
    raise newException(ValueError, "s1b never returns")
  if f(x) > 0:
    symexTarget("s1b_closure_hit")

suite "RFC-0005 S1b (a) -- every degrade records its kind (behavioural correspondence)":

  test "solver resource-out at the target (isTargetLabel consumer) is beSolverUndef, NOT weInternalWalkerFault":
    let r = symexFind(s1bSolverUndefLabel, tLabel("s1b_rare"), tightRLimit)
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(beSolverUndef)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "solver resource-out at a raised finding (routeRaise consumer) is beSolverUndef, NOT weInternalWalkerFault":
    let r = symexFind(s1bSolverUndefRaise, tRaisedExn(), tightRLimit)
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(beSolverUndef)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a Class-B isUnsupported (no parse error) records its own kind at the walk site":
    let r = symexFind(s1bFieldAug, tLabel("s1b_fieldaug"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(feUnsupportedStmtKind)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a Class-A isUnsupported carries the SAME kind as its parse-time error, recorded again at the walk site":
    let r = symexFind(s1bLowBool, tLabel("s1b_lowbool"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    var walkSite = false
    for e in r.errors:
      if e.kind == feUnsupportedExprKind and e.severity == sevError and
         "A0: low/high on non-int-family" in e.msg:
        walkSite = true
    check walkSite

  test "a recursion cycle cut records weRecursionCycleCut":
    let r = symexFind(s1bCycleUser, tLabel("s1b_cycle"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(weRecursionCycleCut)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "an over-cap missing callee records its geInstantiationCapped AT the walk site":
    let r = symexFind(s1bThreeInsts, tLabel("s1b_found"), s1bLowCap)
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    var walkSite = false
    for e in r.errors:
      if e.kind == geInstantiationCapped and e.severity == sevError and
         "reached at walk time" in e.msg:
        walkSite = true
    check walkSite

  test "a `break` with no enclosing loop records weBreakOutsideLoop":
    let r = symexFind(s1bBlockBreak, tLabel("s1b_after_block"))
    checkpoint($kindNames(r.errors))
    check r.status == sxUnknown
    check r.errors.hasKind(weBreakOutsideLoop)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a `continue` with no enclosing loop records weBreakOutsideLoop (IR-level: Nim rejects it at the surface)":
    let prog = SymexProgram(params: @[],
      body: mkBlock(@[mkContinue(), mkTargetLabel("hit")]))
    let raw = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    checkpoint($kindNames(raw.errors))
    check raw.status == sxUnknown
    check raw.errors.hasKind(weBreakOutsideLoop)
    check not raw.errors.hasKind(weInternalWalkerFault)

  test "a bare `raise` in a try body (handler stack, no in-flight exn) records eeHandlerReraiseUnmodelled":
    let r = symexFind(s1bTryBodyReraise, tLabel("s1b_after_try"))
    checkpoint($kindNames(r.errors))
    check r.errors.hasKind(eeHandlerReraiseUnmodelled)
    check not r.errors.hasKind(weInternalWalkerFault)

  test "a closure body with no value-bearing exit records ceClosureBodyDiverged":
    let r = symexFind(s1bClosureDiverge, tLabel("s1b_closure_hit"))
    checkpoint($kindNames(r.errors))
    check r.errors.hasKind(ceClosureBodyDiverged)
    check not r.errors.hasKind(weInternalWalkerFault)

suite "RFC-0005 S1b (c) -- the kind rides the IR (isUnsupported node, unregistered-callee key)":

  test "the walker's isUnsupported arm records exactly the node's own (kind, reason)":
    let prog = SymexProgram(params: @[],
      body: mkBlock(@[mkUnsupported(seNestedSeqUnsupported, "s1b probe reason", 0),
                      mkTargetLabel("hit")]))
    let raw = runSymex(prog, SymexTarget(kind: stkLabel, label: "hit"))
    checkpoint($kindNames(raw.errors))
    check raw.status == sxUnknown
    var found = false
    for e in raw.errors:
      if e.kind == seNestedSeqUnsupported and e.msg == "s1b probe reason" and
         e.severity == sevError:
        found = true
    check found
    check not raw.errors.hasKind(weInternalWalkerFault)

  test "two isUnsupported nodes differing only in kind never share a cache-key canonical form":
    check canonicalize(mkUnsupported(feUnsupportedStmtKind, "r", 0)) !=
          canonicalize(mkUnsupported(feUnsupportedExprKind, "r", 0))

  test "unregisteredCalleeKey round-trips every kind; an ordinary key carries none":
    for k in SymexErrorKind:
      var got = weInternalWalkerFault
      check unregisteredCalleeKind(unregisteredCalleeKey(k, "s1bSzof#h#T=int32"), got)
      check got == k
    var dummy: SymexErrorKind
    check not unregisteredCalleeKind("s1bSzof#h#T=int32", dummy)
    check not unregisteredCalleeKind("__unregistered:", dummy)
    check not unregisteredCalleeKind("__unregistered:notAKind:x", dummy)
    check not unregisteredCalleeKind("__unregistered:geInstantiationCapped", dummy)

# ---- (b) the structural correspondence pin ----------------------------------
# A path can only be tainted through a `Degrade` token (`forkPathTainted`/
# `taintInPlace` take one; the S1 writer grep-pin closes direct `.taint`
# writes). So "every path-taint introduction is paired with a recorded error"
# holds iff every `Degrade(...)` construction sits inside a funnel that
# records. Read at TEST RUNTIME (`readFile`) -- the S1 writer grep-pin /
# N27/N36 audit precedent (MSVC C2026 avoidance for a large `staticRead`).

const smtDir = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "smt"

proc routineName(line: string): string =
  for kw in ["proc ", "template ", "func ", "iterator ", "macro ", "method "]:
    if line.startsWith(kw):
      var i = kw.len
      var name = ""
      while i < line.len and isIdentChar(line[i]):
        name.add line[i]
        inc i
      return name
  ""

proc codeOf(line: string): string =
  let ix = line.find(" #")
  if ix >= 0: line[0 ..< ix] else: line

proc hasIdentCall(code, ident: string): bool =
  ## `ident(` at an identifier boundary (so `heapArmDegrade(` never matches
  ## `Degrade(`).
  var i = 0
  while true:
    i = code.find(ident & "(", i)
    if i < 0: return false
    if i == 0 or not isIdentChar(code[i - 1]): return true
    i += ident.len

type Site = tuple[file, routine, line: string]

proc scanSites(ident: string): seq[Site] =
  for path in walkFiles(smtDir / "runtime*.nim"):
    var routine = "<top-level>"
    for raw in readFile(path).splitLines():
      let r = routineName(raw)
      if r.len > 0: routine = r
      if r == ident: continue   # the routine's own definition line
      let trimmed = raw.strip()
      if trimmed.len == 0 or isCommentLine(trimmed): continue
      if hasIdentCall(codeOf(raw), ident):
        result.add (path.extractFilename, routine, trimmed)

proc routinesOf(ss: seq[Site]): seq[string] =
  var s: HashSet[string]
  for x in ss: s.incl x.file & ":" & x.routine
  for x in s: result.add x
  result.sort()

proc report(ss: seq[Site]): string =
  for x in ss: result.add "\n  " & x.file & " [" & x.routine & "]: " & x.line

suite "RFC-0005 S1b (b) -- structural correspondence: a Degrade token exists only where an error was recorded":

  test "Degrade(...) is constructed ONLY inside the recording funnels":
    let ss = scanSites("Degrade")
    checkpoint(report(ss))
    check routinesOf(ss) == @[
      "runtime.nim:degrade",                     # records into the site's sink
      "runtime.nim:takeLoweringPendingDegrade",  # drains lowerDegrade's recorded joins
      "runtime_heap.nim:heapArmDegrade",         # records via allocDegrade
    ]

  test "the kindless PATH token is gone (every fork site now has a kind)":
    check scanSites("kindlessPathDegrade").len == 0

  test "the kindless RUN mark is gone too (RFC-0005 S1c: zero kindless sites -- every tainted path is solved)":
    ## Was: the shim survived at exactly the two unsolved-skip sites (the
    ## tainted `isTargetLabel` hit, the tainted `routeRaise` early return).
    ## S1c replaced both with the real solve, so the invariant is now total:
    ## no degrade, and no skip, marks the run without a recorded kind.
    check scanSites("kindlessRunDegrade").len == 0
    var left: seq[string]
    for path in walkFiles(smtDir / "runtime*.nim"):
      var ln = 0
      for line in readFile(path).splitLines():
        inc ln
        if "kindlessRunTaint" in line or "kindlessRunDegrade" in line:
          left.add path.extractFilename & ":" & $ln
    checkpoint($left)
    check left.len == 0

  test "no `RFC-0005 S1b: mint kind` worklist marker remains in src/":
    var left: seq[string]
    for path in walkDirRec(smtDir / ".." / ".."):
      if path.endsWith(".nim"):
        var ln = 0
        for line in readFile(path).splitLines():
          inc ln
          if "RFC-0005 S1b: mint kind" in line:
            left.add path.extractFilename & ":" & $ln
    checkpoint($left)
    check left.len == 0
