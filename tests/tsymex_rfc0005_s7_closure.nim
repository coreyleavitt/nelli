## RFC-0005 (soundness channels) slice S7 -- cross-path sinks and closure /
## HOF decline path taint (§2.4, §2.5; §5 row S7). Walker 145 -> 146.
##
## S9 deletes the closure veto (`closureForcedUnknown`) on the strength of
## this slice, so every closure / HOF site that stands a value in for one the
## walk did not compute must put that fact on the PATH, not only in the
## closure error sink the veto reads. Suites:
##   (a) classes -- the S7-owned kinds leave S1's ⊤ default;
##   (b) flips -- each false verdict the audit found, observed through
##       candidate placement / path taint (RawResult), so each test is red
##       before the change and green after it;
##   (c) guards -- clean closures stay clean, dead targets stay dead;
##   (d) the S9 precondition -- the verdict computed WITHOUT the vetoes is
##       never a clean `sxSat` for an S7 SUT;
##   (e) structural -- the solver-sink drain list, the closure-sink funnel,
##       the error-sink -> run-channel map, and the walker version floor.
import std/[unittest, sequtils, macros, strutils, os]
import nelli/symex
import nelli/smt/types
import nelli/smt/runtime
import nelli/smt/dsl_parser
import nelli/smt/canonicalize
import audit_scan_utils

macro progOf(fn: typed): untyped =
  ## The `SymexProgram` `symexFind` would build for `fn`, so a test can read
  ## the raw `RawResult` (its `candidates` / `pathTaint`), which `symexFind`
  ## folds away.
  let parsed = parseEntryImpl(fn, "progOf",
    defaultSymexSettings().budget.maxInstantiationsPerProc)
  let b = parsed.bodyNimNode
  let p = parsed.paramsNimNode
  let pr = parsed.procsNimNode
  let u = parsed.userExnHierarchyNimNode
  let pe = parsed.parseErrorsNimNode
  result = quote do:
    SymexProgram(params: `p`, body: `b`, procs: `pr`,
                 userExnHierarchy: `u`, parseErrors: `pe`)

proc hasKind(errs: seq[SymexErrorInfo]; k: SymexErrorKind): bool =
  for e in errs:
    if e.kind == k: return true
  false

proc show(r: RawResult): string =
  var ks: seq[string]
  for e in r.errors: ks.add $e.kind
  var cs: seq[string]
  for c in r.candidates: cs.add $c.status & ":" & $c.pathTaint
  $r.status & " errs=" & $ks & " cands=" & $cs

proc spuriousCandidate(r: RawResult): bool =
  ## The hit is filed as a CANDIDATE on a spurious-tainted path -- the
  ## placement S10's replay gate consumes -- rather than as a clean finding.
  r.candidates.len > 0 and r.candidates.allIt(scSpurious in it.pathTaint)

const anyRaise = SymexTarget(kind: stkRaisedExn, typeFilter: "")

const inlineOne = block:
  var s = defaultSymexSettings()
  s.budget.maxClosureInlineCount = 1
  s

# =============================================================================
# SUTs
# =============================================================================

# ---- HOF declines -------------------------------------------------------------

proc s7Filter(xs: seq[int]) =
  ## Symbolic-length filter: `__hofFilterUnsupported`, a fresh seq that is
  ## NOT the filtered one (the predicate is never applied). Reality never
  ## keeps a negative element; the walk's stand-in can.
  let kept = xs.filter(proc(x: int): bool = x > 0)
  if kept.len > 0 and kept[0] < 0:
    symexTarget("s7_filter")

proc s7MapCapture(xs: seq[int]; k: int) =
  ## Capturing symbolic-length map: `__hofMapUnsupported`.
  let ys = xs.map(proc(x: int): int = x + k)
  if ys.len > 0 and ys[0] != xs[0] + k:
    symexTarget("s7_map_capture")

proc s7MapArray(xs: seq[int]) =
  ## Capture-free symbolic-length map: the `mapArray` axiom path, whose
  ## function symbol no axiom ever constrains. Reality: ys[0] is even.
  let ys = xs.map(proc(x: int): int = x * 2)
  if ys.len > 0 and ys[0] == 3:
    symexTarget("s7_map_array")

# ---- closure descent ---------------------------------------------------------

proc s7InlineLive(x: int) =
  ## maxClosureInlineCount = 1: `g`'s body reaches `f` over the budget, so
  ## `f(y)` is a value the walk never computed.
  let g = proc(y: int): int =
    let f = proc(z: int): int = z + 1
    f(y) + 1
  let r = g(x)
  if r != x + 2:
    symexTarget("s7_inline_live")

proc s7UncertainLive(a, b: bool) =
  ## The closure body's only arm is spurious-tainted (bool ordering is a
  ## fresh symbol), so it is dropped from the ground axioms
  ## (`ceClosureBodyUncertain`): the call's result is free on that arm.
  let f = proc(p, q: bool): bool = p < q
  if f(a, b):
    symexTarget("s7_uncertain_live")

proc s7CloRaise(a: int) =
  ## A raise inside a closure body (DivByZeroDefect at a == 0) must reach the
  ## caller exactly as a named callee's does.
  let f = proc(x: int): int = 10 div x
  let y = f(a)
  if y == 12345:
    symexTarget("s7_clo_raise")

proc s7CloAlwaysRaise(a: int) =
  ## Every body path raises: no value-bearing exit. Reality never reaches
  ## the label.
  let f = proc(x: int): int =
    raise newException(ValueError, "no")
  let y = f(a)
  if y == 5:
    symexTarget("s7_clo_always_raise")

type S7Box = ref object
  v: int

proc s7CloHeap(p: S7Box) =
  ## Two applications of one closure with a heap write between them: the
  ## results differ in reality (`p.v` then `p.v + 1`).
  if p != nil and p.v < 1000 and p.v > -1000:
    let f = proc(x: int): int = p.v + x
    let a = f(0)
    p.v = p.v + 1
    let b = f(0)
    if a != b:
      symexTarget("s7_clo_heap")

proc s7Isolation(a, b: int) =
  ## The argument's division deposits its raise predicate BEFORE the
  ## closure body is descended; the body's own lowering must not wipe it.
  let f = proc(x: int): int = (if x > 0: 1 else: 2)
  let y = f(10 div b)
  if y == 12345:
    symexTarget("s7_isolation")

# ---- parseInt gate (a cross-path solver sink) ---------------------------------

proc s7ParseNeg(s: string) =
  ## `parseInt("-x")` raises ValueError in Nim.
  if s.len == 2 and s[0] == '-' and s[1] == 'x':
    discard parseInt(s)

proc s7ParseCross(s: string; b: bool) =
  ## The parseInt on the `b` arm must not constrain the other arm's `s`.
  if b:
    discard parseInt(s)
  else:
    if s.len == 2 and s[0] == '-' and s[1] == 'x':
      symexTarget("s7_parse_cross")

# ---- guards ------------------------------------------------------------------

proc s7CleanLive(a: int) =
  let f = proc(x: int): int = (if x > 0: 1 else: 2)
  if f(a) == 2:
    symexTarget("s7_clean_live")

proc s7CleanDead(a: int) =
  let f = proc(x: int): int = (if x > 0: 1 else: 2)
  if f(a) == 3:
    symexTarget("s7_clean_dead")

proc s7CleanTwice(a: int) =
  ## Two occurrences with EQUAL arguments must still agree (each occurrence's
  ## result is fully defined by its own ground axioms).
  let f = proc(x: int): int = (if x > 0: 1 else: 2)
  if f(a) != f(a):
    symexTarget("s7_clean_twice")

proc s7DivTen(x: int): int = 10 div x

proc s7NamedRaise(a: int) =
  ## Control for s7CloRaise: the same division through a named callee.
  let y = s7DivTen(a)
  if y == 12345:
    symexTarget("s7_named_raise")

# =============================================================================
# (a) classes
# =============================================================================

suite "RFC-0005 S7 (a) -- the closure/HOF kinds leave the ⊤ default":

  test "ceUnsupportedHof (closure never applied: raises and captures dropped) is dcSubstituted":
    check classOf(ceUnsupportedHof) == dcSubstituted

  test "ceClosureUnknownCallee (fixed-name stand-in, arguments never lowered) is dcSubstituted":
    check classOf(ceClosureUnknownCallee) == dcSubstituted

  test "ceClosureBodyUncertain (per-occurrence result free on the tainted arm) is dcFreshSymbol":
    check classOf(ceClosureBodyUncertain) == dcFreshSymbol

  test "ceClosureBodyDiverged (the caller continuation is made infeasible: a halt) is dcOmitted":
    check classOf(ceClosureBodyDiverged) == dcOmitted

  test "ceInlineBudgetExceeded stays dcSubstituted (S6a) and ceNotImplemented / feExtractionFailed stay dcNoAnswer":
    check classOf(ceInlineBudgetExceeded) == dcSubstituted
    check classOf(ceNotImplemented) == dcNoAnswer
    check classOf(feExtractionFailed) == dcNoAnswer

# =============================================================================
# (b) flips
# =============================================================================

suite "RFC-0005 S7 (b) -- value-substituting declines taint the path":

  test "RED (§5): a witness through __hofFilterUnsupported is a spurious candidate, never a clean hit":
    let r = runSymex(progOf(s7Filter), tLabel("s7_filter"))
    checkpoint(show(r))
    check r.errors.hasKind(ceUnsupportedHof)
    check r.status != sxSat
    check r.spuriousCandidate

  test "a witness through __hofMapUnsupported is a spurious candidate":
    let r = runSymex(progOf(s7MapCapture), tLabel("s7_map_capture"))
    checkpoint(show(r))
    check r.errors.hasKind(ceUnsupportedHof)
    check r.status != sxSat
    check r.spuriousCandidate

  test "the mapArray path records its decline and taints (was a clean false sxSat)":
    let r = runSymex(progOf(s7MapArray), tLabel("s7_map_array"))
    checkpoint(show(r))
    check r.errors.hasKind(ceUnsupportedHof)
    check r.status != sxSat
    check r.spuriousCandidate

  test "an over-budget closure application taints the path (ceInlineBudgetExceeded)":
    let r = runSymex(progOf(s7InlineLive), tLabel("s7_inline_live"), inlineOne)
    checkpoint(show(r))
    check r.errors.hasKind(ceInlineBudgetExceeded)
    check r.status != sxSat
    check r.spuriousCandidate

  test "a dropped tainted closure arm taints the calling path (ceClosureBodyUncertain + descent join)":
    let r = runSymex(progOf(s7UncertainLive), tLabel("s7_uncertain_live"))
    checkpoint(show(r))
    check r.errors.hasKind(ceClosureBodyUncertain)
    check r.status != sxSat
    check r.spuriousCandidate

suite "RFC-0005 S7 (b) -- closure descent and cross-path sinks":

  test "a raise inside a closure body reaches the caller (was a false sxUnsat)":
    let r = runSymex(progOf(s7CloRaise), anyRaise)
    checkpoint(show(r))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedTypeId == "DivByZeroDefect"

  test "a closure whose every path raises never reaches the label (was a false sxSat)":
    let r = runSymex(progOf(s7CloAlwaysRaise), tLabel("s7_clo_always_raise"))
    checkpoint(show(r))
    check r.status != sxSat
    check r.candidates.len == 0

  test "two applications of one closure are not correlated through a shared result term (was a false sxUnsat)":
    let r = runSymex(progOf(s7CloHeap), tLabel("s7_clo_heap"))
    checkpoint(show(r))
    check r.status == sxSat
    check r.candidates.len == 0

  test "a raise predicate deposited before a closure call survives the descent (was a false sxUnsat)":
    let r = runSymex(progOf(s7Isolation), tRaisedExn("DivByZeroDefect"))
    checkpoint(show(r))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedTypeId == "DivByZeroDefect"

  test "parseInt(\"-x\") raises (the digits gate no longer prunes it globally)":
    let r = runSymex(progOf(s7ParseNeg), anyRaise)
    checkpoint(show(r))
    check r.status == sxRaised
    if r.status == sxRaised: check r.raisedTypeId == "ValueError"

  test "a parseInt on one arm does not constrain a sibling arm (was a false sxUnsat)":
    let r = runSymex(progOf(s7ParseCross), tLabel("s7_parse_cross"))
    checkpoint(show(r))
    check r.status == sxSat
    check r.candidates.len == 0

# =============================================================================
# (c) guards
# =============================================================================

suite "RFC-0005 S7 (c) -- clean closures stay exact":

  test "a clean closure's reachable label is a clean sxSat":
    let r = runSymex(progOf(s7CleanLive), tLabel("s7_clean_live"))
    checkpoint(show(r))
    check r.status == sxSat
    check r.candidates.len == 0

  test "a clean closure's dead label is sxUnsat":
    let r = runSymex(progOf(s7CleanDead), tLabel("s7_clean_dead"))
    checkpoint(show(r))
    check r.status == sxUnsat

  test "two occurrences with equal arguments agree: the label is sxUnsat":
    let r = runSymex(progOf(s7CleanTwice), tLabel("s7_clean_twice"))
    checkpoint(show(r))
    check r.status == sxUnsat

  test "control: the named-callee twin of s7CloRaise is sxRaised":
    let r = runSymex(progOf(s7NamedRaise), anyRaise)
    checkpoint(show(r))
    check r.status == sxRaised

# =============================================================================
# (d) the S9 safety precondition
# =============================================================================

suite "RFC-0005 S7 (d) -- S9 precondition: without the vetoes, no S7 SUT is a clean sxSat":
  ## `rfc0005UnvetoedStatus` is `decideVerdict(…, vetoed = false)` over the
  ## run's own pools. The vetoes stay in this slice; S9 deletes them only
  ## because this holds for every closure / HOF decline.

  test "filter decline (__hofFilterUnsupported)":
    let r = runSymex(progOf(s7Filter), tLabel("s7_filter"))
    checkpoint(show(r) & " unvetoed=" & $rfc0005UnvetoedStatus)
    check r.status == sxUnknown
    check rfc0005UnvetoedStatus != sxSat

  test "capturing map decline (__hofMapUnsupported)":
    let r = runSymex(progOf(s7MapCapture), tLabel("s7_map_capture"))
    checkpoint(show(r) & " unvetoed=" & $rfc0005UnvetoedStatus)
    check rfc0005UnvetoedStatus != sxSat

  test "mapArray decline":
    let r = runSymex(progOf(s7MapArray), tLabel("s7_map_array"))
    checkpoint(show(r) & " unvetoed=" & $rfc0005UnvetoedStatus)
    check rfc0005UnvetoedStatus != sxSat

  test "inline-budget decline (ceInlineBudgetExceeded)":
    let r = runSymex(progOf(s7InlineLive), tLabel("s7_inline_live"), inlineOne)
    checkpoint(show(r) & " unvetoed=" & $rfc0005UnvetoedStatus)
    check rfc0005UnvetoedStatus != sxSat

  test "dropped tainted arm (ceClosureBodyUncertain)":
    let r = runSymex(progOf(s7UncertainLive), tLabel("s7_uncertain_live"))
    checkpoint(show(r) & " unvetoed=" & $rfc0005UnvetoedStatus)
    check rfc0005UnvetoedStatus != sxSat

  test "diverged body (ceClosureBodyDiverged)":
    let r = runSymex(progOf(s7CloAlwaysRaise), tLabel("s7_clo_always_raise"))
    checkpoint(show(r) & " unvetoed=" & $rfc0005UnvetoedStatus)
    check rfc0005UnvetoedStatus != sxSat

  test "control: a clean closure's reachable label IS a clean sxSat unvetoed (the observable is live)":
    let r = runSymex(progOf(s7CleanLive), tLabel("s7_clean_live"))
    checkpoint(show(r) & " unvetoed=" & $rfc0005UnvetoedStatus)
    check rfc0005UnvetoedStatus == sxSat

# =============================================================================
# (e) structural
# =============================================================================

const smtDir = currentSourcePath.parentDir() / ".." / "src" / "nelli" / "smt"

proc runtimeFiles(): seq[string] =
  for f in walkFiles(smtDir / "runtime*.nim"): result.add f

proc routineName(line: string): string =
  for kw in ["proc ", "template ", "func ", "iterator ", "macro ", "method "]:
    if line.startsWith(kw):
      var i = kw.len
      var name = ""
      while i < line.len and (line[i].isAlphaNumeric or line[i] == '_'):
        name.add line[i]
        inc i
      return name
  ""

proc codeLines(path: string): seq[tuple[routine, line: string]] =
  ## Non-comment lines of `path`, tagged with their enclosing top-level
  ## routine.
  var routine = "<top-level>"
  for raw in readFile(path).splitLines():
    let r = routineName(raw)
    if r.len > 0: routine = r
    let t = raw.strip()
    if t.len == 0 or isCommentLine(t): continue
    result.add (routine, t)

proc routineBody(path, name: string): seq[string] =
  for (r, t) in codeLines(path):
    if r == name: result.add t

suite "RFC-0005 S7 (e) -- structural: sinks, funnel, drain map":

  test "the solver-sink drain list in trySolve is exactly the audited set (§2.4, pinned against the code)":
    ## §2.4 tabled seven sinks; the code has fewer. Two rows name ONE pool
    ## (the "closure ground axioms" row and `currentClosureCallAxioms`), and
    ## S7 deleted the parseInt digits-gate pool. What trySolve asserts is the
    ## path's own `pc` / `defectSurvivorPc` plus two global pools:
    ##   currentClosureCallAxioms -- minted only from `taint == {}` body arms;
    ##       each mentions only its own occurrence's fresh result (definitional)
    ##   stripDecompConds         -- definitional over per-occurrence fresh
    ##       strings (unique decomposition): admits every channel.
    ## The call cache (admits `taint == {}` only) and the fresh `Path` roots
    ## are sinks outside trySolve, pinned below.
    var drained: seq[string]
    for t in routineBody(smtDir / "runtime.nim", "trySolve"):
      if t.startsWith("for c in ") and t.endsWith(":"):
        drained.add t["for c in ".len ..< t.len - 1]
    check drained == @["path.pc", "path.defectSurvivorPc",
                       "currentClosureCallAxioms", "stripDecompConds"]

  test "the parseInt digits-gate pool is gone from the source":
    for f in runtimeFiles():
      for (r, t) in codeLines(f):
        check "parseIntGate" notin t

  test "the call cache admits only a clean callee path":
    var gated = false
    for t in routineBody(smtDir / "runtime.nim", "walk"):
      if "frame.returnedPaths[0].taint == {}" in t: gated = true
    check gated

  test "the closure descent root is clean and the only fresh Path root in applyClosureGround":
    let body = routineBody(smtDir / "runtime.nim", "applyClosureGround")
    var roots = 0
    for t in body:
      if "Path(pc:" in t: inc roots
    check roots == 1
    check body.anyIt("taint: {}," in it)

  test "closure / HOF declines record ONLY through closureDegrade (the closure sink never bypasses the path)":
    var sinkWrites, syncCalls: seq[string]
    var degradeSites = 0
    var dsClosureSites: seq[string]
    for f in runtimeFiles():
      for (r, t) in codeLines(f):
        if "currentClosureCallErrors.add" in t: sinkWrites.add r
        if "syncClosureCallError(" in t and not t.startsWith("proc "):
          syncCalls.add r
        if t.startsWith("closureDegrade("): inc degradeSites
        if "dsClosure)" in t: dsClosureSites.add r
    check sinkWrites == @["degrade", "closureDegrade"]
    check syncCalls == @["closureDegrade"]
    check dsClosureSites == @["rfc0005S1CarrierProbe"]
    ## unresolved callee x2, raw-wrap fallback, no-walk and over-budget
    ## guards, uncertain arm, zero-default havoc, HOF filter / capturing map /
    ## mapArray / fold.
    check degradeSites == 11

  test "every closure-sink site's kind is a classified S7 kind, never a ⊤ default":
    for f in runtimeFiles():
      for (r, t) in codeLines(f):
        if t.startsWith("closureDegrade("):
          checkpoint(t)
          let k = t["closureDegrade(".len ..< t.find(',')]
          check k in ["ceClosureUnknownCallee", "feUnsupportedOp",
                      "ceInlineBudgetExceeded", "ceClosureBodyUncertain",
                      "feUnsupportedOpHavoc", "ceUnsupportedHof"]

  test "the closure result is a fresh constant per occurrence, not the funcSym application":
    let body = routineBody(smtDir / "runtime.nim", "applyClosureGround")
    check body.anyIt("Z3_mk_fresh_const(ctx.raw, \"__closureRet\"," in it)
    check not body.anyIt("Z3_mk_app(" in it)

  test "the closure frame's escaped raises are captured before popFrame":
    let body = routineBody(smtDir / "runtime.nim", "applyClosureGround")
    var capIdx, popIdx = -1
    for i, t in body:
      if t == "let escapedRaises = w.frame.escaped": capIdx = i
      if t == "popFrame(w)": popIdx = i
    check capIdx >= 0 and popIdx == capIdx + 1

  test "every error sink runSymexImpl drains feeds a run-coordinate operand (no sink escapes both channels)":
    ## The path channel is the funnels' token; the run channel is derived
    ## here. Every drained sink lands in `exnWarnings` or `closureErrs`, and
    ## `runTaint` is derived from those plus `prog.parseErrors`. The one
    ## sink outside it is `extractionErrors`: recorded on the SAT branch
    ## after the verdict (witness extraction) -- S10's replay gate owns it.
    let body = routineBody(smtDir / "runtime.nim", "runSymexImpl")
    var targets: seq[string]
    for t in body:
      for helper in ["drainSinkUnion(", "drainDedupedByMsg("]:
        if t.startsWith(helper):
          targets.add t[helper.len ..< t.find(',')]
    check targets.len >= 9
    for x in targets: check x in ["exnWarnings", "closureErrs"]
    let rt = body.filterIt(it.startsWith("w.runTaint = "))
    check rt.len == 1
    check "runTaintOf(exnWarnings)" in rt[0]
    check "runTaintOf(prog.parseErrors)" in rt[0]
    check body.anyIt("runTaintOf(closureErrs)" in it)

suite "RFC-0005 S7 -- walker version pin":

  test "walker version floor >= 146 (S7 closure / HOF path taint, cross-path sinks)":
    check parseInt(symexWalkerVersion) >= 146
