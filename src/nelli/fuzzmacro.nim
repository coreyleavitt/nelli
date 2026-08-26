## RFC-fuzzer-nextgen E1 stage 2: the call-site `fuzz(...)` macro (C4).
##
## `Strategy.run`/a property `proc` are opaque runtime closures — Nim cannot
## recover source from them, and a fresh OS process (Track E) cannot inherit
## them across `exec`. The RESOLVED design (RFC §Open items, the opaque-
## closure boundary) is a `macro` that captures the strategy/property
## *construction expressions* at the call site, not their closure values:
##
## - **Track G** (later, C7) gets the property as an emittable **typed proc
##   symbol** — the walker's ONLY ingestion door is `fn: typed` -> `getImpl`
##   -> `parseProc` -> `walk` (verified in code, `symex.nim:461`/`:1627`), so
##   this macro's job is to make sure a named, module-scope proc symbol
##   EXISTS for the property, lifting an inline `proc(x: T) = ...` literal to
##   one when needed (`liftPropIfNeeded` below). It does not itself drive the
##   walker (C7 is a separate follow-up).
## - **Track E** gets worker reconstruction with no new user-facing API: the
##   same macro emits a hidden worker-mode entry, keyed by a stable call-site
##   id, that RE-RUNS the captured construction to rebuild a fresh
##   `(Strategy[T], prop)` pair instead of reusing the parent's objects. At E1
##   this is exercised in-process only (`runWorkerReentry`, C5) — real
##   fork/spawn dispatch is Track E's job (E2a+).
##
## Two contracts, not one (round-2 RFC fix): Track G's need is *syntactic*
## (capture the AST); Track E's is *semantic* (the capture must be safely
## re-executable, unmodified, from scratch). The compile-time checks below
## (`validateCapture`, C6, this cycle) exist for Track E's contract — they
## reject a capture that closes over a runtime local (not reconstructible at
## all) or that calls a known-impure stdlib proc (reconstructs to a possibly
## different value each time, best-effort denylist, not sound).
##
## C4 is the behavior-preserving front: `fuzz(<strategyExpr>, <propExpr>,
## <settings?>)` expands to the exact wiring `tfuzzloop.nim`/
## `tfuzzcovcorpus.nim` already write by hand — a fresh `CoverageFrontier`
## plus `fuzz(s, inProcessTarget(prop), frontier, settings)` — so it is a
## drop-in, no-behavior-change entry point. C5 adds the worker-mode registry.

import std/[macros, tables, options]
import ./fuzz, ./fuzzworker
import ./symex
import ./smt/transparency
export symex
# RFC-fuzzer-nextgen G3 C4. `parseEntryImpl`'s (and our own) generated code
# is SPLICED into the macro CALL SITE's module (e.g. a test file that only
# `import nelli`) — its free identifiers (IR constructor names, `IRExprKind`
# enum values like `iekStrLen`, `ConcolicParamBinding`, `concolicFlip`
# itself, etc.) resolve against THAT scope, not this module's. Without
# re-exporting, only a caller that separately `import nelli/symex`d would
# have them in scope — re-exporting here is what makes `fuzz(...)`'s now-
# unconditional real-bridge construction work for every macro caller,
# mirroring `fuzz.nim`'s own `export coverage` for the identical reason.
# RFC-fuzzer-nextgen G3 C4: the real concolic bridge. `fuzz.nim` stays
# Z3-free by design (`ConcolicOutcomeTag`/`ConcolicCoverageTag`/
# `ConcolicBridgeResult`/`ConcolicBridgeEntry` there are a type-erased
# mirror of this module's real `ConcolicFlipOutcome`/`ConcolicCoverageOutcome`
# /`concolicFlip` types) — but THIS module is where the macro captures a
# walkable typed proc symbol for the property (the same symbol Track G's
# walker needs), so it is the one place a REAL Z3 bridge can be built, per
# the fuzz.nim `ConcolicOutcomeTag` doc comment ("the call-site macro,
# which DOES import the walker"). This makes `import nelli` (which
# includes this module) pull in Z3 — an accepted, already-anticipated
# consequence of wiring the real bridge, not a new tradeoff introduced
# here.

# --- worker-mode registry (C5) -----------------------------------------------

type
  WorkerEntry* = proc(input: ChoiceSeq): Observation[void] {.closure.}
    ## Type-erased over T: `Observation[T]`'s fields never mention T (verdict/
    ## coverage/message/crash/runResult are all concrete types already), so a
    ## single non-generic registry can hold entries for `fuzz(...)` call sites
    ## instantiated at any T without a variant/case-object dance.

var nelliWorkerRegistry: Table[string, WorkerEntry] = initTable[string, WorkerEntry]()
  ## RFC-fuzzer-nextgen E1 (C5): process-global call-site-id -> reconstruction
  ## entry. Populated by each `fuzz(...)` macro expansion's own execution
  ## (registration happens when that call site actually runs, matching how a
  ## real worker's argv `--nelli-worker=<id>` dispatch — E2a+ — can only
  ## re-enter a site the parent process actually reached).

var nelliLastFuzzCallSiteId*: string
  ## RFC-fuzzer-nextgen E1 (C5): the call-site id most recently registered by
  ## a `fuzz(...)` expansion. A test/introspection seam ONLY — it lets a test
  ## exercise `runWorkerReentry` in-process without a real argv dispatcher
  ## (that's E2a+, which receives the id via argv, not by reading this var).

proc nelliRegisterWorkerEntry*(id: string; entry: WorkerEntry) =
  ## Register (or replace) the worker-mode reconstruction entry for a
  ## `fuzz(...)` call site. Called by the macro's own expansion; not meant to
  ## be called directly by users.
  nelliWorkerRegistry[id] = entry
  nelliLastFuzzCallSiteId = id

proc runWorkerReentry*(id: string; input: ChoiceSeq): Observation[void] =
  ## RFC-fuzzer-nextgen E1 (C5): the in-process worker-mode dispatch path.
  ## Looks up `id`'s registered entry and runs it — the entry RECONSTRUCTS
  ## strategy+property by re-running the captured construction expressions
  ## (a fresh call to `stratExpr`/a fresh reference to the property's proc
  ## symbol), never reusing the parent call site's own objects — then submits
  ## `input` to a freshly-built `Worker`. Raises `KeyError` for an
  ## unregistered id (mirrors a real worker's "unknown call-site id"
  ## bootstrap failure; E2a+ turns that into the RFC's circuit-breaker
  ## diagnostic instead of a raw exception, out of scope here).
  nelliWorkerRegistry[id](input)

# --- compile-time capture checks (C6) ----------------------------------------

const impurityDenylist = ["getEnv", "paramStr", "readFile", "getTime", "now", "rand", "random"]
  ## RFC §Open items (impurity denylist): best-effort, name-based, not sound —
  ## an impure proc outside this list, or impurity behind an indirect call,
  ## slips through. Documented limitation, not a claim of soundness.

proc collectBoundNames(n: NimNode; bound: var seq[string]) =
  ## Best-effort: collect every identifier NAME bound *within* the captured
  ## tree itself (proc/lambda params, `let`/`var` locals, for-loop vars) so
  ## `checkCapture` below can tell "the property's own parameter `x`" (fine)
  ## from "a free reference to an enclosing scope's `x`" (not fine). Matched
  ## by name, not symbol identity (a shadowing edge case could slip through —
  ## the same best-effort tradeoff as the impurity check).
  case n.kind
  of nnkIdentDefs:
    for i in 0 ..< n.len - 2:
      if n[i].kind in {nnkIdent, nnkSym}: bound.add n[i].strVal
  of nnkVarTuple:
    for i in 0 ..< n.len - 1:
      if n[i].kind in {nnkIdent, nnkSym}: bound.add n[i].strVal
  of nnkForStmt:
    for i in 0 ..< n.len - 2:
      if n[i].kind in {nnkIdent, nnkSym}: bound.add n[i].strVal
  of nnkProcDef, nnkFuncDef, nnkLambda, nnkMethodDef, nnkIteratorDef, nnkTemplateDef:
    # RFC-fuzzer-nextgen G6: pre-existing gap, not previously exercised — a
    # single-expression proc/lambda body (`proc(x: T): U = expr`, the shape
    # a strategy combinator's inline fn argument commonly takes) desugars to
    # `result = expr`, an auto-generated `nskResult` symbol this proc never
    # bound. Every `fuzz(...)` call passing an inline-lambda combinator
    # (`.map(proc(x: int): int = x * 2 + 1)`) tripped `checkCapture`'s
    # non-reconstructible-identifier rejection on `result` itself — caught
    # by G6's own headline test, the first `fuzz(...)` caller to pass an
    # inline lambda as (part of) the strategy expression. `result` is bound
    # whenever a nested routine declares a non-void return type; matched by
    # NAME only (not symbol identity), same caveat as every other name here.
    if n.len > 3 and n[3].kind == nnkFormalParams and n[3].len > 0 and n[3][0].kind != nnkEmpty:
      bound.add "result"
  else: discard
  for c in n: collectBoundNames(c, bound)

const nonReconstructibleSymKinds = {nskVar, nskLet, nskParam, nskForVar, nskTemp, nskResult}
  ## Any runtime value binding — param, local `let`/`var` (mutable OR not),
  ## for-loop var — referenced from OUTSIDE the captured tree is rejected.
  ## Deliberately includes plain module-scope `let`/`var`, not just proc
  ## locals: the RFC's example list names "an enclosing let, a proc param, a
  ## runtime-config value, a mutable global" together — worker re-entry does
  ## not replay the module from `main` to the call site, so even a top-level
  ## `var`/non-const `let` may not have run its initializer yet when the
  ## reconstruction proc is invoked in isolation. `const`/enum fields are
  ## already inlined by sem-check before this macro ever sees the tree, so
  ## they never appear as `nnkSym` nodes here — no special-casing needed.

proc checkCapture(n: NimNode; bound: seq[string]; label: string) =
  if n.kind == nnkSym:
    if n.symKind in nonReconstructibleSymKinds and n.strVal notin bound:
      error("fuzz: " & label & " captures non-reconstructible identifier '" &
            n.strVal & "' from an enclosing scope; worker re-entry needs a " &
            "module-scope-reconstructible expression — hoist '" & n.strVal &
            "' to a const, or restructure the " & label &
            " to a module-scope constructor call", n)
    if n.symKind == nskProc and n.strVal in impurityDenylist:
      error("fuzz: " & label & " initializer calls '" & n.strVal &
            "', which is on the best-effort impurity denylist (" &
            "getEnv/paramStr/readFile/getTime/now/rand/random) — worker " &
            "reconstruction re-runs this call in a fresh process/instance, " &
            "so an impure initializer can reconstruct a drifted value", n)
  for c in n: checkCapture(c, bound, label)

proc validateCapture(n: NimNode; label: string) =
  ## RFC-fuzzer-nextgen E1 (C6): reject at COMPILE time a capture that is not
  ## safely re-runnable from scratch — (a) a free reference to a runtime
  ## local/param/mutable-global (`nonReconstructibleSymKinds`), (b) a call to
  ## a best-effort-denylisted impure stdlib proc. Both name the offending
  ## identifier in the error.
  var bound: seq[string] = @[]
  collectBoundNames(n, bound)
  checkCapture(n, bound, label)

# --- G6: transparency-descriptor AST classification -------------------------
#
# RFC-fuzzer-nextgen G6. The G1b/G3 classifier above (`countFormalParams`'s
# doc) was positional-only: every property parameter got `cbDrawLinked`
# regardless of what actually produced it, so `integers().map(f)` already
# broke the symbolic link at the FIRST combinator (Z3 would solve for the
# wrong equation — the raw draw, not `f(draw)` — and the replay would
# disprove it, silently zeroing yield for every mapped/filtered strategy).
#
# This section walks the CAPTURED strategy-construction expression (the
# SAME typed AST `stratExpr`/`stratCopyForEntry` already is — the macro's own
# `typed` parameter, proven walkable by direct inspection: a chain like
# `s.map(f)` types as `nnkCall(sym"map", s, f)`, `f` (an inline
# `proc(x: T): U = …` literal) arrives wrapped in `nnkHiddenStdConv` around
# an `nnkLambda`, whose single-expression body compiles to
# `nnkAsgn(sym"result", <expr>)` at index 6 of the 8-child lambda layout) and
# classifies it into `smt/transparency`'s `TransparencyDescriptor` via the
# SAME composition algebra G6 C1 proved closed. Only `map`/`filter`/`flatMap`
# are recognized combinators (the RFC's own "Classification from the
# captured AST" scope); anything else (a bare strategy constructor call, a
# strategy referenced by a pre-built `let` variable, an unrecognized
# combinator) classifies as `dkIdentity` — the SAME assumption the pre-G6
# code always made for every param, so this is never a regression, only an
# upgrade for the chains this cycle DOES recognize.
#
# Scope cuts (deliberate, not silent): (1) only the SINGLE-STRATEGY,
# single-property-parameter shape is classified this way — a multi-param
# property's N-ary applicative `map(sa, sb, …, f)` strategy expression falls
# back to the pre-G6 positional classifier unchanged (decomposing an N-ary
# product back into its own per-component chains is additional AST-walking
# the RFC's headline does not require); (2) `flatMap`/`branching` is
# CLASSIFIED (produces a real `dkBranching` descriptor for a simple 2-way
# `if`/`else` over an affine-comparable guard) but not yet WIRED into a
# runtime binding — a resolved-branching binding needs the CONCRETE trace to
# pick the taken case (only known at bridge-invocation time), which is a
# real further increment; wiring falls back to the pre-G6 `cbDrawLinked`
# for a `dkBranching` result, same as `dkOpaque`, so BOTH are safe no-worse-
# than-before defaults. `identity`/`affine`/`predicated` (the RFC's own
# headline category) ARE fully wired.

proc unwrapValueExpr(n: NimNode): NimNode =
  ## Peel wrapper nodes that carry no semantic content of their own down to
  ## the expression they wrap: `nnkHiddenStdConv`/`nnkHiddenCallConv` (last
  ## child is the real value), `nnkStmtListExpr`/`nnkStmtList` (last
  ## non-Empty child — the "value" of a Nim statement list).
  var cur = n
  while true:
    case cur.kind
    of nnkHiddenStdConv, nnkHiddenCallConv:
      cur = cur[^1]
    of nnkStmtListExpr, nnkStmtList:
      var last = newEmptyNode()
      for c in cur:
        if c.kind != nnkEmpty: last = c
      if last.kind == nnkEmpty: return cur
      cur = last
    else:
      return cur

proc procShapeOf(raw: NimNode): tuple[ok: bool, paramName: string, body: NimNode] =
  ## `raw` is a `map`/`filter`/`flatMap` fn ARGUMENT node — either an inline
  ## `proc(x: T): U = …` lambda literal (wrapped in `nnkHiddenStdConv`) or a
  ## reference to a named proc/closure (`nnkSym`, resolved via `getImpl`).
  ## Returns `ok = false` for anything else (a runtime closure VALUE with no
  ## recoverable body — the same opaque-closure boundary `validateCapture`
  ## already names) or a proc whose shape this cycle doesn't recognize
  ## (more than one parameter — `map`/`filter`/`flatMap`'s fn is always
  ## unary by the combinator's own signature, so this only guards against a
  ## malformed match).
  let unwrapped = unwrapValueExpr(raw)
  var procNode: NimNode
  if unwrapped.kind in {nnkLambda, nnkProcDef}:
    procNode = unwrapped
  elif unwrapped.kind == nnkSym and unwrapped.symKind == nskProc:
    procNode = unwrapped.getImpl
  else:
    return (false, "", newEmptyNode())
  let formalParams = procNode.params
  if formalParams.len != 2 or formalParams[1].len != 3:
    return (false, "", newEmptyNode())
  let paramName = formalParams[1][0].strVal
  var body = procNode.body
  # `proc(x: T): U = expr` compiles its single-expression body to
  # `result = expr` (an `nnkAsgn`) — unwrap to the VALUE expression itself;
  # an explicit `return expr` unwraps the same way.
  if body.kind == nnkStmtList and body.len >= 1:
    var last = body[^1]
    if last.kind == nnkAsgn and last[0].kind == nnkSym and last[0].strVal == "result":
      body = last[1]
    elif last.kind == nnkReturnStmt:
      body = last[0]
    else:
      body = last
  elif body.kind == nnkAsgn and body[0].kind == nnkSym and body[0].strVal == "result":
    body = body[1]
  (true, paramName, unwrapValueExpr(body))

proc affineOf(e: NimNode, paramName: string): Option[tuple[a, b: int64]] =
  ## Recognize a literal-affine expression (`+`/`-`/`*` over the sole param
  ## and integer literals) — `x`, `x*2+1`, `2*x+1`, `x-3`, `-x`, a bare
  ## constant, etc. Anything outside this closed shape (another free
  ## identifier, a non-`+`/`-`/`*` op, `param*param`) returns `none` — the
  ## caller degrades to `dkOpaque`, never guesses.
  let e = unwrapValueExpr(e)
  case e.kind
  of nnkSym, nnkIdent:
    if e.strVal == paramName: some((1'i64, 0'i64)) else: none((int64, int64))
  of nnkIntLit..nnkInt64Lit:
    some((0'i64, e.intVal))
  of nnkPrefix:
    if e.len == 2 and e[0].kind in {nnkSym, nnkIdent} and e[0].strVal == "-":
      let inner = affineOf(e[1], paramName)
      if inner.isSome: some((-inner.get.a, -inner.get.b)) else: none((int64, int64))
    else: none((int64, int64))
  of nnkInfix:
    if e.len != 3 or e[0].kind notin {nnkSym, nnkIdent}: return none((int64, int64))
    let opStr = e[0].strVal
    let lhs = affineOf(e[1], paramName)
    let rhs = affineOf(e[2], paramName)
    if lhs.isNone or rhs.isNone: return none((int64, int64))
    case opStr
    of "+": some((lhs.get.a + rhs.get.a, lhs.get.b + rhs.get.b))
    of "-": some((lhs.get.a - rhs.get.a, lhs.get.b - rhs.get.b))
    of "*":
      if lhs.get.a == 0: some((lhs.get.b * rhs.get.a, lhs.get.b * rhs.get.b))
      elif rhs.get.a == 0: some((rhs.get.b * lhs.get.a, rhs.get.b * lhs.get.b))
      else: none((int64, int64))
    else: none((int64, int64))
  else: none((int64, int64))

proc flipPredOp(op: PredOp): PredOp =
  case op
  of poEq: poEq
  of poNe: poNe
  of poLt: poGt
  of poLe: poGe
  of poGt: poLt
  of poGe: poLe

proc negatePredOp(op: PredOp): PredOp =
  case op
  of poEq: poNe
  of poNe: poEq
  of poLt: poGe
  of poLe: poGt
  of poGt: poLe
  of poGe: poLt

proc predOpOf(opStr: string): Option[PredOp] =
  case opStr
  of "==": some(poEq)
  of "!=": some(poNe)
  of "<":  some(poLt)
  of "<=": some(poLe)
  of ">":  some(poGt)
  of ">=": some(poGe)
  else: none(PredOp)

proc predicateOf(e: NimNode, paramName: string): Option[PredicateSpec] =
  ## Recognize `affineExpr op literal` (either operand order — Nim's
  ## typed AST rewrites `x > 5` to `5 < x` via `>`'s own template
  ## definition, so BOTH orders occur in practice; the literal side is
  ## whichever one reduces to `a == 0` under `affineOf`) for the closed
  ## comparison-op set. `not (…)` unwraps and negates (best-effort — covers
  ## a `!=` that itself desugars through a `not`).
  let e = unwrapValueExpr(e)
  if e.kind == nnkPrefix and e.len == 2 and e[0].kind in {nnkSym, nnkIdent} and e[0].strVal == "not":
    let inner = predicateOf(e[1], paramName)
    if inner.isSome:
      let p = inner.get
      return some(PredicateSpec(a: p.a, b: p.b, op: negatePredOp(p.op), lit: p.lit))
    return none(PredicateSpec)
  if e.kind != nnkInfix or e.len != 3 or e[0].kind notin {nnkSym, nnkIdent}:
    return none(PredicateSpec)
  let opOpt = predOpOf(e[0].strVal)
  if opOpt.isNone: return none(PredicateSpec)
  let lhs = affineOf(e[1], paramName)
  let rhs = affineOf(e[2], paramName)
  if lhs.isNone or rhs.isNone: return none(PredicateSpec)
  if rhs.get.a == 0 and lhs.get.a != 0:
    some(PredicateSpec(a: lhs.get.a, b: lhs.get.b, op: opOpt.get, lit: rhs.get.b))
  elif lhs.get.a == 0 and rhs.get.a != 0:
    some(PredicateSpec(a: rhs.get.a, b: rhs.get.b, op: flipPredOp(opOpt.get), lit: lhs.get.b))
  else:
    none(PredicateSpec)

proc classifyStrategyExpr(n: NimNode): TransparencyDescriptor
  ## Forward-declared: mutually recursive with `classifyBranching` (a
  ## `flatMap` case's own body is itself a strategy expression to classify).

proc classifyBranching(paramName: string, ifExprNode: NimNode): Option[seq[BranchingCase]] =
  ## Bounded recognizer: a simple 2-way `if cond: … else: …` EXPRESSION
  ## (`nnkIfExpr`/`nnkElifExpr`/`nnkElseExpr` — the typed-AST shape an
  ## `if` used as a proc's return value takes, distinct from the
  ## `nnkIfStmt` control-flow shape) whose guard is affine-comparable and
  ## whose branches are themselves classifiable strategy expressions. Any
  ## wider shape (3+ arms, a non-affine-comparable guard such as `mod`,
  ## a missing `else`) returns `none` — the caller degrades to `dkOpaque`,
  ## matching the RFC's own "falls back to opaque the instant the split
  ## isn't finite/enumerable [or a case is itself opaque]" rule.
  if ifExprNode.kind != nnkIfExpr or ifExprNode.len != 2: return none(seq[BranchingCase])
  if ifExprNode[0].kind != nnkElifExpr or ifExprNode[1].kind != nnkElseExpr:
    return none(seq[BranchingCase])
  let guard = predicateOf(ifExprNode[0][0], paramName)
  if guard.isNone: return none(seq[BranchingCase])
  let thenDesc = classifyStrategyExpr(unwrapValueExpr(ifExprNode[0][1]))
  let elseDesc = classifyStrategyExpr(unwrapValueExpr(ifExprNode[1][0]))
  if thenDesc.kind == dkOpaque or elseDesc.kind == dkOpaque: return none(seq[BranchingCase])
  some(@[
    BranchingCase(guard: guard.get, then: thenDesc),
    BranchingCase(guard: PredicateSpec(a: guard.get.a, b: guard.get.b,
                                       op: negatePredOp(guard.get.op), lit: guard.get.lit),
                  then: elseDesc),
  ])

proc classifyStrategyExpr(n: NimNode): TransparencyDescriptor =
  ## Walk a strategy-construction expression's typed AST and classify it —
  ## see the section doc comment above for the recognized shapes and scope
  ## cuts. The base case (anything not a recognized `map`/`filter`/`flatMap`
  ## call — a bare `integers(0, 1000)`, a `let`-bound strategy variable, an
  ## unrecognized combinator) is `dkIdentity`: the pre-G6 assumption for
  ## every parameter, kept as the floor so this classifier only ever adds
  ## precision, never removes it.
  let n = unwrapValueExpr(n)
  if n.kind == nnkCall and n.len >= 2 and n[0].kind == nnkSym:
    let name = n[0].strVal
    if name == "map" and n.len == 3:
      let inner = classifyStrategyExpr(n[1])
      let shape = procShapeOf(n[2])
      if shape.ok:
        let aff = affineOf(shape.body, shape.paramName)
        if aff.isSome:
          return compose(inner, dAffine(aff.get.a, aff.get.b))
      return dOpaque()
    elif name == "filter" and n.len == 3:
      let inner = classifyStrategyExpr(n[1])
      let shape = procShapeOf(n[2])
      if shape.ok:
        let pred = predicateOf(shape.body, shape.paramName)
        if pred.isSome:
          return compose(inner, dPredicated(dIdentity(), @[pred.get]))
      return dOpaque()
    elif name == "flatMap" and n.len == 3:
      let inner = classifyStrategyExpr(n[1])
      let shape = procShapeOf(n[2])
      if shape.ok and shape.body.kind == nnkIfExpr:
        let cases = classifyBranching(shape.paramName, shape.body)
        if cases.isSome:
          return compose(inner, dBranching(cases.get))
      return dOpaque()
  dIdentity()

proc bindingExprFor(desc: TransparencyDescriptor, drawIndexLit: NimNode): NimNode =
  ## Flatten a FINISHED (fully composed) `TransparencyDescriptor` into the
  ## NimNode for a runtime `ConcolicParamBinding` construction, emitted
  ## directly into the macro's generated code (primitive int64/enum
  ## literals only — `runtime.nim` never sees this module's descriptor
  ## tree, matching `fuzz.nim`'s own erased-mirror convention). `identity`
  ## is `cbTransformLinked` with `tA=1,tB=0` (equivalent to `cbDrawLinked`
  ## but expressed through the same new binding kind, so a chain that
  ## STARTS with a genuine transform and later composes back to identity —
  ## e.g. `.map(x=>x+1).map(x=>x-1)` — still routes through one consistent
  ## mechanism). `opaque`/`branching` (not yet wired — see the section doc)
  ## fall back to the pre-G6 `cbDrawLinked`, byte-identical to today.
  case desc.kind
  of dkIdentity:
    quote do: ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: `drawIndexLit`,
                                   tA: 1'i64, tB: 0'i64, tConjuncts: @[])
  of dkAffine:
    let aLit = newLit(desc.a)
    let bLit = newLit(desc.b)
    quote do: ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: `drawIndexLit`,
                                   tA: `aLit`, tB: `bLit`, tConjuncts: @[])
  of dkPredicated:
    # `base` is restricted to {identity, affine} for this cycle's classifier
    # (never span-composite — that category has no AST producer yet); a
    # `base` of any other kind here would be a classifier bug, not a
    # runtime possibility, so it is asserted rather than silently mis-
    # flattened.
    doAssert desc.base.kind in {dkIdentity, dkAffine}
    let aLit = newLit(if desc.base.kind == dkAffine: desc.base.a else: 1'i64)
    let bLit = newLit(if desc.base.kind == dkAffine: desc.base.b else: 0'i64)
    var conjNodes: seq[NimNode]
    for c in desc.conjuncts:
      let cA = newLit(c.a)
      let cB = newLit(c.b)
      let cLit = newLit(c.lit)
      let cOp = newLit(case c.op
        of poEq: ccoEq
        of poNe: ccoNe
        of poLt: ccoLt
        of poLe: ccoLe
        of poGt: ccoGt
        of poGe: ccoGe)
      conjNodes.add(quote do: ConcolicConjunct(drawIndex: `drawIndexLit`, a: `cA`, b: `cB`,
                                               op: `cOp`, lit: `cLit`))
    let conjSeq = newTree(nnkBracket, conjNodes)
    quote do: ConcolicParamBinding(kind: cbTransformLinked, tDrawIndex: `drawIndexLit`,
                                   tA: `aLit`, tB: `bLit`, tConjuncts: @(`conjSeq`))
  of dkOpaque, dkSpanComposite, dkBranching:
    quote do: ConcolicParamBinding(kind: cbDrawLinked, drawIndex: `drawIndexLit`)

# --- the macro (C4/C5) --------------------------------------------------------

proc fuzzCallSiteId(n: NimNode): string =
  let li = n.lineInfoObj
  li.filename & ":" & $li.line & ":" & $li.column

proc countFormalParams(formalParams: NimNode): int =
  ## RFC-fuzzer-nextgen G3 C4. `formalParams` is an `nnkFormalParams` node:
  ## child 0 is the return type, children 1.. are `nnkIdentDefs` groups, each
  ## covering ONE OR MORE names sharing a type (`proc f(a, b: int)` is a
  ## single group of 2 names) — mirrors `collectBoundNames`'s `nnkIdentDefs`
  ## counting above. Used to build the concolic bridge's minimal per-param
  ## `ConcolicParamBinding` list (one `cbDrawLinked` binding per property
  ## parameter, positionally — full draw-to-param classification is G6;
  ## `runConcolicCollectImpl` degrades an out-of-range/kind-mismatched
  ## binding to a concretized ground value rather than crashing, so an
  ## imprecise positional guess here is sound, just potentially less useful).
  for i in 1 ..< formalParams.len:
    result += formalParams[i].len - 2

proc propFormalParams(propExpr: NimNode): NimNode =
  ## The property expression's `nnkFormalParams` node — works whether
  ## `propExpr` is an already-named proc symbol (`nnkSym`, via `getImpl`) or
  ## an inline lambda literal (`nnkLambda`, same child layout as
  ## `nnkProcDef` — see `liftPropIfNeeded`). Read BEFORE lifting: a freshly
  ## `genSym`'d lifted name has no resolvable `getImpl` within this same
  ## macro expansion.
  if propExpr.kind == nnkSym: propExpr.getImpl.params
  else: propExpr.params

proc liftPropIfNeeded(propExpr: NimNode): tuple[def: NimNode, sym: NimNode] =
  ## RFC-fuzzer-nextgen E1 (C4/C7 pre-req): if `propExpr` already names a
  ## proc (`nnkSym` — the user wrote `fuzz(s, myProp, ...)`), it is ALREADY a
  ## named module-scope typed proc symbol — nothing to do. Otherwise
  ## (`nnkLambda` — an inline `proc(x: T) = ...` literal) lift it into a
  ## brand-new top-level `proc` definition (same params/body/pragmas, just a
  ## fresh name) so the property is a named, module-scope, referenceable
  ## typed proc symbol EITHER way — the shape Track G's walker will need
  ## later (`getImpl` on a symbol; a closure *value* is not enough).
  if propExpr.kind == nnkSym:
    (newEmptyNode(), propExpr)
  else:
    let liftedName = genSym(nskProc, "nelliFuzzProp")
    var children = newSeq[NimNode]()
    for c in propExpr: children.add c
    children[0] = liftedName
    (newTree(nnkProcDef, children), liftedName)

proc fuzzMacroImpl(stratExpr, propExpr, settingsExpr: NimNode): NimNode =
  validateCapture(stratExpr, "strategy expression")
  validateCapture(propExpr, "property expression")

  let idStr = fuzzCallSiteId(stratExpr)
  let idLit = newLit(idStr)
  let paramCount = countFormalParams(propFormalParams(propExpr))
  let paramCountLit = newLit(paramCount)
  let (liftedDef, propSym) = liftPropIfNeeded(propExpr)
  let stratCopyForEntry = copyNimTree(stratExpr)
  let stratCopyForCall = copyNimTree(stratExpr)

  var stmts = newStmtList()
  if liftedDef.kind != nnkEmpty:
    stmts.add liftedDef

  # The worker-mode reconstruction entry (C5): a closure that, EACH TIME it
  # runs, re-evaluates a fresh copy of `stratExpr` — a genuine rebuild, not a
  # captured reference to the parent call site's own strategy object — then
  # drives one input through a freshly-built in-process `Worker`.
  stmts.add quote do:
    nelliRegisterWorkerEntry(`idLit`, proc (input: ChoiceSeq): Observation[void] {.closure.} =
      var nelliRebuiltStrategy = `stratCopyForEntry`
      let nelliRebuiltWorker = newInProcessWorker(nelliRebuiltStrategy, inProcessTarget(`propSym`))
      let nelliObs = nelliRebuiltWorker.submit(input)
      Observation[void](verdict: nelliObs.verdict, coverage: nelliObs.coverage,
                         message: nelliObs.message, crash: nelliObs.crash,
                         runResult: nelliObs.runResult))

  # RFC-fuzzer-nextgen E2a: worker-mode dispatch. `nelliWorkerModeId`
  # (fuzzworker.nim) is parsed from argv at module load, BEFORE this call
  # site's own code (including the registration statement just above) runs
  # — so by the time control reaches here, both "was this process launched
  # in worker mode" and "is THIS the call site it names" are already
  # decidable. A match means the ordinary `fuzz(...)` site "double-serves"
  # (RFC §Open items): instead of the front door, it enters the worker loop
  # over the pipes the orchestrator's `spawnWorkerProcess` wired to fds 3/4.
  # `runWorkerLoopAndExit` is `{.noreturn.}` (it always `quit`s), so the
  # front-door block below is simply never reached on that path — no
  # if/else expression-type unification needed. Non-POSIX builds never see
  # this check at all (`when defined(posix)`, resolved in the CALLER's
  # module against the CALLER's active defines): the slice is POSIX-only.
  stmts.add quote do:
    when defined(posix):
      if nelliWorkerModeId == `idLit`:
        runWorkerLoopAndExit(`idLit`, proc (input: ChoiceSeq): Observation[void] {.closure.} =
          runWorkerReentry(`idLit`, input))

  # RFC-fuzzer-nextgen G3 C4 / G6: the real concolic bridge. Closes over
  # `propSym` — the SAME walkable typed proc symbol Track G's walker
  # consumes (per the module doc comment) — so it can run `concolicFlip` for
  # real, in-process, on demand. `ConcolicBridgeEntry`'s contract is exactly
  # `(trace, targetBranchIndex) -> ConcolicBridgeResult`; no cross-process
  # registry is needed (unlike the worker-mode entry above) because the
  # bridge only ever runs inside the SAME orchestrator process that already
  # holds this closure. `bindings` is G6's transparency-descriptor
  # classifier (see the section above) for a single-parameter property —
  # `stratExpr`'s combinator chain is classified ONCE, at macro-expansion
  # time, into a `TransparencyDescriptor` flattened directly into the
  # generated binding; a multi-parameter property keeps the pre-G6 minimal
  # positional `cbDrawLinked` classifier (documented scope cut — see the
  # section doc). The real `ConcolicFlipOutcome`/`ConcolicCoverageOutcome`
  # taxonomy is translated into fuzz.nim's type-erased
  # `ConcolicOutcomeTag`/`ConcolicCoverageTag` so the Orchestrator (which
  # stays Z3-free) never sees a symex type.
  # The behavior-preserving front (C4): identical wiring to what
  # `tfuzzloop`/`tfuzzcovcorpus` write by hand today — a fresh
  # `CoverageFrontier` plus `fuzz(s, inProcessTarget(prop), frontier,
  # settings, concolicBridge)`. G3 C4 adds the real bridge (built in the SAME
  # `quote do` block as its only use, below — cross-block local-variable
  # references don't resolve here); every pre-C4 caller stays byte-identical
  # because the bridge stays INERT unless the caller also opts into
  # `settings.stallRounds > 0` (`tryConcolicBridge`'s own gate, fuzz.nim).
  # This is the macro's VALUE (last expression in the stmt list).
  #
  # NOTE: the paramCount==1 / else branch below is decided at MACRO-
  # EXPANSION time (a plain Nim `if`, not `when`) and each arm is its own
  # SELF-CONTAINED `quote do` block — deliberately not a shared block with a
  # spliced multi-statement fragment for the bindings setup. Substituting a
  # multi-statement `NimNode` (built by a separate `quote do`) into the
  # MIDDLE of another `quote do` block nests it as a child `nnkStmtList`,
  # which opens its OWN scope — a `let`/`var` declared inside it is then
  # invisible to sibling statements later in the outer block (Nim macro-
  # hygiene footgun, caught empirically: `concolicFlip`'s `nelliBindings`
  # argument came back "undeclared identifier" until this was split). Only
  # EXPRESSION-level substitutions (`bindingNode`, `paramCountLit`, …) are
  # safe across a `quote do` boundary, matching every other backtick use in
  # this file.
  if paramCount == 1:
    let bindingNode = bindingExprFor(classifyStrategyExpr(stratExpr), newLit(0))
    stmts.add quote do:
      block:
        let nelliConcolicBridge = proc (nelliTrace: seq[ChoiceNode];
                                        nelliTargetBranchIndex: int): ConcolicBridgeResult {.closure.} =
          let nelliBindings = @[`bindingNode`]
          let nelliFlip = concolicFlip(`propSym`, nelliTrace, nelliBindings, nelliTargetBranchIndex)
          let nelliOutcome =
            case nelliFlip.outcome
            of cfoSolvedExact, cfoSolvedOptimistic: coSolved
            of cfoUnsat: coUnsat
            of cfoTimedOut: coTimedOut
            of cfoUnmodelable: coUnmodelable
          let nelliCoverage =
            case nelliFlip.coverage
            of ccoIntendedCovered: ccIntendedCovered
            of ccoUnrelatedCoverage: ccUnrelatedCoverage
            of ccoNotApplicable: ccNotApplicable
          # RFC-fuzzer-nextgen S5b: translate G2's real yield taxonomy
          # (`ConcolicFlipCounters`/`ConcolicYieldCounters`, smt/runtime.nim)
          # into fuzz.nim's Z3-free erased `ConcolicYieldTotals` — same
          # erasure-boundary convention as `nelliOutcome`/`nelliCoverage`
          # above, just carrying the full breakdown instead of collapsing it.
          let nelliYield = ConcolicYieldTotals(
            solvedExact: nelliFlip.flipCounters.byOutcome[cfoSolvedExact],
            solvedOptimistic: nelliFlip.flipCounters.byOutcome[cfoSolvedOptimistic],
            unsat: nelliFlip.flipCounters.byOutcome[cfoUnsat],
            unmodelable: nelliFlip.flipCounters.byOutcome[cfoUnmodelable],
            timedOut: nelliFlip.flipCounters.byOutcome[cfoTimedOut],
            intendedCovered: nelliFlip.flipCounters.byCoverage[ccoIntendedCovered],
            unrelatedCoverage: nelliFlip.flipCounters.byCoverage[ccoUnrelatedCoverage],
            notApplicable: nelliFlip.flipCounters.byCoverage[ccoNotApplicable],
            relaxationAttemptsUsed: nelliFlip.flipCounters.relaxationAttemptsUsed,
            tracesTruncated: nelliFlip.collectCounters.tracesTruncated,
            drawsSymbolicated: nelliFlip.collectCounters.drawsSymbolicated,
            paramsConcretized: nelliFlip.collectCounters.paramsConcretized,
            unsupportedDrawKinds: nelliFlip.collectCounters.unsupportedDrawKinds,
            ambiguousBranches: nelliFlip.collectCounters.ambiguousBranches)
          ConcolicBridgeResult(materialized: nelliFlip.materialized,
                               outcome: nelliOutcome, coverage: nelliCoverage,
                               yieldTotals: nelliYield)
        var nelliFuzzFrontier = newCoverageFrontier()
        fuzz(`stratCopyForCall`, inProcessTarget(`propSym`), nelliFuzzFrontier, `settingsExpr`,
            concolicBridge = nelliConcolicBridge)
  else:
    stmts.add quote do:
      block:
        let nelliConcolicBridge = proc (nelliTrace: seq[ChoiceNode];
                                        nelliTargetBranchIndex: int): ConcolicBridgeResult {.closure.} =
          var nelliBindings: seq[ConcolicParamBinding]
          for nelliParamIx in 0 ..< `paramCountLit`:
            nelliBindings.add ConcolicParamBinding(kind: cbDrawLinked, drawIndex: nelliParamIx)
          let nelliFlip = concolicFlip(`propSym`, nelliTrace, nelliBindings, nelliTargetBranchIndex)
          let nelliOutcome =
            case nelliFlip.outcome
            of cfoSolvedExact, cfoSolvedOptimistic: coSolved
            of cfoUnsat: coUnsat
            of cfoTimedOut: coTimedOut
            of cfoUnmodelable: coUnmodelable
          let nelliCoverage =
            case nelliFlip.coverage
            of ccoIntendedCovered: ccIntendedCovered
            of ccoUnrelatedCoverage: ccUnrelatedCoverage
            of ccoNotApplicable: ccNotApplicable
          # RFC-fuzzer-nextgen S5b: translate G2's real yield taxonomy
          # (`ConcolicFlipCounters`/`ConcolicYieldCounters`, smt/runtime.nim)
          # into fuzz.nim's Z3-free erased `ConcolicYieldTotals` — same
          # erasure-boundary convention as `nelliOutcome`/`nelliCoverage`
          # above, just carrying the full breakdown instead of collapsing it.
          let nelliYield = ConcolicYieldTotals(
            solvedExact: nelliFlip.flipCounters.byOutcome[cfoSolvedExact],
            solvedOptimistic: nelliFlip.flipCounters.byOutcome[cfoSolvedOptimistic],
            unsat: nelliFlip.flipCounters.byOutcome[cfoUnsat],
            unmodelable: nelliFlip.flipCounters.byOutcome[cfoUnmodelable],
            timedOut: nelliFlip.flipCounters.byOutcome[cfoTimedOut],
            intendedCovered: nelliFlip.flipCounters.byCoverage[ccoIntendedCovered],
            unrelatedCoverage: nelliFlip.flipCounters.byCoverage[ccoUnrelatedCoverage],
            notApplicable: nelliFlip.flipCounters.byCoverage[ccoNotApplicable],
            relaxationAttemptsUsed: nelliFlip.flipCounters.relaxationAttemptsUsed,
            tracesTruncated: nelliFlip.collectCounters.tracesTruncated,
            drawsSymbolicated: nelliFlip.collectCounters.drawsSymbolicated,
            paramsConcretized: nelliFlip.collectCounters.paramsConcretized,
            unsupportedDrawKinds: nelliFlip.collectCounters.unsupportedDrawKinds,
            ambiguousBranches: nelliFlip.collectCounters.ambiguousBranches)
          ConcolicBridgeResult(materialized: nelliFlip.materialized,
                               outcome: nelliOutcome, coverage: nelliCoverage,
                               yieldTotals: nelliYield)
        var nelliFuzzFrontier = newCoverageFrontier()
        fuzz(`stratCopyForCall`, inProcessTarget(`propSym`), nelliFuzzFrontier, `settingsExpr`,
            concolicBridge = nelliConcolicBridge)

  result = stmts

macro fuzz*(stratExpr, propExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>)` — settings default to `FuzzSettings()`.
  ## See the module doc comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, newCall(ident"FuzzSettings"))

macro fuzz*(stratExpr, propExpr, settingsExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>, <settings>)`. See the module doc
  ## comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, settingsExpr)
