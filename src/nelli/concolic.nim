## nelli/concolic — the opt-in concolic-assist door.
##
## RFC-z3-optional. `import nelli` is Z3-free; concolic fuzzing needs the
## symbolic-execution walker, so it lives behind this extra import. That is
## the whole seam: **this module is the only place in the fuzz stack that
## imports `./symex`** (and therefore `z3`), and the only producer of a
## non-nil `ConcolicAssist.bridge`.
##
## Why a macro and not a proc: the walker's ONLY ingestion door is a typed
## proc SYMBOL (`fn: typed` -> `getImpl` -> `parseProc` -> `walk`,
## `symex.nim:461`/`:1627`), and `concolicFlip` is itself a macro that
## splices a `SymexProgram` IR literal into its caller. A runtime proc value
## carries none of that. So the assist is built at the CALL SITE, at
## compile time, from the captured strategy/property expressions — exactly
## the contract `fuzz(...)` (fuzzmacro.nim) already uses for worker
## re-entry, moved to the module the caller opts into.
##
## **Import direction, stated so it is not rediscovered:** `concolic ->
## fuzzmacro` (for the shared `propFormalParams`/`countFormalParams`/
## `liftPropIfNeeded` capture helpers) is the ONLY edge that ever exists.
## The reverse — `fuzzmacro -> concolic` — must never be added: with the
## shared-helper edge in place it is an immediate circular import, confirmed
## empirically in this tree (RFC §S1a, round 3). Core does not call into
## this module; callers do.
##
## **`export symex` is hygiene-forced, not an API choice.** `concolicAssist`
## splices generated code into the CALLER's module, and that code carries
## free identifiers — IR constructors, `IRExprKind` values like `iekStrLen`,
## `ConcolicParamBinding`, `concolicFlip` itself — which resolve against the
## caller's scope, not this one. Without the re-export every caller would
## also have to `import nelli/symex` by hand. A future "narrow the
## re-export" cleanup would break every caller at a distance.
import std/[macros, options]
import ./symex
export symex
import ./fuzz
import ./fuzzmacro
import ./smt/transparency

# --- G6: transparency-descriptor AST classification -------------------------
#
# RFC-z3-optional S1a: COPIED verbatim from `fuzzmacro.nim` (the G6 cluster
# plus both bridge-emission arms). The copy is deliberate and temporary in
# exactly one direction: core still auto-wires a bridge from its own
# originals until S1b1 deletes them in the same slice that removes the
# auto-wiring. Deleting them here-and-now instead would force the forbidden
# `fuzzmacro -> concolic` edge (see the module doc).
#
# The section doc below is the original's, unchanged — it documents the
# classifier's recognized shapes and its deliberate scope cuts.
#
#
# RFC-fuzzer-nextgen G6. The G1b/G3 classifier (`fuzzmacro`'s
# `countFormalParams` doc) was positional-only: every property parameter got `cbDrawLinked`
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
  ## tree at all, macro-side only). `identity`
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


# --- the assist builder ------------------------------------------------------

proc concolicAssistImpl(strat, prop, stallRoundsExpr, maxBranchAttemptsExpr: NimNode): NimNode =
  ## RFC-z3-optional: build a `ConcolicAssist` — a real, Z3-backed
  ## `ConcolicBridgeEntry` plus the activation policy that makes it fire —
  ## from the captured strategy/property expressions.
  ##
  ## The emitted closure is the same one `fuzzmacro` emits today (S1a is a
  ## copy), with one deliberate difference: it is a VALUE the caller holds,
  ## not something core wires behind their back.
  ##
  ## `paramCount` dispatch, both arms, exactly as `fuzzMacroImpl` does it:
  ## a single-parameter property gets G6's classified transparency binding
  ## (the strategy's combinator chain flattened at compile time); a
  ## multi-parameter property keeps the pre-G6 minimal positional
  ## `cbDrawLinked` list. Reproducing BOTH arms is required — dropping the
  ## multi-param arm would silently narrow the assist to unary properties.
  ##
  ## Each arm is its own self-contained `quote do` block for the same
  ## macro-hygiene reason `fuzzmacro` documents: splicing a multi-statement
  ## `NimNode` into the middle of another `quote do` nests it as a child
  ## `nnkStmtList`, which opens its own scope and hides the `let`s from
  ## sibling statements.
  let paramCount = countFormalParams(propFormalParams(prop))
  let paramCountLit = newLit(paramCount)
  let (liftedDef, propSym) = liftPropIfNeeded(prop)

  var stmts = newStmtList()
  # RFC §The coherence invariant: `concolicAssist` performs its OWN lift of
  # an inline-lambda property, so the walker walks a distinct-but-identical
  # symbol from the one `fuzz` lifts. Sound (same AST), and compile-time
  # only — the generated closure evaluates neither `strat` nor `prop`.
  if liftedDef.kind != nnkEmpty:
    stmts.add liftedDef

  if paramCount == 1:
    let bindingNode = bindingExprFor(classifyStrategyExpr(strat), newLit(0))
    stmts.add quote do:
      block:
        let nelliConcolicBridge = proc (nelliTrace: seq[ChoiceNode];
                                        nelliTargetBranchIndex: int): ConcolicBridgeResult {.closure.} =
          let nelliBindings = @[`bindingNode`]
          let nelliFlip = concolicFlip(`propSym`, nelliTrace, nelliBindings, nelliTargetBranchIndex)
          ConcolicBridgeResult(flip: nelliFlip, construct: wckIf)
        ConcolicAssist(bridge: nelliConcolicBridge,
                       stallRounds: `stallRoundsExpr`,
                       maxBranchAttempts: `maxBranchAttemptsExpr`)
  else:
    stmts.add quote do:
      block:
        let nelliConcolicBridge = proc (nelliTrace: seq[ChoiceNode];
                                        nelliTargetBranchIndex: int): ConcolicBridgeResult {.closure.} =
          var nelliBindings: seq[ConcolicParamBinding]
          for nelliParamIx in 0 ..< `paramCountLit`:
            nelliBindings.add ConcolicParamBinding(kind: cbDrawLinked, drawIndex: nelliParamIx)
          let nelliFlip = concolicFlip(`propSym`, nelliTrace, nelliBindings, nelliTargetBranchIndex)
          ConcolicBridgeResult(flip: nelliFlip, construct: wckIf)
        ConcolicAssist(bridge: nelliConcolicBridge,
                       stallRounds: `stallRoundsExpr`,
                       maxBranchAttempts: `maxBranchAttemptsExpr`)

  result = stmts

macro concolicAssist*(strat, prop: typed;
                      stallRounds: untyped = 1;
                      maxBranchAttempts: untyped = 8): ConcolicAssist =
  ## Build the concolic assist for one `(strategy, property)` pair.
  ##
  ##     import nelli
  ##     import nelli/concolic
  ##
  ##     let assist = concolicAssist(integers(0, 0xFFFFFFFF), magicGate)
  ##
  ## **Argument order is `(strat, prop)`, matching `fuzz`.** A transposition
  ## across the two spellings is the coherence bug (the assist classifies
  ## bindings from one strategy chain while the campaign draws from
  ## another) with a worse error message.
  ##
  ## `strat`/`prop` are independent `typed` macro parameters, so they carry
  ## the same overloaded-proc / generic-proc resolution constraints
  ## `fuzz(...)`'s own arguments carry today: a bare overloaded name with no
  ## disambiguating context can fail to resolve.
  ##
  ## `stallRounds` defaults to `1`, not `0`: an assist you went out of your
  ## way to build is an assist you want to fire. The defaults are the active
  ## values, by design.
  concolicAssistImpl(strat, prop, stallRounds, maxBranchAttempts)

template fuzzConcolic*(s, p: untyped; settings: untyped = FuzzSettings();
                       stallRounds: untyped = 1;
                       maxBranchAttempts: untyped = 8): FuzzReport =
  ## **The default form for concolic-assisted fuzzing.**
  ##
  ##     import nelli
  ##     import nelli/concolic
  ##
  ##     let report = fuzzConcolic(integers(0, 0xFFFFFFFF), magicGate,
  ##                               FuzzSettings(seed: 42'u64, maxIterations: 60))
  ##
  ## Identical to `fuzz(s, p, settings, assist = concolicAssist(s, p, ...))`,
  ## and that is the point: `s` and `p` are named ONCE and generated TWICE,
  ## so the strategy the campaign draws from and the strategy the assist
  ## classifies bindings for cannot diverge. That is not a style preference
  ## — it is what makes the common path correct by construction (RFC
  ## §The coherence invariant).
  ##
  ## It also stops a real strategy expression from being written twice at
  ## one call site: `integers(0, 1000).map(proc(x: int): int = x * 2 + 1)`
  ## is a mouthful once.
  ##
  ## The double substitution is compile-time only. `concolicAssist` consumes
  ## `s` and `p` during classification and parse; the closure it generates
  ## evaluates neither, so there is no runtime double evaluation. An inline
  ## lambda `p` is lifted twice — once by `fuzz`, once by `concolicAssist`
  ## — which is sound (same AST, distinct-but-identical symbols) and worth
  ## knowing when reading expanded code.
  ##
  ## Defaults are the ACTIVE values: `stallRounds = 1`. Calling this and
  ## getting an inert campaign is not a state this API spells.
  fuzz(s, p, settings, assist = concolicAssist(s, p, stallRounds, maxBranchAttempts))
