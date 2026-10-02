## RFC-0005 S8ah -- the compile-time VM let-aliasing guard, promoted from
## `tests/tsymex_rfc0005_s8ab_letaudit.nim`'s own private copy (S8ab/S8af)
## into a REUSABLE library module, so the exact same mechanism can run both
## as a test (`check`, unconditional, every `dt-bounded.sh`/`nimble test`
## run) and as an OPT-IN build-time gate (`doAssert`, gated by
## `-d:nelliVmAliasAudit`) wired into the real symex compile path -- see
## `symex.nim`'s and `concolic.nim`'s own trailing `when defined` blocks,
## which both `import` this module rather than duplicating it.
##
## **What the walker does** and **why it is split this way** are documented
## in full at the top of `tests/tsymex_rfc0005_s8ab_letaudit.nim` (S8x's VM
## probe, S8ab's type-aware shapes, S8af's four closed gaps) -- that header
## is not repeated here. This module's own doc covers only what changed to
## make it a shared library (S8ah):
##
## 1. **Field-graph depth.** `collectFieldTypes` was bounded to 3 levels
##    (S8ab's own choice, unchanged by S8af). S8ah replaces the depth bound
##    with a full walk guarded by a `sameType`-keyed VISITED LIST (not a
##    depth counter) -- the depth bound's only real job was preventing an
##    infinite loop on a self-referential `ref` type (`type Node = ref
##    object; next: Node`); a visited set does that job exactly, without
##    capping the search at an arbitrary 3.
## 2. **Macro-by-macro generic reachability** (`genericRoutineSpecs`,
##    `vmGuardWalkForGenericCalls`, `vmGuardAuditMacroReach`). S8af forced
##    ONE instantiation (`traceOneCallBoundary[seq[NimNode]]`) based on a
##    MANUAL trace of which of the scope's 37 generic-bracketed routines
##    are called directly (unquoted) from a macro's own compile-time-VM-
##    executed code, versus only emitted inside `quote do:` (which lowers
##    to `getAst`/tree-construction calls, never a live call to the
##    target -- probed empirically, see the RFC note). S8ah makes that
##    trace MECHANICAL: walk every macro's typed `getImpl()` tree,
##    TRANSITIVELY through the call graph, for a live `nnkCall`/
##    `nnkCommand` whose resolved callee IS one of the 37, for every macro
##    in the 16-file scope, not just the ones S8af happened to trace by
##    hand. The transitive hop is a REAL finding, not a hypothetical: the
##    one generic S8af forced by hand, `traceOneCallBoundary`, is never
##    called directly from any macro at all -- it is called from
##    `collectStringBackedByteSeqParamsImpl`, an ordinary proc, which is
##    what the macro actually calls. A one-level-only walk (the first
##    version of this mechanism) missed it entirely; the walk now follows
##    proc/func/method/converter/iterator callees recursively, guarded by
##    a `file:name@line`-keyed visited set against recursion/call cycles
##    (same shape as the field-graph fix in item 1 above).
## 3. **Forced-instantiation completeness.** Whichever generics the
##    mechanical walk above finds VM-reachable MUST each have a forced
##    `vmGuardAuditInstantiation` call auditing a real instantiation (the
##    `auditGenericInstantiation` mechanism S8af built) -- a generic found
##    reachable with no forced audit is a gap, not a pass. The completeness
##    check lives with each self-audit's allowlist (see `symex.nim`).
##
## **S8ak -- S8ah's own remainder, closed here:**
## 4. **Zero-required-argument macros, resolved by symbol.** S8ah's walk
##    (item 2 above) needed a NAME resolved to a `typed` macro symbol before
##    `getImpl()` could run on it; the old path did that by generating
##    `vmGuardAuditRoutine(ident(nm), fileTag)` and letting the COMPILER
##    re-resolve `ident(nm)` as a fresh `typed` ARGUMENT EXPRESSION. Nim
##    auto-invokes a macro with no required parameters when it is referenced
##    bare in that position (probed, confirmed: the macro's own RESULT, an
##    `nnkIntLit`, arrives in place of its symbol -- macros have no
##    first-class "value" form the way an ordinary proc does, so a bare
##    reference has no OTHER valid reading) -- a silent false negative, the
##    exact shape S8ah's own remainder note left open. `vmGuardAuditNames`
##    now resolves each name via `bindSym(nm, brForceOpen)` instead: pure
##    NAME RESOLUTION (an API-level symbol lookup), never an expression
##    evaluation, so the macro is never invoked -- `.getImpl()` reads
##    straight off the resolved symbol. See that macro's own doc for the
##    probed before/after node kinds.
## 5. **`extractTopLevelNames`/`extractTopLevelMacroNames`, re-based on a
##    real parse.** The column-0 line-text scan is replaced with
##    `parseStmt(staticRead(path))` -- a genuine (if untyped) parse of the
##    module's own source -- read for each top-level routine DEFINITION
##    NODE's own name, instead of pattern-matching source TEXT line by
##    line. This needs no special-casing for a backtick-quoted name
##    (`nnkAccQuoted`, unwrapped the same way whether its `nnkPostfix`
##    export-marker wrapper is present or not) or for a routine whose
##    keyword and name sit on different physical lines (invisible to the
##    old scan's `line.startsWith("proc ")`-style check, since the keyword's
##    OWN line never contains the name at all) -- a real parser has no line
##    boundaries to be confused by in the first place. See
##    `tests/s8ak_scan_fixture.nim` for both fixtured shapes.
## 6. **A reachable generic's hit key is derived from the live callee, never
##    `genericRoutineSpecs`' own hand-typed `line` field.** Found by a
##    Windows-only build-time-gate failure (the Linux sweep never compiles
##    with `-d:nelliVmAliasAudit` on): S8ad edited `dsl_parser.nim` above
##    `traceOneCallBoundary`, shifting it from line 7269 to 7270;
##    `genericRoutineSpecs` still said 7269, so the reachable-generic hit
##    key (`vmGuardWalkForGenericCallsAux`, built from `spec.line`) and
##    `vmGuardAuditInstantiation`'s forced-instantiation key (always built
##    from the LIVE `getImpl().lineInfoObj.line`) silently stopped matching
##    -- `traceOneCallBoundary` is both reachable AND already forced, but
##    `symex.nim`'s and this module's own self-audits both reported it
##    "unforced" and failed their `doAssert`. `calleeMatchesGeneric` (the
##    ELIGIBILITY check) only ever compared `spec.name`/`spec.file` --
##    `spec.line` was dead for MATCHING already, only ever used to build
##    the hit string -- so building that string from the matched callee's
##    own `getImpl()` instead fixes this with no change to eligibility, and
##    makes the key immune to any future edit anywhere in the file, not
##    just the one S8ad happened to make. `genericRoutineSpecs`' `line`
##    field itself is unchanged (still needed to tell `logCmp`'s and
##    `map`'s two same-file, same-name overloads apart during review; see
##    its own doc) -- only the derived KEY stopped trusting it.
##
## **S8al -- S8ak's own remainder, closed here:**
## 7. **`vmGuardAuditMacroReachWithSpecs` (the test-only reachability hook),
##    resolved by symbol.** Took the macro SYMBOL directly as a `typed`
##    argument, the exact auto-invoke trap item 4 above already fixed for
##    `vmGuardAuditNames` -- a genuinely zero-required-argument macro
##    referenced bare there is auto-invoked by Nim, not resolved to its own
##    symbol. This test hook needed the same fix (same `bindSym`-via-
##    nested-macro technique, see `vmGuardAuditOneSymReachOnly`), which also
##    let the two existing reachability fixtures
##    (`s8ahFxDirectGenericCall`/`s8ahFxQuotedGenericCall`) drop the dummy
##    required parameter they carried purely to dodge the trap.
## 8. **The force-and-audit half exercised against a fixture generic, not
##    only `traceOneCallBoundary`.** The "found reachable -> must have a
##    forced-instantiation audit or the completeness check fails closed"
##    comparison (`vmGuardForcedGenerics`'s own doc, and each self-audit's
##    `doAssert unforced.len == 0`) had, in the real scope, only ever had
##    ONE row to evaluate -- always forced, so the comparison's FAILING
##    branch had never actually been exercised. The test file's own new
##    `s8alFxUnforcedHazardGeneric` fixture (reachable, deliberately never
##    forced) proves the comparison correctly reports it unforced rather
##    than silently passing; `s8alFxForcedHazardGeneric` (reachable, forced)
##    proves the hazard itself is still reported once real.
##
## No walker bump: this is compile-time reflection over already-compiled
## modules, same as S8ab/S8af/S8ah/S8ak -- it never touches the SMT IR.

import std/[macros, os, strutils, tables]

# RFC-0005 S8ak: `vmGuardAuditNames` resolves each discovered name via
# `bindSym(nm, brForceOpen)` where `nm` is a runtime-computed `seq[string]`
# element, not a literal identifier/string token written where the macro
# itself is defined -- ordinary `bindSym` requires the latter. See
# `vmGuardAuditNames`'s own doc for why this replaces the old
# `ident(nm)`-via-`typed`-argument path.
{.experimental: "dynamicBindSym".}

# ---- shared hazard-shape primitives (S8ab/S8af, moved verbatim) -------------

const objKinds* = {ntyObject, ntyTuple, ntySequence, ntyString, ntySet, ntyArray}
  ## RFC-0005 S8x's VM probe: every non-scalar VALUE location the VM
  ## aliases through a `let`. `ref` (`ntyRef`) is excluded on purpose --
  ## "shared by design", the VM's own safe case.

const routineSymKinds* = {nskProc, nskFunc, nskMethod, nskIterator,
                           nskConverter, nskTemplate, nskMacro}

proc unwrapHidden*(n: NimNode): NimNode =
  ## Strips the implicit conversions/derefs the typed tree inserts around
  ## an expression (`nnkHiddenStdConv` and friends) so shape/root checks
  ## see the real expression underneath.
  result = n
  while result.kind in {nnkHiddenDeref, nnkHiddenAddr, nnkHiddenStdConv,
                         nnkHiddenSubConv, nnkHiddenCallConv, nnkConv,
                         nnkExprColonExpr}:
    if result.len == 0: break
    result = result[^1]

proc calleeReturnsVar*(callNode: NimNode): bool =
  ## RFC-0005 S8af (closes S8ab's "`[]`-via-`nnkCall`" gap). True iff
  ## `callNode` (an already-`unwrapHidden`-ed `nnkCall`) resolves to a
  ## routine whose DECLARED return type is `var T` -- see the test file's
  ## header for the full probe-backed rationale.
  if callNode.kind != nnkCall or callNode.len == 0: return false
  let callee = callNode[0]
  if callee.kind != nnkSym or callee.symKind notin routineSymKinds: return false
  var impl: NimNode
  try: impl = callee.getImpl()
  except CatchableError: return false
  if impl.isNil or impl.kind == nnkNilLit or impl.len <= 3: return false
  let formals = impl[3]
  if formals.kind != nnkFormalParams or formals.len == 0: return false
  formals[0].kind == nnkVarTy

proc rootSym*(n: NimNode): NimNode =
  ## The base symbol of a `.field`/`[i]`/aliasing-call chain.
  result = unwrapHidden(n)
  while true:
    case result.kind
    of nnkBracketExpr, nnkDotExpr:
      if result.len == 0: return
      result = unwrapHidden(result[0])
    of nnkCall:
      if calleeReturnsVar(result) and result.len > 1:
        result = unwrapHidden(result[1])
      else:
        return
    else:
      return

proc rhsAliasKind*(n: NimNode): NimNode =
  ## nil: not one of the hazard shapes. Otherwise the (unwrapped) RHS node
  ## to classify by type.
  let r = unwrapHidden(n)
  if r.kind in {nnkBracketExpr, nnkDotExpr, nnkSym}: return r
  if r.kind == nnkCall and calleeReturnsVar(r): return r
  nil

proc walkLets*(n: NimNode; owner: string; hits: var seq[string]) =
  if n == nil: return
  if n.kind == nnkLetSection:
    var localNames: seq[string]
    for iddef in n:
      if iddef.kind notin {nnkIdentDefs, nnkVarTuple}: continue
      for k in 0 ..< iddef.len - 2:
        if iddef[k].kind == nnkSym: localNames.add macros.strVal(iddef[k])
    for iddef in n:
      if iddef.kind notin {nnkIdentDefs, nnkVarTuple}: continue
      let rhs = rhsAliasKind(iddef[^1])
      if rhs.isNil: continue
      let root = rootSym(rhs)
      if root.kind == nnkSym and macros.strVal(root) in localNames: continue
      for k in 0 ..< iddef.len - 2:
        let nameNode = iddef[k]
        if nameNode.kind != nnkSym: continue
        let t = nameNode.getTypeInst()
        if t.isNil: continue
        if t.typeKind notin objKinds: continue
        hits.add owner & ": let " & macros.strVal(nameNode) & " : " & t.repr &
          " (" & $t.typeKind & ") <- " & rhs.repr
  for c in n:
    walkLets(c, owner, hits)

const mutMethods* = ["add", "setLen", "del", "delete", "insert", "incl",
  "excl", "pop", "clear", "sort", "reverse", "shrink", "fill", "inc", "dec",
  "mgetOrPut", "containsOrIncl", "missingOrExcl", "swap", "apply", "keepIf",
  "keepItIf", "applyIt", "mitems", "mpairs", "addQuoted", "removePrefix",
  "removeSuffix"]
  ## S8x's `scan.py` MUT_METH vocabulary, reused at the typed level.

proc calleeName(n: NimNode): string =
  ## RFC-0005 S8bh. The routine name a callee node spells, or "" when it
  ## spells none: an identifier or symbol, the first candidate of an
  ## overload choice (every candidate has the one name), the name inside
  ## backquotes or under a generic instantiation (`f[T]`). `strVal` on any
  ## other kind is a compile error, which every typed body holding such a
  ## callee (`x.f[T](...)`) used to trip.
  case n.kind
  of nnkIdent, nnkSym: macros.strVal(n)
  of nnkOpenSymChoice, nnkClosedSymChoice, nnkAccQuoted, nnkBracketExpr:
    if n.len > 0: calleeName(n[0]) else: ""
  of nnkPostfix:
    if n.len > 1: calleeName(n[1]) else: ""
  else: ""

proc bodyMutatesRoot*(n: NimNode; target: NimNode): bool =
  if n == nil: return false
  case n.kind
  of nnkAsgn:
    let lhs = unwrapHidden(n[0])
    if lhs.kind in {nnkBracketExpr, nnkDotExpr} and rootSym(lhs) == target:
      return true
  of nnkCall, nnkCommand:
    if n.len > 0:
      let callee = n[0]
      if callee.kind == nnkDotExpr and callee.len == 2 and
         calleeName(callee[1]) in mutMethods and rootSym(callee[0]) == target:
        return true
      if callee.kind == nnkSym and calleeName(callee) in mutMethods and
         n.len > 1 and rootSym(n[1]) == target:
        return true
  else: discard
  for c in n:
    if bodyMutatesRoot(c, target): return true
  false

proc typeAlreadyVisited*(visited: seq[NimNode]; t: NimNode): bool =
  ## RFC-0005 S8ah: `sameType` identity, not a repr/pointer compare -- the
  ## same standard S8af already applied to the sibling-field comparison
  ## itself (see `walkParams` below), now also applied to cycle detection.
  for v in visited:
    if sameType(v, t): return true
  false

proc collectFieldTypes*(objTypeSym: NimNode; visited: var seq[NimNode];
                         into: var seq[NimNode]) =
  ## RFC-0005 S8ah: full field-graph walk (was depth-3-bounded, S8ab/S8af).
  ## `visited` is keyed by `sameType` (via `typeAlreadyVisited`), not a
  ## depth counter -- the depth bound's only real job was stopping an
  ## infinite loop on a self-referential type (`type Node = ref object;
  ## next: Node`); a visited set does that job exactly, at any depth,
  ## rather than silently giving up at an arbitrary 3. See the RED fixture
  ## in `tests/tsymex_rfc0005_s8ab_letaudit.nim` (a hazard 5 fields deep)
  ## and the cyclic-termination fixture (a self-referential chain with a
  ## hazard past the cycle) for what this actually catches.
  if objTypeSym.kind != nnkSym: return
  if typeAlreadyVisited(visited, objTypeSym): return
  visited.add objTypeSym
  var cur: NimNode
  try: cur = objTypeSym.getTypeImpl()
  except CatchableError: return
  if cur.isNil: return
  if cur.kind in {nnkRefTy, nnkPtrTy} and cur.len > 0 and cur[0].kind == nnkSym:
    let inner = cur[0]
    if typeAlreadyVisited(visited, inner): return
    visited.add inner
    try: cur = inner.getTypeImpl()
    except CatchableError: return
  if cur.kind != nnkObjectTy or cur.len < 3: return
  let recList = cur[2]
  if recList.kind != nnkRecList: return
  for fld in recList:
    if fld.kind != nnkIdentDefs: continue
    let fieldNameSym = fld[0]
    if fieldNameSym.kind != nnkSym: continue
    var fieldType: NimNode
    try: fieldType = fieldNameSym.getTypeInst()
    except CatchableError: continue
    if fieldType.isNil: continue
    into.add fieldType
    if fieldType.kind == nnkSym:
      collectFieldTypes(fieldType, visited, into)

proc walkParams*(impl: NimNode; owner: string; hits: var seq[string]) =
  if impl.len <= 6: return
  let formals = impl[3]
  if formals.kind != nnkFormalParams: return
  let body = impl[6]
  var candidates: seq[tuple[nm: string, t: NimNode]]
  var siblingFieldTypes: seq[NimNode]
  for i in 1 ..< formals.len:
    let iddef = formals[i]
    if iddef.kind != nnkIdentDefs: continue
    if iddef[1].kind == nnkVarTy: continue  # `var T`: copies, safe
    let sym = iddef[0]
    if sym.kind != nnkSym: continue
    let t = sym.getTypeInst()
    if t.isNil: continue
    if t.typeKind == ntyRef:
      if bodyMutatesRoot(body, sym):
        var visited: seq[NimNode]
        collectFieldTypes(t, visited, siblingFieldTypes)
    elif t.typeKind in objKinds:
      candidates.add (macros.strVal(sym), t)
  if siblingFieldTypes.len == 0: return
  for (nm, t) in candidates:
    var matched = false
    for ft in siblingFieldTypes:
      if sameType(t, ft): matched = true; break
    if matched:
      hits.add owner & ": param " & nm & " : " & t.repr &
        " (" & $t.typeKind & ") -- a sibling ref param, mutated in this " &
        "body, reaches the same field type"

# ---- RFC-0005 S8ah: macro-by-macro reachability of the 37 generics ---------

type GenericRoutineSpec* = tuple[name: string, file: string, line: int]

const genericRoutineSpecs*: seq[GenericRoutineSpec] = @[
  ("traceOneCallBoundary", "dsl_parser.nim", 7269),
  ("checkUnsatOverTaintOnly", "types.nim", 3434),
  ("sortedKeysOf", "symex.nim", 55),
  ("sortedElemsOf", "symex.nim", 64),
  ("renderInto", "symex.nim", 69),
  ("renderAsChoices", "symex.nim", 172),
  ("forAllWithSymexSeeds", "symex.nim", 454),
  ("allRaiseFindings", "symex.nim", 2336),
  ("processIsolationSpawnWorker", "fuzzmacro.nim", 135),
  ("logCmp", "coverage.nim", 540),
  ("logCmp", "coverage.nim", 561),
  ("newStrategy", "strategy.nim", 97),
  ("displayWith", "strategy.nim", 102),
  ("generate", "strategy.nim", 111),
  ("valueType", "strategy.nim", 115),
  ("just", "strategy.nim", 130),
  ("sampledFrom", "strategy.nim", 134),
  ("sampledFromWhere", "strategy.nim", 143),
  ("oneOf", "strategy.nim", 160),
  ("frequency", "strategy.nim", 191),
  ("map", "strategy.nim", 236),
  ("mapWithDisplay", "strategy.nim", 246),
  ("filter", "strategy.nim", 254),
  ("recursive", "strategy.nim", 267),
  ("enums", "strategy.nim", 287),
  ("map", "strategy.nim", 303),
  ("flatMap", "strategy.nim", 390),
  ("flatMapWithDisplay", "strategy.nim", 402),
  ("lists", "strategy.nim", 451),
  ("tables", "strategy.nim", 534),
  ("sets", "strategy.nim", 562),
  ("bitsets", "strategy.nim", 586),
  ("arrays", "strategy.nim", 595),
  ("isLinearisable", "parallel.nim", 74),
  ("workerProc", "parallel.nim", 774),
  ("runPlan", "parallel.nim", 799),
  ("parallelCheck", "parallel.nim", 850),
]
  ## The 37 generic-bracketed top-level routines in the guard's 16-file
  ## scope (a column-0 `[` scan across `proc`/`func`/`macro`/`template`/
  ## `iterator`/`converter` -- exactly reproduces the count the RFC note
  ## already cited). `(name, file)` pairs repeat for `logCmp` (two
  ## constraint overloads, `coverage.nim`) and `map` (a proc AND a macro,
  ## both named `map`, `strategy.nim`) -- kept as separate entries (by
  ## line) rather than merged, since each is a DISTINCT routine body that
  ## could independently be VM-reachable or not.

proc calleeMatchesGeneric*(callee: NimNode; spec: GenericRoutineSpec): bool =
  if callee.kind != nnkSym or callee.symKind notin routineSymKinds: return false
  if macros.strVal(callee) != spec.name: return false
  var impl: NimNode
  try: impl = callee.getImpl()
  except CatchableError: return false
  if impl.isNil or impl.kind == nnkNilLit: return false
  impl.lineInfoObj.filename.endsWith(spec.file)

proc vmGuardWalkForGenericCallsAux(n: NimNode; macroTag: string;
                                    specs: seq[GenericRoutineSpec];
                                    visitedProcs: var seq[string];
                                    hits: var seq[string]) =
  if n == nil: return
  if n.kind in {nnkCall, nnkCommand} and n.len > 0:
    let callee = unwrapHidden(n[0])
    if callee.kind == nnkSym:
      var registered = false
      for spec in specs:
        if calleeMatchesGeneric(callee, spec): registered = true
      if registered:
        # RFC-0005 S8ak: the hit key is derived from the MATCHED CALLEE's
        # own live `getImpl()`, never from `spec.line` -- `calleeMatchesGeneric`
        # above only ever used `spec.name`/`spec.file` (never `spec.line`) to
        # decide eligibility, so `spec.line` was already dead for MATCHING;
        # it was still baked into this hit string, which is exactly what
        # broke S8ad's `dsl_parser.nim` edit: that edit shifted
        # `traceOneCallBoundary` from line 7269 to 7270, `genericRoutineSpecs`
        # still said 7269, and `vmGuardAuditInstantiation`'s own forced-key
        # (below) ALREADY derived its line live -- so the two keys silently
        # stopped matching and a real, already-forced generic was reported
        # "unforced" (`symex.nim`'s and `vm_alias_guard.nim`'s own
        # self-audits both `doAssert unforced.len == 0`). Deriving THIS key
        # live too means an edit anywhere else in the file -- above, below,
        # anywhere -- can never desync it from the forced-instantiation key,
        # which is the one invariant a registry keyed by "this routine's
        # declaration line, hand-copied into a const table" cannot give.
        var impl: NimNode
        try: impl = callee.getImpl()
        except CatchableError: impl = nil
        if impl != nil and impl.kind != nnkNilLit:
          hits.add macroTag & " -> " & extractFilename(impl.lineInfoObj.filename) &
                    ":" & macros.strVal(callee) & "@" & $impl.lineInfoObj.line
      # RFC-0005 S8ah (real-scope finding): a macro's OWN body frequently
      # calls the generic only through an intermediate PROC (e.g.
      # `dsl_parser.nim`'s `traceOneCallBoundary` is called from
      # `collectStringBackedByteSeqParamsImpl`, an ordinary proc, never
      # directly from a macro) -- that intermediate proc still executes
      # in the SAME compile-time VM once a macro calls it, so reachability
      # must follow the call graph TRANSITIVELY, not just one level. A
      # `file:name@line`-keyed visited set (not a depth bound, same
      # reasoning as the field-graph fix) guards against recursive/mutual
      # call cycles.
      if callee.symKind in {nskProc, nskFunc, nskMethod, nskConverter, nskIterator}:
        var calleeImpl: NimNode
        try: calleeImpl = callee.getImpl()
        except CatchableError: calleeImpl = nil
        if calleeImpl != nil and calleeImpl.kind != nnkNilLit:
          let key = calleeImpl.lineInfoObj.filename & ":" & macros.strVal(callee) &
                    "@" & $calleeImpl.lineInfoObj.line
          if key notin visitedProcs:
            visitedProcs.add key
            vmGuardWalkForGenericCallsAux(calleeImpl, macroTag, specs, visitedProcs, hits)
  for c in n:
    vmGuardWalkForGenericCallsAux(c, macroTag, specs, visitedProcs, hits)

proc vmGuardWalkForGenericCalls*(n: NimNode; macroTag: string;
                                  specs: seq[GenericRoutineSpec]; hits: var seq[string]) =
  ## RFC-0005 S8ah. Walks a macro's typed `getImpl()` tree, TRANSITIVELY
  ## through every proc/func/method/converter/iterator it calls, for a
  ## LIVE call (`nnkCall`/`nnkCommand`) whose resolved callee matches one
  ## of `specs`. This is the mechanical version of S8af's manual trace: a
  ## call written inside `quote do:` lowers to `getAst`/tree-construction
  ## code (probed, `probe_quotedo_reach.nim` -- the quoted call never
  ## shows up as a live `nnkCall` to the target at all, only the DIRECT,
  ## unquoted shape does), so this walk needs no special-casing for
  ## `quote do:` blocks: it naturally sees only genuine compile-time-VM
  ## execution. `specs` is a parameter (not hardwired to
  ## `genericRoutineSpecs`) so a TEST can point the exact same mechanism
  ## at its own small fixture list, independent of the real 37-routine
  ## registry -- see `tests/tsymex_rfc0005_s8ab_letaudit.nim`'s own
  ## reachability fixtures.
  var visitedProcs: seq[string]
  vmGuardWalkForGenericCallsAux(n, macroTag, specs, visitedProcs, hits)

# ---- name discovery (RFC-0005 S8ak: parsed from the module AST) -------------

const routineDefKinds* = {nnkProcDef, nnkFuncDef, nnkMacroDef, nnkTemplateDef,
                           nnkIteratorDef, nnkConverterDef}

proc routineDefName*(nameNode: NimNode): string =
  ## RFC-0005 S8ak. A top-level routine definition's own name node, as
  ## `parseStmt` returns it (untyped -- no `getImpl`/symbol involved yet),
  ## is either a bare `nnkIdent`, that wrapped in `nnkPostfix` (the `*`
  ## export marker), a backtick-quoted `nnkAccQuoted`, or `nnkPostfix`
  ## wrapping THAT. Unwraps the export marker, then joins `nnkAccQuoted`'s
  ## parts (an operator name is one part in practice, but joining handles
  ## any backtick-quoted sequence uniformly rather than assuming exactly
  ## one). Probed (`s8ak_probe_scratch.nim`, not shipped): confirms this
  ## shape for both an ordinary and a backtick-quoted exported name.
  var nn = nameNode
  if nn.kind == nnkPostfix and nn.len == 2: nn = nn[1]
  case nn.kind
  of nnkIdent, nnkSym: nn.strVal
  of nnkAccQuoted:
    var s = ""
    for part in nn:
      s.add(if part.kind in {nnkIdent, nnkSym}: part.strVal else: part.repr)
    s
  else: ""

proc extractTopLevelNames*(path: string): seq[string] =
  ## RFC-0005 S8ak: every top-level `proc`/`func`/`macro`/`template`/
  ## `iterator`/`converter` name in `path`, in source order, deduplicated
  ## -- enumerated by PARSING the module's source (`parseStmt`, a genuine
  ## recursive-descent parse) and reading each top-level definition node's
  ## own name, in place of the old column-0 line-TEXT scan. A real parser
  ## has no line boundaries to be confused by: a backtick-quoted name and a
  ## routine whose keyword and name sit on different physical lines (both
  ## invisible to a line-based `line.startsWith("proc ")`-style check, the
  ## latter because the keyword's OWN line never contains the name at all)
  ## are handled the exact same way as an ordinary single-line signature --
  ## see `tests/s8ak_scan_fixture.nim` for both fixtured shapes. Walks only
  ## DIRECT children of the module's top statement list, same "top-level
  ## only" scope the old scan had (see the test file's header for the
  ## nested-def caveat -- a routine nested inside another body is audited
  ## anyway, via the outer routine's own `impl` tree walk).
  let tree = parseStmt(staticRead(path))
  var seen: seq[string]
  for n in tree:
    if n.kind notin routineDefKinds: continue
    let nm = routineDefName(n[0])
    if nm.len > 0 and nm notin seen:
      seen.add nm
      result.add nm

proc extractTopLevelMacroNames*(path: string): seq[string] =
  ## Same scan as `extractTopLevelNames`, restricted to `nnkMacroDef` --
  ## used to build the "which of the scope's own macro names exist in this
  ## file" list a reachability audit needs (a name that is ALSO a
  ## proc/template elsewhere is still walked correctly by
  ## `vmGuardAuditMacroReach`'s own `s.symKind != nskMacro: continue` filter
  ## on each symChoice candidate; this is just a smaller candidate list,
  ## not a correctness requirement).
  let tree = parseStmt(staticRead(path))
  for n in tree:
    if n.kind != nnkMacroDef: continue
    let nm = routineDefName(n[0])
    if nm.len > 0 and nm notin result: result.add nm

# ---- compile-time accumulators (shared across every importer) --------------

var vmGuardLetHits* {.compileTime.}: seq[string]
var vmGuardParamHits* {.compileTime.}: seq[string]
var vmGuardReachHits* {.compileTime.}: seq[string]
var vmGuardWalkErrs* {.compileTime.}: seq[string]
var vmGuardForcedGenerics* {.compileTime.}: seq[string]
  ## RFC-0005 S8ah. Every `file:name@line` key `vmGuardAuditInstantiation`
  ## has forced an instantiation for, ANYWHERE in this compile -- GLOBAL,
  ## like the hit lists above, so a completeness check in one module (e.g.
  ## `symex.nim`'s own self-audit) can see a forcing call made from
  ## another (e.g. `vm_alias_guard.nim`'s own 14-file self-audit, which
  ## already forces `traceOneCallBoundary` once) without needing to repeat
  ## it -- a repeat would need `{.all.}}` visibility into the generic's
  ## OWN module, which most callers (symex.nim included) do not have and
  ## should not need.

# ---- the audit entry points (typed macros -- force resolution) -------------

proc vmGuardAuditOneSym*(s: NimNode; fileTag: string) =
  ## RFC-0005 S8ak: the per-symbol audit body -- extracted from what was
  ## S8ah's `vmGuardAuditRoutine` so `vmGuardAuditNames` (below, the only
  ## caller now; see its own doc for why the OLD `vmGuardAuditRoutine`
  ## `typed`-argument entry point was retired, not just refactored) can
  ## call it directly once IT has resolved a symbol by a DIFFERENT route
  ## (`bindSym`, never a `typed` argument). Audits `s` for both the
  ## let-aliasing hazard shapes and the param-aliasing shape, AND (S8ah)
  ## for direct, unquoted calls into one of the 37 generics if `s` is
  ## itself a macro.
  if s.symKind notin routineSymKinds: return
  var impl: NimNode
  try:
    impl = s.getImpl()
  except CatchableError as e:
    vmGuardWalkErrs.add fileTag & ": " & macros.strVal(s) & " getImpl raised: " & e.msg
    return
  if impl.isNil or impl.kind == nnkNilLit: return
  if not impl.lineInfoObj.filename.endsWith(fileTag): return
  let owner = fileTag & ":" & macros.strVal(s)
  walkLets(impl, owner, vmGuardLetHits)
  walkParams(impl, owner, vmGuardParamHits)
  if s.symKind == nskMacro:
    vmGuardWalkForGenericCalls(impl, owner, genericRoutineSpecs, vmGuardReachHits)

macro vmGuardAuditNames*(names: static seq[string]; fileTag: static string): untyped =
  ## RFC-0005 S8ak. For each name, generates a FRESH, uniquely-scoped (its
  ## own `block:`) NESTED MACRO DEFINITION whose own `bindSym(nm,
  ## brForceOpen)` call -- the only way to obtain a macro's resolved symbol
  ## without invoking it -- resolves that one name, and immediately invokes
  ## it. This replaces the OLD approach (`newCall(bindSym"vmGuardAuditRoutine",
  ## ident(nm), newLit(fileTag))`, wrapped in a `when true:` to keep each
  ## instantiation distinct): generating `vmGuardAuditRoutine(ident(nm),
  ## fileTag)` and letting the compiler re-semcheck `ident(nm)` as a fresh
  ## `typed` ARGUMENT EXPRESSION is exactly where S8ah's own remainder bug
  ## lived -- Nim auto-invokes a zero-required-argument macro referenced
  ## bare in an expression context expecting a value (macros have no
  ## first-class "value" form the way an ordinary proc does, so a bare
  ## reference has no other valid reading), so `vmGuardAuditRoutine` would
  ## receive the macro's OWN RESULT (e.g. an `nnkIntLit`), never its
  ## symbol, and silently find nothing.
  ##
  ## `bindSym` itself avoids that (pure NAME RESOLUTION, never an
  ## expression evaluation) -- but it resolves against the scope of
  ## WHEREVER THE BINDSYM CALL ITSELF IS LEXICALLY WRITTEN, not the calling
  ## macro's own call site (probed empirically, `s8ak_probe_{a,b,c}.nim`,
  ## not shipped: a `bindSym` call written directly in THIS macro's own
  ## body -- the first version of this fix -- fails to find a PRIVATE
  ## symbol that is only visible via the CALLER's own `{.all.}}` import,
  ## e.g. `symex.nim`'s private, generic `sortedKeysOf`, audited from the
  ## TEST FILE's call site: "undeclared identifier"). Generating a NESTED
  ## macro definition via `quote do:` and splicing it into the CALL SITE
  ## fixes this: when the compiler processes that spliced code, it compiles
  ## as part of the CALLING module (the test file / `symex.nim` /
  ## `concolic.nim`'s own trailing self-audit block), so the nested macro's
  ## OWN `bindSym` call resolves using THAT module's scope, `{.all.}}`
  ## imports included -- same probe, same name, resolves correctly once
  ## wrapped this way, and a genuinely zero-arg macro target's `.getImpl()`
  ## comes back as its real, never-invoked body too.
  ##
  ## `vmGuardAuditOneSym` is itself resolved ONCE here, OUTSIDE the
  ## per-name loop, via a plain `bindSym` call -- a SAME-MODULE lookup
  ## (this macro and that proc are siblings in `vm_alias_guard.nim`),
  ## unaffected by the cross-module issue above -- and spliced in as an
  ## ALREADY-RESOLVED symbol, so the generated call-site code never needs
  ## to re-resolve it by (bare) name itself.
  ##
  ## `{.experimental: "dynamicBindSym".}}` (declared at this module's top)
  ## is required because `names`/`nm` is a runtime-computed string, not a
  ## literal identifier/string token known when this macro was written --
  ## ordinary `bindSym` requires the latter.
  let auditOneSymSym = bindSym("vmGuardAuditOneSym")
  let fileTagLit = newLit(fileTag)
  result = newStmtList()
  for nm in names:
    let nmLit = newLit(nm)
    result.add quote do:
      block:
        macro vmGuardAuditNameLocal(): untyped =
          let resolved = bindSym(`nmLit`, brForceOpen)
          case resolved.kind
          of nnkClosedSymChoice, nnkOpenSymChoice:
            for s in resolved: `auditOneSymSym`(s, `fileTagLit`)
          of nnkSym:
            `auditOneSymSym`(resolved, `fileTagLit`)
          else: discard
        vmGuardAuditNameLocal()

proc vmGuardAuditOneSymReachOnly*(s: NimNode; fileTag: string;
                                   specs: seq[GenericRoutineSpec]) =
  ## RFC-0005 S8ah/S8al: the per-symbol body `vmGuardAuditMacroReachWithSpecs`
  ## (below) splices a call to, once it has resolved `s` by NAME via the
  ## SAME `bindSym`-based nested-macro technique `vmGuardAuditNames` uses
  ## (see that macro's own doc) -- extracted to a proc, same shape as
  ## `vmGuardAuditOneSym`, so the generated code's `quote do:` body stays a
  ## one-line call rather than repeating this logic inline.
  if s.symKind != nskMacro: return
  var impl: NimNode
  try: impl = s.getImpl()
  except CatchableError as e:
    vmGuardWalkErrs.add fileTag & ": " & macros.strVal(s) & " (reach-only) getImpl raised: " & e.msg
    return
  if impl.isNil or impl.kind == nnkNilLit: return
  if not impl.lineInfoObj.filename.endsWith(fileTag): return
  let owner = fileTag & ":" & macros.strVal(s)
  vmGuardWalkForGenericCalls(impl, owner, specs, vmGuardReachHits)

macro vmGuardAuditMacroReachWithSpecs*(name: static string; fileTag: static string;
                                        specs: static seq[GenericRoutineSpec]): untyped =
  ## RFC-0005 S8ah test hook: runs ONLY the reachability half of
  ## `vmGuardAuditOneSym`, against a CALLER-SUPPLIED `specs` list rather
  ## than the real `genericRoutineSpecs` registry. This is what lets
  ## `tests/tsymex_rfc0005_s8ab_letaudit.nim` prove the reachability
  ## MECHANISM itself (a direct call is flagged, a `quote do:`-only call
  ## is not) against its own small fixture generic, independent of
  ## whether that fixture happens to also be one of the real 37.
  ##
  ## RFC-0005 S8al: `name` is now a `static string` (the macro's OWN name),
  ## resolved to its symbol via `bindSym(name, brForceOpen)` inside a
  ## NESTED macro spliced into the caller's own code -- exactly
  ## `vmGuardAuditNames`'s own technique (see that macro's doc for the full
  ## probed rationale: `bindSym` is pure name resolution, never an
  ## expression evaluation, so a genuinely zero-required-argument macro is
  ## never auto-invoked the way a bare `typed`-argument reference to one
  ## would be). The OLD signature (`macroSym: typed`) took the macro
  ## SYMBOL directly as a typed argument -- which is exactly where the
  ## auto-invoke trap lived: passing a zero-arg macro bare in that position
  ## has Nim invoke it and hand this macro the RESULT (an `nnkIntLit` or
  ## similar), never the symbol, so its body was silently never walked.
  ## This forced `s8ahFxDirectGenericCall`/`s8ahFxQuotedGenericCall` to
  ## carry a dummy required parameter purely to dodge the auto-invoke --
  ## no longer needed now that this hook resolves by symbol the same way
  ## the real `vmGuardAuditNames` path already does.
  let auditSym = bindSym("vmGuardAuditOneSymReachOnly")
  let fileTagLit = newLit(fileTag)
  let specsLit = newLit(specs)
  let nameLit = newLit(name)
  result = quote do:
    block:
      macro vmGuardAuditMacroReachLocal(): untyped =
        let resolved = bindSym(`nameLit`, brForceOpen)
        case resolved.kind
        of nnkClosedSymChoice, nnkOpenSymChoice:
          for s in resolved: `auditSym`(s, `fileTagLit`, `specsLit`)
        of nnkSym:
          `auditSym`(resolved, `fileTagLit`, `specsLit`)
        else: discard
      vmGuardAuditMacroReachLocal()

macro vmGuardAuditInstantiation*(callExpr: typed; fileTag: static string): untyped =
  ## RFC-0005 S8af's forced-instantiation mechanism, moved verbatim.
  ## `callExpr` is an actual CALL EXPRESSION (never a bare name), which
  ## forces the compiler to produce the fully-substituted INSTANTIATED
  ## symbol as the call's own callee -- `getImpl()` on THAT returns the
  ## typed body with every generic parameter resolved to the concrete type
  ## the call used, so the ordinary `walkLets`/`walkParams` see real
  ## `nnkSym` bindings instead of an un-instantiated generic's `nnkIdent`
  ## tree.
  result = newEmptyNode()
  if callExpr.kind notin {nnkCall, nnkCommand} or callExpr.len == 0: return
  let callee = callExpr[0]
  if callee.kind != nnkSym or callee.symKind notin routineSymKinds: return
  var impl: NimNode
  try:
    impl = callee.getImpl()
  except CatchableError as e:
    vmGuardWalkErrs.add fileTag & ": " & macros.strVal(callee) &
      " (forced instantiation) getImpl raised: " & e.msg
    return
  if impl.isNil or impl.kind == nnkNilLit: return
  let owner = fileTag & ":" & macros.strVal(callee) & "[instantiated]"
  walkLets(impl, owner, vmGuardLetHits)
  walkParams(impl, owner, vmGuardParamHits)
  let forcedKey = extractFilename(impl.lineInfoObj.filename) & ":" &
    macros.strVal(callee) & "@" & $impl.lineInfoObj.line
  if forcedKey notin vmGuardForcedGenerics: vmGuardForcedGenerics.add forcedKey

# =============================================================================
# RFC-0005 S8ah: this module's OWN self-contained audit of the 14 sibling
# files that do NOT import `nelli/symex` -- `dsl_parser.nim`,
# `dsl_typebridge.nim`, `scoped_names.nim`, `exn_hierarchy.nim`,
# `stdlib_models.nim`, `types.nim`, `scan.nim` (the six smt/ front-end
# modules plus S8af's scan.nim addition) and `fuzzmacro.nim`, `derive.nim`,
# `dsl.nim`, `coverage.nim`, `mutation.nim`, `strategy.nim`, `parallel.nim`
# (the eight other macro-declaring top-level modules, minus `concolic.nim`).
#
# `concolic.nim` is EXCLUDED here on purpose: it is the one file in the
# 16-file scope that itself `import ./symex`s (RFC-z3-optional's documented
# seam -- "this module is the only place in the fuzz stack that imports
# `./symex`"). If this module imported `concolic.nim` with `{.all.}}` AND
# `symex.nim` imported THIS module (as its own trailing self-audit block
# does, conditionally), the import graph would cycle: this module ->
# concolic.nim -> symex.nim -> this module. `symex.nim` and `concolic.nim`
# each therefore run their OWN trailing self-audit instead (no `{.all.}}`
# import needed for a module to reflect on its OWN top-level routines) --
# see their own `when defined(nelliVmAliasAudit)` blocks. Together, this
# module's 14 files + symex.nim's 1 + concolic.nim's 1 = the full 16.
#
# This audit-with-hard-error block is what makes the guard an actual
# BUILD-TIME check (RFC-0005 S8ah item 4), not only a test: importing this
# module (which only ever happens behind `-d:nelliVmAliasAudit`, from
# `symex.nim`/`concolic.nim`'s own gated blocks, OR unconditionally from
# `tests/tsymex_rfc0005_s8ab_letaudit.nim`, whose whole job IS to run this)
# runs it. A `doAssert` failure here is a genuine compile error, in either
# case.
# =============================================================================

import ./dsl_parser {.all.}
import ./dsl_typebridge {.all.}
import ./scoped_names {.all.}
import ./exn_hierarchy {.all.}
import ./stdlib_models {.all.}
import ./types {.all.}
import ./scan {.all.}
import ../fuzzmacro {.all.}
import ../derive {.all.}
import ../dsl {.all.}
import ../coverage {.all.}
import ../mutation {.all.}
import ../strategy {.all.}
import ../parallel {.all.}

const selfScopeDir = currentSourcePath().parentDir()
const selfRootDir = selfScopeDir / ".."

template auditSelfScopeFile(dir, fname: string) =
  const path = dir / fname
  const names = extractTopLevelNames(path)
  vmGuardAuditNames(names, fname)

auditSelfScopeFile(selfScopeDir, "dsl_parser.nim")
auditSelfScopeFile(selfScopeDir, "dsl_typebridge.nim")
auditSelfScopeFile(selfScopeDir, "scoped_names.nim")
auditSelfScopeFile(selfScopeDir, "exn_hierarchy.nim")
auditSelfScopeFile(selfScopeDir, "stdlib_models.nim")
auditSelfScopeFile(selfScopeDir, "types.nim")
auditSelfScopeFile(selfScopeDir, "scan.nim")
auditSelfScopeFile(selfRootDir, "fuzzmacro.nim")
auditSelfScopeFile(selfRootDir, "derive.nim")
auditSelfScopeFile(selfRootDir, "dsl.nim")
auditSelfScopeFile(selfRootDir, "coverage.nim")
auditSelfScopeFile(selfRootDir, "mutation.nim")
auditSelfScopeFile(selfRootDir, "strategy.nim")
auditSelfScopeFile(selfRootDir, "parallel.nim")

# The one compile-time-VM-reachable generic this scope's own audit found
# (S8af's manual trace, now re-confirmed mechanically by the reachability
# walk above): `traceOneCallBoundary[seq[NimNode]]`, called un-quoted from
# `symexFindAllWitnesses`'s own macro body (`symex.nim:2826`). Forced here
# with minimal closures matching the real signature -- never called, only
# typed-checked (and thereby instantiated).
proc s8afSelfFxGetCalleeMarked(calleeImpl: NimNode): seq[NimNode] = @[]
proc s8afSelfFxIsMarked(marked: seq[NimNode], formalSym: NimNode): bool = false
proc s8afSelfFxOnMatch(argNode: NimNode) = discard

vmGuardAuditInstantiation(
  traceOneCallBoundary[seq[NimNode]](
    newEmptyNode(), s8afSelfFxGetCalleeMarked, s8afSelfFxIsMarked, s8afSelfFxOnMatch),
  "dsl_parser.nim")

const selfScopeLetHits = block:
  var dedup: seq[string]
  for h in vmGuardLetHits:
    if h notin dedup: dedup.add h
  dedup

const selfScopeParamHits = block:
  var dedup: seq[string]
  for h in vmGuardParamHits:
    if h notin dedup: dedup.add h
  dedup

const selfScopeReachHits = block:
  var dedup: seq[string]
  for h in vmGuardReachHits:
    if h.startsWith("dsl_parser.nim:") or h.startsWith("dsl_typebridge.nim:") or
       h.startsWith("scoped_names.nim:") or h.startsWith("exn_hierarchy.nim:") or
       h.startsWith("stdlib_models.nim:") or h.startsWith("types.nim:") or
       h.startsWith("scan.nim:") or h.startsWith("fuzzmacro.nim:") or
       h.startsWith("derive.nim:") or h.startsWith("dsl.nim:") or
       h.startsWith("coverage.nim:") or h.startsWith("mutation.nim:") or
       h.startsWith("strategy.nim:") or h.startsWith("parallel.nim:"):
      if h notin dedup: dedup.add h
  dedup

# Every `let` hit this 14-file scope produces today: `types.nim`'s `IRType`
# `==`, reading a `VariantAxis`/`VariantArm` element with nothing written
# while the binding is live (S8x's own hand audit, S8ab/S8af's allowlist --
# the other two historical allowlist entries are `symex.nim`'s own, audited
# by `symex.nim`'s OWN trailing block instead). Every VM-reachable generic
# found by the mechanical walk must have a corresponding forced-
# instantiation entry below, or this fails closed.
const selfScopeLetAllowlist = [
  "types.nim:==: let bx : VariantAxis (ntyObject) <- b.mvAxes[i]",
  "types.nim:==: let barm : VariantArm (ntyObject) <- bx.arms[k]",
]

static:
  doAssert vmGuardWalkErrs.len == 0,
    "vm_alias_guard: getImpl/audit-machinery error in the 14-file self " &
    "scope:\n" & vmGuardWalkErrs.join("\n")
  var unexpectedLets: seq[string]
  for h in selfScopeLetHits:
    if h notin selfScopeLetAllowlist: unexpectedLets.add h
  doAssert unexpectedLets.len == 0,
    "vm_alias_guard: unallowlisted compile-time VM let-aliasing hazard in " &
    "the 14-file self scope (RFC-0005 S8ab/S8x) -- either fix it or add a " &
    "reviewed allowlist entry with a justification:\n" & unexpectedLets.join("\n")
  doAssert selfScopeParamHits.len == 0,
    "vm_alias_guard: unallowlisted compile-time VM param-aliasing hazard " &
    "in the 14-file self scope:\n" & selfScopeParamHits.join("\n")
  var reachableGenerics: seq[string]
  for h in selfScopeReachHits:
    let genericKey = h.split(" -> ")[^1]
    if genericKey notin reachableGenerics: reachableGenerics.add genericKey
  var unforced: seq[string]
  for g in reachableGenerics:
    if g notin vmGuardForcedGenerics: unforced.add g
  doAssert unforced.len == 0,
    "vm_alias_guard: a macro in the 14-file self scope directly (unquoted) " &
    "calls a generic with no forced-instantiation audit -- add a " &
    "vmGuardAuditInstantiation call for it (RFC-0005 S8ah item 1/3):\n" &
    unforced.join("\n")
