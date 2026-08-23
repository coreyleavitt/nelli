# runtime_closures.nim — Cluster C include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_closures.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents (CR-7-deeper Stage 8+):
#   sortFingerprint, paramSorts, buildClosure — Cluster C construction
#   helpers (moved from runtime.nim; only used within this cluster).
#   `lowerClosureArm(env, e)` — the `lower()` dispatch arm for
#   `iekLambda` and `iekClosureCall` (Cluster C, Stage 7 / Stage 8, CR-7).
# Both arms are single-line dispatches to `buildClosure` / `lowerClosureCall`
# (buildClosure defined here; lowerClosureCall forward-declared in runtime.nim).
# Placement in runtime.nim: immediately after `include "runtime_exceptions.nim"`
# and immediately before `lower`'s body, between `lower`'s forward-decl
# and body.

proc sortFingerprint(sorts: openArray[RawZ3Sort]): string =
  ## A stable per-context fingerprint of a sort list (the `Z3_get_sort_id`s,
  ## joined). Used to key the closure funcSym memo so the SAME lambda site at
  ## two monomorphizations (distinct leaf/param sorts) gets distinct funcSyms
  ## (ADR-0009 D8). Sort ids are monotone+unique within a context.
  let ctx = requireCurrentContext()
  var parts: seq[string]
  for s in sorts: parts.add $sortId(ctx, s)
  parts.join(",")

proc paramSorts(params: seq[IRParam]): seq[RawZ3Sort] =
  ## The Z3 sorts of a lambda's parameters. A throwaway representative SymVal is
  ## allocated per param to read its sort (G4 `baseRep` pattern — the init
  ## constraints are discarded; the decl only needs the sort).
  let ctx = requireCurrentContext()
  for p in params:
    var scratchPC: seq[Z3Bool]
    let rep = allocateSym(p.ty, "__closureParamSort." & p.name, scratchPC)
    for s in sortOfTuple(rep): result.add s

proc buildClosure(env: Env, e: IRExpr): SymVal =
  ## Phase 15 C2a (ADR-0009 D1/D2/D4). Construct an `svClosure` from an
  ## `iekLambda`:
  ##   1. Snapshot the captured locals: look each `lambdaCaptures` name up in the
  ##      CURRENT env, collect the SymVals → an `svTuple` `envRecord` (the env
  ##      snapshot). NO body descent — the lambda body is NOT lowered here.
  ##   2. Get-or-create the per-site uninterpreted `funcSym`, memoized in the
  ##      `currentClosureSyms` threadvar keyed by `((siteHash, declOrder),
  ##      envSortId, paramsSortTupleId)`. Domain = flattened env leaf sorts ++
  ##      param sorts (the C1 PoC pattern, D2); range = `lambdaRetTy`'s sort.
  ##   3. Build `svClosure{closureSite, closureEnv, closureRawFD}`.
  ## (`lower` has no `WalkCtx`, so the memo lives on a threadvar — the G4
  ## `currentDistinctSorts` idiom.)
  let ctx = requireCurrentContext()
  # 1. Env snapshot: captured locals (in capture order) → svTuple.
  var capVals: seq[SymVal]
  var capNames: seq[string]
  for name in e.lambdaCaptures:
    if env.hasKey(name):
      capVals.add env[name]
      capNames.add name
    # A capture missing from the current env is dropped from the snapshot (it
    # was a body-local or a name the walker never bound symbolically); the
    # funcSym domain follows the snapshot, so this stays consistent.
  let envRecord = SymVal(kind: svTuple, fields: capVals, fieldNames: capNames)
  # Phase 15 C3: a no-capture lambda (a top-level proc-as-value, lambdaCaptures
  # == @[]) materializes a ZERO-field svTuple unitEnv — the snapshot must have
  # collected nothing. (Belt-and-braces: a capture present in lambdaCaptures but
  # absent from the env is dropped above, so the invariant is "empty captures ⇒
  # empty env", checked only on the no-capture path.)
  if e.lambdaCaptures.len == 0:
    doAssert envRecord.fields.len == 0,
      "buildClosure: no-capture lambda (unit-env, C3) must have a zero-field " &
      "env, got " & $envRecord.fields.len & " fields"
  # 2. Get-or-create the per-site funcSym.
  let envLeafSorts = sortOfTuple(envRecord)
  let pSorts = paramSorts(e.lambdaParams)
  let key: ClosureSymKey = (siteHash: e.lambdaSite.siteHash,
                            declOrder: e.lambdaSite.declOrder,
                            envSortId: sortFingerprint(envLeafSorts),
                            paramsSortTupleId: sortFingerprint(pSorts))
  var fd: RawZ3FuncDecl
  if currentClosureSyms.hasKey(key):
    fd = currentClosureSyms[key]
  else:
    # Domain = flattened env leaf sorts ++ param sorts (D2); range = retTy sort.
    var domain = envLeafSorts
    for s in pSorts: domain.add s
    var retPC: seq[Z3Bool]
    let retRep = allocateSym(e.lambdaRetTy, "__closureRet", retPC)
    let rangeSorts = sortOfTuple(retRep)
    let rangeSort =
      if rangeSorts.len == 1:
        rangeSorts[0]
      else:
        # N29-followup (Bucket-2 opening fix-slice, walker v120): a
        # closure/lambda whose return type flattens to MORE than one Z3
        # leaf (e.g. `proc(x: int): (string, string) = ...`) has no single
        # Z3 range sort `Z3_mk_func_decl` can express -- ADR-0009 D4 is
        # single-leaf-scalar-return only, by design (`applyClosureGround`'s
        # own `symValFromRawAst` wrap is likewise scalar-only). Pre-fix
        # this was a raw `doAssert`, unreachable in practice ONLY because
        # N29 (a wholly unrelated seq-literal sort bug -- see
        # `symexWalkerVersion`'s own doc comment) crashed every inline-HOF
        # closure application first; fixing N29 exposed this genuine,
        # orthogonal gap as a raw internal-fault crash (caught by the
        # outermost catch-all as `weInternalWalkerFault`) instead of an
        # honest classified decline. Degrade IN-BAND here (this proc runs
        # inside `lower()`, no `Path`/`WalkCtx` in scope -- the established
        # ADR-0023 idiom every other `lower()`-reachable construct-gap uses)
        # and fall back to a scalar Bool range sort so the func_decl/
        # application stay structurally valid; `loweringDidDegrade` already
        # forces the whole path to `sxUnknown`, so the range's actual
        # content is never trusted downstream (same doctrine `allocateSym`'s
        # own totality work established -- "the fallback's content need
        # not be trustworthy, only type-correct enough that a downstream
        # consumer does not crash").
        loweringDegradeErrors.add SymexErrorInfo(
          kind: feUnsupportedOp, severity: sevError,
          msg: "closure/lambda return type kind " & $e.lambdaRetTy.kind &
               " flattens to " & $rangeSorts.len &
               " Z3 leaves — only a single-leaf scalar closure return " &
               "type is modeled (feUnsupportedOp)")
        loweringDidDegrade = true
        mkBoolSort(ctx).raw
    let fname = "closure@" & $e.lambdaSite.siteHash & "/" &
                $e.lambdaSite.declOrder
    let fsym = ctx.checkErr Z3_mk_string_symbol(ctx.raw, fname.cstring)
    # `Z3_mk_func_decl` over the runtime-known sorts (G4 raw-FFI discipline:
    # domains are a HEAP seq; the decl is inc-ref'd for the run's lifetime). A
    # zero-arity domain (no captures, no params) passes a nil ptr.
    let domPtr = if domain.len > 0:
                   cast[ptr UncheckedArray[RawZ3Sort]](addr domain[0])
                 else: nil
    fd = ctx.checkErr Z3_mk_func_decl(ctx.raw, fsym, cuint(domain.len),
      domPtr, rangeSort)
    incRefFD(ctx, fd)
    currentClosureSyms[key] = fd
    # CR-9 Stage 4: also populate WalkerStatics when a walk is active so the
    # live WalkerStatics.closureSyms is the authoritative source, making the
    # post-walk mirror loop for closureSyms redundant.
    syncClosureSymEntry(key, fd)
  # 3. Stash the lambda body + signature so the CALL (C2b) can descend it —
  # `svClosure` carries the site key + env + funcSym, but NOT the body IR. The
  # site is the reach-back key (ADR-0009 D6: the body is descended at apply).
  let siteKey = (e.lambdaSite.siteHash, e.lambdaSite.declOrder)
  let cBody = ClosureBody(body: e.lambdaBody, params: e.lambdaParams,
                          captures: capNames, retTy: e.lambdaRetTy)
  currentClosureBodies[siteKey] = cBody
  # CR-9 Stage 4: also populate WalkerStatics when a walk is active so
  # applyClosureGround can read from statics via the nil-guard.
  syncClosureBodyEntry(siteKey, cBody)
  # 4. Assemble the svClosure.
  var boxedEnv = new(SymVal)
  boxedEnv[] = envRecord
  SymVal(kind: svClosure,
         closureSite: e.lambdaSite,
         closureEnv: boxedEnv,
         closureRawFD: fd)

proc lowerClosureArm(env: Env, e: IRExpr): SymVal =
  ## Stage 7 (CR-7) Cluster C extraction. Called from `lower`'s case arm for
  ## `iekLambda` and `iekClosureCall`. Both arms are already single-line
  ## dispatches to `buildClosure` / `lowerClosureCall` — extracting them here
  ## preserves the coupling pattern (the arm body IS the named-proc call).
  ## `proto` NOT used by either arm.
  ##
  ## Shared-symbol dependencies for Stage 8 include-ordering:
  ##   buildClosure, lowerClosureCall (forward-declared above).
  case e.kind
  of iekLambda:
    # Phase 15 C2a. Closure CONSTRUCTION: snapshot the captured locals from the
    # current env into an `svTuple` envRecord, get-or-create the per-site
    # uninterpreted funcSym (memoized in `currentClosureSyms`), and assemble the
    # `svClosure{closureSite, closureEnv, closureRawFD}`. NO body descent — the
    # lambda body is lowered only at APPLICATION (C2b, the ground per-call
    # axiom). Closure CALL (`iekClosureCall`) stays `ceNotImplemented` below.
    buildClosure(env, e)
  of iekClosureCall:
    # Phase 15 C2b. Closure APPLICATION. Resolve the callee variable to an
    # `svClosure`, descend the lambda body ONCE (reached via the site→body map),
    # collect its return sub-paths, and assert the GROUND per-call-site axiom
    # (ADR-0009 D6): one `implies(callerPC and pc_i, funcSym(env, args) == v_i)`
    # per sub-path, NEVER a `∀env,args` axiom (the G4 hang). The call RESULT is
    # the funcSym application the axioms constrain. The descent uses `walk` via
    # the `currentWalkCtxPtr` threadvar (`lower` has no `WalkCtx`); the body is
    # defined after `walk`, so this dispatches to the forward-declared
    # `lowerClosureCall`.
    lowerClosureCall(env, e)
  else:
    raise newException(ValueError,
      "lowerClosureArm: unexpected e.kind=" & $e.kind &
      " (not iekLambda/iekClosureCall)")
