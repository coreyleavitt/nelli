# runtime_closures.nim — Cluster C include fragment of runtime.nim
#
# THIS FILE IS NOT A STANDALONE MODULE. It is textually included into
# runtime.nim via `include "runtime_closures.nim"` and CANNOT be compiled
# independently. It inherits ALL imports, types, threadvars, helpers, and
# forward-declared procs from runtime.nim's lexical scope; do NOT add
# `import` statements here.
#
# Contents: `lowerClosureArm(env, e)` — the `lower()` dispatch arm for
# `iekLambda` and `iekClosureCall` (Cluster C, Stage 7 / Stage 8, CR-7).
# Both arms are single-line dispatches to `buildClosure` / `lowerClosureCall`
# (both forward-declared in runtime.nim above this include point).
# Placement in runtime.nim: immediately after `include "runtime_exceptions.nim"`
# and immediately before `lower`'s body, between `lower`'s forward-decl
# and body.

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
