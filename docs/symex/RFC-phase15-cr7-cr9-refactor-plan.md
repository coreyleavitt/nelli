# CR-9 + CR-7 Staged Refactor Plan (Phase 15 code-review follow-up)

Goal: (CR-9) replace the ~36 file-scoped threadvars + scattered seed/drain convention with an explicit context reached via the existing `currentWalkCtxPtr`, and add `lowerInExpr` wrappers so drain-omission is structurally impossible; then (CR-7) split `runtime.nim` (~7200 lines) into per-theory `include` files.

Hard rules: build/test ONLY via `scripts/dt-bounded.sh <c|cpp> <test> [secs]` and `scripts/parity-check.sh <test.nim>`; BOTH backends green after every commit; commits on `main`; one logical unit per commit; NO `symexWalkerVersion`/`renderAsChoicesVersion` bump on ANY stage (every stage is encapsulation/relocation → byte-identical Z3 terms; a verdict flip = a BUG to fix, not a bump). 137 exit = Z3 hang regression.

CR-9 MUST fully precede CR-7 (the threadvars are what make the file un-splittable; an explicit ctx enables the split). `include` (not `import`) for CR-7 because of the `lower → applyClosureGround → walk → lower` mutual recursion, already broken today via `currentWalkCtxPtr`.

## Stages
- **0 Baseline:** parity-check canaries: rereview_drains, CR1_CR5_closure_heap, CR3_CR4_CR6_float, S10b_strconv, r9_recursive (hang canary), z4_walkctx. Record green.
- **1 `lowerInExpr`/`lowerBoolInExpr` wrappers** (after `drainPendingLowerEffects` ~4770): encapsulate `parseIntRaiseConds=@[]; convFloatToIntBoundConds=@[]; seedCallerHeapThreadvars(p); lower(...); drainPendingLowerEffects(p)` → return `(SymVal, drainedPath)`. `drainParseIntRaises` is a FORK — NOT swallowed; arms call it on the returned path. Pure addition, migrate no sites. +1 test. No bump.
- **2 Migrate ~10 simple arms** (1/commit, drains canary each): isLet, isAssign, isWhile-cond, isReturn, isCall-args, isAssert, index arms, isVariantReassignSymbolic, isDerefWrite-value. isIf per-branch (re-seeds in loop, threads `cp`) LAST and SOLO with full canary.
- **3 `lowerLeafInExpr`** for the 4 field-container arms (doAssert kind in {iekVar,iekField}, no drain — operand side-effect-free): isIndex/ixArr, isVariantField/vfRecv, isDeref/dPtr, isDerefWrite/dwPtr.
- **4 Group-1 caches → WalkerStatics** (1/commit): currentRefSorts, currentNilConsts, currentDistinctSorts, currentClosureSyms, currentClosureBodies. DANGER: nil-`currentWalkCtxPtr` probe paths (C2a) — keep threadvar as fallback when ptr==nil, redirect to field only when a walk is active.
- **5 Group-3 error/hint sinks → WalkCtx** (1/commit): extractionErrors, unknownExnWarnings, currentClosureCallErrors, distinctBijectivityHints, freshnessCapHints, heapDepthErrors, ptrFamilyHints, convFloatToIntDomainHints, parseIntGateConstraints, currentClosureCallAxioms/Strs.
- **6 Group-2 transient sinks → WalkCtx** (HIGHEST risk = drain-bug family): convFloatToIntBoundConds, parseIntRaiseConds, currentCallerHeap*, currentClosureExit*. Post Stage1-2 all access is funneled through 3 helpers — convert one helper at a time (float-bound, parseInt, caller-heap, closure-exit) with F5hang_derefwrite + r9_recursive canaries between each. RE-REVIEW after.
- **7 Extract cluster arm-bodies into named procs** (1 cluster/commit, no file move): S (lowest coupling), F, E, C, R. `of iekStr...: lowerStrArm(env,e)`.
- **8 Move named procs into `runtime_*.nim` includes** (1 cluster/commit): runtime_strings/floats/exceptions/closures/heap. Include order: core+helpers → `lower` fwd-decl → `walk` fwd-decl → cluster includes calling lower/walk → `lower` def → `walk` def → driver. heap+closure includes AFTER `walk` fwd-decl (reach walk only via currentWalkCtxPtr). Bad placement = compile error (safe). RE-REVIEW after.
- **9 (optional) `runtime_core.nim`** extraction if runtime.nim still large. Keep `include` unless core has zero back-edge into lower/walk (then real import).

Strictly sequential on `main` (all touch runtime.nim). Independent pairs: Stage 3 vs 2; Stage 4 vs 5. Danger stages get re-review: 6 and 8.
