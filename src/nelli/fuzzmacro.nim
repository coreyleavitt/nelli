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

import std/[macros, tables]
import ./fuzz, ./fuzzworker

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

# --- the macro (C4/C5) --------------------------------------------------------

proc fuzzCallSiteId(n: NimNode): string =
  let li = n.lineInfoObj
  li.filename & ":" & $li.line & ":" & $li.column

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

  # The behavior-preserving front (C4): identical wiring to what
  # `tfuzzloop`/`tfuzzcovcorpus` write by hand today — a fresh
  # `CoverageFrontier` plus `fuzz(s, inProcessTarget(prop), frontier,
  # settings)`. This is the macro's VALUE (last expression in the stmt list).
  stmts.add quote do:
    block:
      var nelliFuzzFrontier = newCoverageFrontier()
      fuzz(`stratCopyForCall`, inProcessTarget(`propSym`), nelliFuzzFrontier, `settingsExpr`)

  result = stmts

macro fuzz*(stratExpr, propExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>)` — settings default to `FuzzSettings()`.
  ## See the module doc comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, newCall(ident"FuzzSettings"))

macro fuzz*(stratExpr, propExpr, settingsExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>, <settings>)`. See the module doc
  ## comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, settingsExpr)
