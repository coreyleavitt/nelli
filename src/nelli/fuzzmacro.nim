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
## all) or that TRANSITIVELY calls a known-impure stdlib proc: a denylisted
## call reached through a named helper proc's own body (`getImpl`, bounded
## by depth + a visited set — see `checkCallee`/`maxImpurityTraversalDepth`
## below) is caught, not just a denylisted call written directly at the
## capture's top level (reconstructs to a possibly different value each
## time a worker re-runs it; best-effort/name-based denylist, not sound).
## The genuinely-accepted residual (R8 finding, RFC's own "checked through
## called procs" paragraph) is narrower than "impurity behind any function
## call": impurity reached only through a runtime CLOSURE VALUE or proc
## POINTER — never a named proc symbol this walk can resolve via `getImpl`
## — still slips through, along with any impure proc outside the denylist
## itself.
##
## C4 is the behavior-preserving front: `fuzz(<strategyExpr>, <propExpr>,
## <settings?>)` expands to the exact wiring `tfuzzloop.nim`/
## `tfuzzcovcorpus.nim` already write by hand — a fresh `CoverageFrontier`
## plus `fuzz(s, inProcessTarget(prop), frontier, settings)` — so it is a
## drop-in, no-behavior-change entry point. C5 adds the worker-mode registry.

import std/[macros, tables, sets]
import ./fuzz, ./fuzzworker
# RFC-z3-optional: this module imports NO symex, and therefore no z3.
#
# v0.6.0's G3 C4 wired a real, Z3-backed concolic bridge here for every
# caller. That convenience — a bridge nobody asked for — is the whole
# reason `import nelli` reached Z3, breaking a contract `README.md:91-95`
# still documents and `tests/tsmoke.nim` still asserts.
#
# The bridge now lives in `nelli/concolic`, built on demand by
# `concolicAssist` and handed to `fuzz` through the 4-arg overload at the
# bottom of this file. That overload takes the assist as `untyped` and
# never resolves it here, so nothing on this side needs the walker's
# symbols in scope; they resolve in the CALLER's module, where
# `nelli/concolic`'s own `export symex` puts them.
#
# **Never add `import ./concolic` here.** `concolic` imports this module
# for the shared capture helpers (`propFormalParams`/`countFormalParams`/
# `liftPropIfNeeded`), so the reverse edge is an immediate circular import
# — confirmed empirically in this tree (RFC-z3-optional §S1a, round 3).

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

# --- process isolation (RFC-fuzzer-nextgen E-review, code-review headline fix) --
#
# The finding: `fuzzworker.nim`'s process-worker tier (`newProcessWorker`,
# Job Object limits, the bootstrap breaker, worker recycling, shm coverage)
# was fully built, fully tested, and CI-proven on real Windows -- but DARK.
# `fuzz*[T]` (fuzz.nim) never passed `newOrchestrator` a `spawnFreshWorker`,
# so `newInProcessWorker` was the only `Worker` any public entry point ever
# built; `newProcessWorker`/`newForkWorker` had zero callers in `src/`.
#
# The fix needs worker RECONSTRUCTION (E1's whole premise, module doc
# above): only `fuzz(...)` has a walkable, re-runnable construction
# expression for the property, so only IT can supply a real process-spawn
# closure. `processIsolationSpawnWorker` builds that closure -- called
# identically from BOTH of `fuzzMacroImpl`'s emission branches below (the
# `paramCount == 1` branch and its multi-param sibling), so the
# construction lives in exactly ONE place rather than duplicated a third
# time alongside the concolic-bridge block those two branches already
# repeat (see the NOTE ahead of that block for why a shared *quote do*
# fragment can't be spliced across branches instead).

proc processIsolationSpawnWorker*[T](id: string; propWitness: proc(x: T)): proc(): Worker[T] {.closure.} =
  ## Builds the `FuzzSettings.executor.processIsolation` spawn closure over the SAME
  ## call-site id `nelliRegisterWorkerEntry` above already registers for
  ## worker-mode re-entry -- a freshly spawned `newProcessWorker[T](id)` is
  ## exactly what makes a submit to the returned closure's `Worker`
  ## re-exec this binary into `runWorkerLoopAndExit`/`runWorkerReentry`
  ## (the `when defined(posix) or defined(windows)` block just below the
  ## macro's registration statement) instead of running in-process.
  ##
  ## `propWitness` (the property proc VALUE, never called here) exists
  ## purely so Nim infers `T` from a value already in scope at the call
  ## site — `newProcessWorker[T]` only mentions `T` in its return type, not
  ## its `(id: string)` parameter list, so it cannot be inferred from `id`
  ## alone; passing the already-typed `propSym` as a witness is cheaper and
  ## more robust than re-deriving `T` from the captured AST a second time.
  ##
  ## Real cross-process isolation only exists where `fuzzworker.nim`
  ## defines `newProcessWorker` at all — its own `when defined(posix)`/
  ## `when defined(windows)` blocks. On any other platform this returns
  ## `nil`, the SAME `when defined(posix) or defined(windows)` gate this
  ## module already uses for worker-mode dispatch (just below in the
  ## generated code) — `fuzz*[T]`'s own `processIsolation` check (fuzz.nim)
  ## then turns a `nil` spawn closure into `ProcessIsolationError` at run
  ## time on such a platform, rather than a compile error here.
  when defined(posix) or defined(windows):
    result = proc(): Worker[T] {.closure.} = newProcessWorker[T](id)
  else:
    result = nil

# --- compile-time capture checks (C6) ----------------------------------------

const impurityDenylist = ["getEnv", "paramStr", "readFile", "getTime", "now", "rand", "random"]
  ## RFC §Open items (impurity denylist): best-effort, name-based, not sound —
  ## an impure proc outside this list, or impurity reached only through a
  ## runtime closure VALUE / proc POINTER (never a named symbol `checkCallee`
  ## below can resolve via `getImpl`), slips through. Documented limitation,
  ## not a claim of soundness.

const impureCallableSymKinds = {nskProc, nskFunc, nskMethod, nskConverter}
  ## Symbol kinds `checkCapture` follows into their own implementation
  ## looking for a TRANSITIVELY reached denylisted call (R8: "checked
  ## through called procs, not just the top-level call" — RFC). Excludes
  ## `nskIterator`/`nskTemplate`/`nskMacro`: a template/macro invocation is
  ## already inlined into this `typed` captured tree by sem-check before the
  ## macro ever sees it (there is no `nnkSym` of that kind left to walk to),
  ## and an iterator cannot occur as an ordinary call target inside a
  ## value-producing expression the way a strategy/property initializer is
  ## (it needs a `for`-loop binding) — it can never appear as the callee
  ## position this walk inspects, so there is nothing to exclude a false
  ## negative on.

const maxImpurityTraversalDepth = 5
  ## Bounds how many named-proc hops `checkCallee` follows below the
  ## captured expression's own top level. The motivating case (R8) is a
  ## named helper wrapping one denylisted call directly (`seedFromEnv()`
  ## wrapping `getEnv`) — 1 hop; a helper calling a helper is 2. 5 gives
  ## headroom for a few genuine layers of indirection (a strategy-building
  ## helper that calls a config-resolution helper that calls a seed helper,
  ## etc.) while bounding the real cost this walk adds: EVERY `fuzz(...)`
  ## expansion now pays it at compile time, and the captured tree routinely
  ## includes calls into this library's own strategy combinators
  ## (`integers`, `map`, `filter`, …) whose bodies are themselves reachable
  ## — without a depth cap, a single call site's compile time would depend
  ## on how deep that graph happens to run rather than on anything the
  ## macro's author controls. Paired with `visited` (below), the walk is
  ## also finite on a cyclic call graph well before this bound matters.

proc procIdentityKey(implNode: NimNode): string =
  ## `implNode` is the result of `sym.getImpl` for some SPECIFIC proc
  ## symbol; its own definition-site location uniquely identifies that one
  ## proc body regardless of how many different `nnkSym` nodes (recursive
  ## calls, mutually-recursive helpers, multiple unrelated call sites within
  ## the same capture) reference it — used as the `visited` key so a
  ## recursive or mutually-recursive helper cannot loop the traversal.
  let li = implNode.lineInfoObj
  li.filename & ":" & $li.line & ":" & $li.column

proc checkCallee(sym: NimNode; label: string; visited: var HashSet[string]; depth: int)

proc checkCalleeBody(n: NimNode; label: string; visited: var HashSet[string]; depth: int) =
  ## Walk a resolved callee's OWN body looking for a denylisted call, and
  ## recurse one hop further through any further named-proc call it makes
  ## (bounded by `depth`/`visited`, see `checkCallee`). Unlike `checkCapture`
  ## below, this never runs the free-identifier (`nonReconstructibleSymKinds`)
  ## check: a callee's own params/locals are bound within itself and rebuilt
  ## fresh on every call, worker or not — only impurity propagates across a
  ## call boundary, not the "closes over an outer local" concern.
  if n.kind == nnkSym:
    if n.symKind in impureCallableSymKinds and n.strVal in impurityDenylist:
      error("fuzz: " & label & " initializer transitively calls '" & n.strVal &
            "' (through a named helper proc, not at the top level), which is " &
            "on the best-effort impurity denylist (getEnv/paramStr/readFile/" &
            "getTime/now/rand/random) — worker reconstruction re-runs this " &
            "call in a fresh process/instance, so an impure initializer can " &
            "reconstruct a drifted value", n)
    elif n.symKind in impureCallableSymKinds:
      checkCallee(n, label, visited, depth)
  for c in n: checkCalleeBody(c, label, visited, depth)

proc checkCallee(sym: NimNode; label: string; visited: var HashSet[string]; depth: int) =
  ## Resolve `sym` (a named proc/func/method/converter call reached from the
  ## capture, not itself denylisted) to its implementation and look inside
  ## for a denylisted call. Conservative on an unavailable body: `getImpl`
  ## returns `nnkEmpty` for a symbol with no accessible source — an
  ## `importc`/FFI proc, a compiler magic/builtin (`+`, `len`, and similar
  ## routinely appear in a captured arithmetic/comparison expression), or a
  ## proc from a precompiled/binary-only module — and there is then no AST
  ## left to inspect. This SILENTLY ALLOWS rather than flags: a false
  ## positive here would reject otherwise-valid, already-compiling user code
  ## (strictly worse than the false negative this check closes, per the
  ## RFC's own risk framing), and an opaque body is exactly the "impurity
  ## behind an indirect call" residual the RFC already documents as
  ## unsound — declining to guess keeps that a stated limitation rather than
  ## introducing a new failure mode (a spurious rejection).
  if depth > maxImpurityTraversalDepth: return
  let impl = sym.getImpl
  if impl.kind == nnkEmpty or impl.kind notin RoutineNodes: return
  let key = procIdentityKey(impl)
  if key in visited: return
  visited.incl key
  let b = impl.body
  if b.kind == nnkEmpty: return
  checkCalleeBody(b, label, visited, depth + 1)

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

proc checkCapture(n: NimNode; bound: seq[string]; label: string; visited: var HashSet[string]) =
  if n.kind == nnkSym:
    if n.symKind in nonReconstructibleSymKinds and n.strVal notin bound:
      error("fuzz: " & label & " captures non-reconstructible identifier '" &
            n.strVal & "' from an enclosing scope; worker re-entry needs a " &
            "module-scope-reconstructible expression — hoist '" & n.strVal &
            "' to a const, or restructure the " & label &
            " to a module-scope constructor call", n)
    if n.symKind in impureCallableSymKinds:
      if n.strVal in impurityDenylist:
        error("fuzz: " & label & " initializer calls '" & n.strVal &
              "', which is on the best-effort impurity denylist (" &
              "getEnv/paramStr/readFile/getTime/now/rand/random) — worker " &
              "reconstruction re-runs this call in a fresh process/instance, " &
              "so an impure initializer can reconstruct a drifted value", n)
      else:
        # R8: the direct top-level check above only catches a denylisted
        # name written straight into the capture. Follow this (non-
        # denylisted) named proc into its own body too, so impurity hiding
        # one or more named-proc hops away (`seedFromEnv()` wrapping
        # `getEnv`) is caught the same way — bounded by
        # `maxImpurityTraversalDepth` and `visited` (see `checkCallee`).
        checkCallee(n, label, visited, 1)
  for c in n: checkCapture(c, bound, label, visited)

proc validateCapture(n: NimNode; label: string) =
  ## RFC-fuzzer-nextgen E1 (C6, R8): reject at COMPILE time a capture that is
  ## not safely re-runnable from scratch — (a) a free reference to a runtime
  ## local/param/mutable-global (`nonReconstructibleSymKinds`), (b) a call
  ## that TRANSITIVELY reaches a best-effort-denylisted impure stdlib proc,
  ## whether written directly in the capture or reached through one or more
  ## named-proc hops (`checkCallee`). Both name the offending identifier in
  ## the error.
  var bound: seq[string] = @[]
  collectBoundNames(n, bound)
  var visited: HashSet[string] = initHashSet[string]()
  checkCapture(n, bound, label, visited)

# --- the macro (C4/C5) --------------------------------------------------------

proc fuzzCallSiteId(n: NimNode): string =
  let li = n.lineInfoObj
  li.filename & ":" & $li.line & ":" & $li.column

proc countFormalParams*(formalParams: NimNode): int =
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

proc propFormalParams*(propExpr: NimNode): NimNode =
  ## The property expression's `nnkFormalParams` node — works whether
  ## `propExpr` is an already-named proc symbol (`nnkSym`, via `getImpl`) or
  ## an inline lambda literal (`nnkLambda`, same child layout as
  ## `nnkProcDef` — see `liftPropIfNeeded`). Read BEFORE lifting: a freshly
  ## `genSym`'d lifted name has no resolvable `getImpl` within this same
  ## macro expansion.
  if propExpr.kind == nnkSym: propExpr.getImpl.params
  else: propExpr.params

proc liftPropIfNeeded*(propExpr: NimNode): tuple[def: NimNode, sym: NimNode] =
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

proc fuzzMacroImpl(stratExpr, propExpr, settingsExpr: NimNode;
                   assistExpr: NimNode = nil): NimNode =
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

  # RFC-fuzzer-nextgen E2a / E4a (C2): worker-mode dispatch. `nelliWorkerModeId`
  # (workerproto.nim) is parsed from argv at module load, BEFORE this call
  # site's own code (including the registration statement just above) runs
  # — so by the time control reaches here, both "was this process launched
  # in worker mode" and "is THIS the call site it names" are already
  # decidable. A match means the ordinary `fuzz(...)` site "double-serves"
  # (RFC §Open items): instead of the front door, it enters the worker loop
  # over the pipes/handles the orchestrator's `spawnWorkerProcess` wired up
  # (POSIX: fixed fds 3/4; Windows: env-var-communicated pipe handles — see
  # fuzzworker.nim's module doc). `runWorkerLoopAndExit` is `{.noreturn.}`
  # (it always `quit`s), so the front-door block below is simply never
  # reached on that path — no if/else expression-type unification needed.
  # `when defined(posix) or defined(windows)` (resolved in the CALLER's
  # module against the CALLER's active defines) — no `fork` exists on
  # Windows, so `fuzzworker.nim`'s Windows `runWorkerLoopAndExit`/
  # `nelliWorkerModeId` reconstruct via the SAME captured-construction
  # closure this re-entry point always used (E1's `runWorkerReentry`,
  # already exec-based/platform-neutral); nothing about THIS check itself
  # was ever POSIX-specific (`nelliWorkerModeId`'s own doc comment already
  # notes `std/os`'s `paramCount`/`paramStr` are not POSIX-only) — only the
  # `runWorkerLoopAndExit` implementation it calls into needed a Windows
  # counterpart, added in E4a C2.
  stmts.add quote do:
    when defined(posix) or defined(windows):
      if nelliWorkerModeId == `idLit`:
        runWorkerLoopAndExit(`idLit`, proc (input: ChoiceSeq): Observation[void] {.closure.} =
          runWorkerReentry(`idLit`, input))

  # The behavior-preserving front (C4): identical wiring to what
  # `tfuzzloop`/`tfuzzcovcorpus` write by hand today — a fresh
  # `CoverageFrontier` plus `fuzz(s, inProcessTarget(prop), frontier,
  # settings)`. This is the macro's VALUE (last expression in the stmt
  # list).
  #
  # RFC-z3-optional: core builds NO concolic bridge. Until this slice, both
  # `paramCount` arms constructed a real, Z3-backed bridge for every caller
  # — which is what forced `import ./symex` here and, transitively, made
  # `import nelli` reach Z3. The bridge now comes from `nelli/concolic`'s
  # `concolicAssist`, through the 4-arg overload below, only when a caller
  # asks for it. With the bridge gone the two arms became identical, so
  # they are one — but note what the collapse still carries: the Track-E
  # `spawnFreshWorker = processIsolationSpawnWorker(...)` wiring, whose
  # coverage lives entirely outside the concolic suites. Dropping it here
  # would be silent.
  #
  # `paramCount` survives the collapse in `concolicAssist` (nelli/concolic),
  # which still dispatches on it to pick the binding classifier.
  #
  # `assistExpr` is `nil` for the 2-/3-argument entry points and the raw
  # assist syntax for the 4-argument one; the two shapes differ by exactly
  # that one argument, so they share this emission rather than maintaining
  # two copies that can drift.
  if assistExpr == nil:
    stmts.add quote do:
      block:
        var nelliFuzzFrontier = newCoverageFrontier()
        fuzz(`stratCopyForCall`, inProcessTarget(`propSym`), nelliFuzzFrontier, `settingsExpr`,
            spawnFreshWorker = processIsolationSpawnWorker(`idLit`, `propSym`))
  else:
    stmts.add quote do:
      block:
        var nelliFuzzFrontier = newCoverageFrontier()
        fuzz(`stratCopyForCall`, inProcessTarget(`propSym`), nelliFuzzFrontier, `settingsExpr`,
            assist = `assistExpr`,
            spawnFreshWorker = processIsolationSpawnWorker(`idLit`, `propSym`))

  result = stmts

macro fuzz*(stratExpr, propExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>)` — settings default to `FuzzSettings()`.
  ## See the module doc comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, newCall(ident"FuzzSettings"))

macro fuzz*(stratExpr, propExpr, settingsExpr: typed): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>, <settings>)`. See the module doc
  ## comment for the full contract.
  fuzzMacroImpl(stratExpr, propExpr, settingsExpr)

proc concolicAssistCalleeName(callee: NimNode): string =
  ## Extract the bare identifier a call's callee ultimately names, if any.
  ## Handles the plain form (`concolicAssist`), the sym-choice a partially
  ## resolved callee can land in, and a QUALIFIED spelling
  ## (`cc.concolicAssist`, `nelli/concolic.concolicAssist`) by recursing into
  ## the `nnkDotExpr`'s tail.
  ##
  ## **The qualifier is deliberately NOT consulted, and that is a trade-off,
  ## not a safety property.** In an untyped AST `cc` could be a module alias,
  ## a variable, or anything else, so there is no sound way to tell
  ## `nelli/concolic`'s `concolicAssist` from an unrelated `.concolicAssist`
  ## member on some other object. Matching on the trailing name therefore
  ## ACCEPTS that over-match: a same-named call written as `fuzz`'s `assist`
  ## argument would have its first two arguments overwritten. That is bounded
  ## and judged acceptable — `alignAssistWithCapture` only ever runs on the
  ## single expression a caller passes as `assist =`, where a
  ## non-`concolicAssist` call of that exact name is not a shape this API
  ## has any meaning for. Under-matching (a renamed import, a wrapping
  ## template) is the opposite residual, listed on
  ## `alignAssistWithCapture` below.
  case callee.kind
  of nnkIdent, nnkSym:
    result = callee.strVal
  of nnkOpenSymChoice, nnkClosedSymChoice:
    if callee.len > 0: result = callee[0].strVal
  of nnkDotExpr:
    if callee.len > 1: result = concolicAssistCalleeName(callee[1])
  else:
    discard

proc originMatches(a, b: NimNode): bool =
  ## True when `a` and `b` are known to come from the exact same source
  ## position — the signature of one written expression reused twice, which
  ## is exactly what `fuzzConcolic`'s template substitution does (`s`/`p`
  ## are spliced into both the outer typed capture and the nested
  ## `concolicAssist(s, p, ...)` call). A plain `repr` comparison is NOT
  ## reliable here: `stratExpr`/`propExpr` arrive already `typed`, and Nim
  ## typechecking materializes optional/default arguments into the resolved
  ## node — `integers(0, 100)` typechecks to `integers(0, 100, [])` — so
  ## even the sugar's own already-aligned call would repr as "changed"
  ## under naive comparison (measured: it does). Source position is not
  ## fooled by that: the same reused node keeps the same file/line/column,
  ## while a genuinely different expression — even one with coincidentally
  ## identical text — does not.
  let la = a.lineInfoObj
  let lb = b.lineInfoObj
  la.filename == lb.filename and la.line == lb.line and la.column == lb.column

proc alignAssistWithCapture(assist, stratExpr, propExpr: NimNode): NimNode =
  ## RFC-z3-optional §The coherence invariant. `fuzz(sA, pA, settings,
  ## assist = concolicAssist(sB, pB))` is expressible, and on mismatch the
  ## assist classifies bindings from one strategy chain while the campaign
  ## draws from another: the solver solves the wrong equation. Damage is
  ## bounded — a mismatched seed still replays cleanly (it is a valid draw
  ## for the campaign's OWN strategy), so it is not the re-verify gate that
  ## catches it; it is turned away one layer later, by `admit`'s
  ## interestingness fold, as `caoSupersededByRace` — but silent
  ## yield-poisoning is exactly the ambiguity Track G exists to kill.
  ##
  ## Because `assist` is declared `untyped`, this macro sees the RAW call
  ## syntax, before `concolicAssist` has expanded. So for the written-inline
  ## form the divergence is not merely diagnosable — it is REMOVED: the
  ## assist call's strategy/property arguments are overwritten with this
  ## macro's own already-typed copies, and the assist is built from the pair
  ## the campaign actually runs. The bare (`concolicAssist(...)`), named
  ## (`concolicAssist(strat = ..., prop = ...)`), and QUALIFIED
  ## (`cc.concolicAssist(...)`) spellings are all handled; a rewrite that
  ## silently skipped any of them would leave exactly the hole it exists to
  ## close. When the rewrite actually changes an argument, a `hint` marks the
  ## call site, so the substitution is never silent — but the common
  ## `fuzzConcolic` sugar (`nelli/concolic.nim`) expands to a call that is
  ## ALREADY aligned by construction, and stays hint-free: see
  ## `originMatches` below for how a no-op substitution is told apart from a
  ## real one.
  ##
  ## Two shapes remain a residual, and cannot be closed from an untyped AST:
  ##
  ## * a pre-built `ConcolicAssist` variable, or a proc call returning one —
  ##   there is no `concolicAssist(...)` call node to align at all;
  ## * a genuine RENAME of the import (`from nelli/concolic import
  ##   concolicAssist as ca`) or a user template that itself expands to
  ##   `concolicAssist(...)` — the callee's own name really is `ca` (or
  ##   whatever the template is called), not `concolicAssist`, and nothing
  ##   in the untyped AST says otherwise.
  ##
  ## Both residual shapes pass through untouched, by necessity. That residual
  ## is what `tfuzzconcolicmismatch.nim` pins as bounded.
  result = copyNimTree(assist)
  if result.kind notin nnkCallKinds or result.len < 3: return
  if concolicAssistCalleeName(result[0]) != "concolicAssist": return
  var changed = false
  var positional = 0
  for i in 1 ..< result.len:
    if result[i].kind == nnkExprEqExpr:
      let key = result[i][0]
      if key.kind in {nnkIdent, nnkSym}:
        if key.strVal == "strat":
          if not originMatches(result[i][1], stratExpr): changed = true
          result[i][1] = copyNimTree(stratExpr)
        elif key.strVal == "prop":
          if not originMatches(result[i][1], propExpr): changed = true
          result[i][1] = copyNimTree(propExpr)
    else:
      inc positional
      if positional == 1:
        if not originMatches(result[i], stratExpr): changed = true
        result[i] = copyNimTree(stratExpr)
      elif positional == 2:
        if not originMatches(result[i], propExpr): changed = true
        result[i] = copyNimTree(propExpr)
  if changed:
    hint("concolicAssist(...)'s strategy/property arguments were realigned " &
         "to the (strategy, property) pair being fuzzed", assist)

macro fuzz*(stratExpr, propExpr, settingsExpr: typed; assist: untyped): untyped =
  ## `fuzz(<strategyExpr>, <propExpr>, <settings>, assist = <assist>)` — the
  ## compositional primitive for concolic-assisted fuzzing.
  ##
  ##     import nelli
  ##     import nelli/concolic
  ##
  ##     fuzz(integers(0, 0xFFFFFFFF), magicGate, settings,
  ##          assist = concolicAssist(integers(0, 0xFFFFFFFF), magicGate))
  ##
  ## **`fuzzConcolic` (nelli/concolic) is the documented default form**; it
  ## names the strategy and property once and generates both occurrences,
  ## so the pair cannot diverge and the expression is not written twice.
  ## Reach for this primitive when you need to compose an assist separately
  ## — and read `alignAssistWithCapture` for exactly how much of the
  ## coherence invariant this overload can enforce for you.
  ##
  ## `assist` is deliberately `untyped`: it is what lets this macro align
  ## an inline assist with the captured pair, and (measured, not assumed) it
  ## does not disturb overload resolution — a 4-argument call to the
  ## concrete `proc fuzz*[T](s, target, frontier, settings)` still selects
  ## the proc. The parameter must be literally named `assist`; naming it
  ## anything else breaks the `assist = ...` call form.
  ##
  ## Note this macro never resolves the assist expression itself. It splices
  ## it into the caller's module, where `nelli/concolic`'s re-exports are in
  ## scope — which is why core needs no walker import to offer this door.
  # `validateCapture` (inside `fuzzMacroImpl`) covers the strategy and
  # property ONLY. Running it over the assist argument would reject it: by
  # the time it matters the assist is an expanded closure block, not a
  # re-runnable construction expression.
  fuzzMacroImpl(stratExpr, propExpr, settingsExpr,
                alignAssistWithCapture(assist, stratExpr, propExpr))
